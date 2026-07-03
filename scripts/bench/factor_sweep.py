#!/usr/bin/env python3
"""Cross-system factorization sweep orchestrator (issue #8545, deliverable 4).

Spawns each measured system as a warm persistent process speaking the suite line
protocol, sweeps the committed corpus at a fixed per-call cutoff, cross-checks
factor degree multisets across every system that answered, and writes one durable
JSON record per sweep (deliverable 5).

This is a comparator sweep, run manually on dedicated hardware (carica) -- NOT a
CI job and NOT a hex-internal benchmark harness, so the one-harness rule stays
intact (see SPEC/benchmarking.md addendum).

Systems (``--systems`` selects a comma-separated subset; default: all):

    hex-factor               hexbz_factor_service --entry factor
    hex-lattice              hexbz_factor_service --entry factorLattice
    hex-fast                 hexbz_factor_service --entry factorFast
    hex-classical-nodecline  hexbz_factor_service --entry factorClassicalNoDecline
    flint                    bz_flint_service.py
    pari                     bz_pari_service.py
    ntl                      bz_ntl_service (built on demand)
    isabelle-bz              bz_isabelle    (setup_bz_isabelle.sh)
    isabelle-lll             lll_isabelle   (setup_bz_lll_isabelle.sh; build-spike gated)

Per system: spawn warm, measure per-call protocol overhead on a trivial input,
then sweep. Median-of-5 when the first real call is under 1 s, single call
otherwise. On timeout the process is killed, the abandonment recorded, and the
process respawned. Statuses: ok | declined | timeout | error -- failures are
always recorded, never dropped.

Example::

    python3 scripts/bench/factor_sweep.py --cutoff 10 \\
        --systems hex-factor,hex-lattice,flint,ntl

Exit code is non-zero if any cross-system factor-degree-multiset mismatch is
found (a differential-correctness failure of hex against the other systems).
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import queue
import shutil
import socket
import subprocess
import sys
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CORPUS_PATH = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
ORACLE = ROOT / "scripts" / "oracle"
HEX_SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"

# A trivial input whose algorithmic work is sub-millisecond, for the per-call
# protocol-overhead measurement (SPEC/benchmarking.md external-comparator clause).
OVERHEAD_INPUT = {"coeffs": [-1, 1]}
OVERHEAD_REPEATS = 21

# Families whose difficulty rises (near-)monotonically with degree, so that once
# a system has timed out on a run of successively harder instances the rest of
# the family is hopeless too. When early termination is enabled (the default),
# a system that times out on `--early-terminate-run` consecutive instances of
# such a family (degree-ordered) skips the remaining higher-degree instances,
# recording them as timeouts without running them (`early_terminated: true`).
# Any solve resets the run counter.
#
# For a strictly monotonic family the run threshold triggers on the first few
# higher-degree instances, so termination is result-preserving up to at most
# `run - 1` extra timeouts, and the cactus/survival curves are unchanged.
#
# `conway` is included even though it is not strictly monotonic: a lifted Conway
# polynomial's difficulty is non-monotonic in degree because the reducer's prime
# choice varies (e.g. `factorFast` times out on C_{2,12} yet solves C_{2,16} in
# milliseconds). The consecutive-run threshold (default 3) is what makes this
# safe: an isolated prime-lucky solve resets the counter and survives, while the
# genuinely hopeless tail — a long unbroken run of timeouts — is still cut off.
# Pass `--no-early-terminate` for a full-fidelity measurement (as the committed
# baseline record was collected).
MONOTONIC_FAMILIES = frozenset({
    "swinnerton-dyer", "sd-products", "hoeij-zimmermann", "conway",
})

# Consecutive-timeout run length that trips early termination within a monotonic
# family. Chosen to ride over isolated non-monotonic solves (conway prime luck)
# while still cutting the hopeless tail.
DEFAULT_EARLY_TERMINATE_RUN = 3


@dataclass(frozen=True)
class SystemSpec:
    name: str
    # A callable returning the argv to spawn a warm service, or None if the
    # system is unavailable in this environment.
    resolve: "callable"
    version: "callable"  # callable -> version string (or "unknown")


def _hex_service_argv(entry: str):
    def resolve():
        if not HEX_SERVICE.exists():
            return None
        return [str(HEX_SERVICE), "--entry", entry]
    return resolve


def _python_service_argv(script: str, probe: "str | None" = None):
    """Resolve a Python service, or None if it cannot run in this environment.

    ``probe`` names a module the service imports (e.g. ``cypari2``); it is
    import-checked in a subprocess so a missing third-party dependency makes the
    system cleanly *unavailable* (skipped under ``--skip-unavailable``) rather
    than spawning a process that dies on import and records only errors -- which
    would leave the cross-check vacuously green for a system that never answered.
    """
    def resolve():
        path = ORACLE / script
        if not path.exists():
            return None
        if probe is not None:
            try:
                r = subprocess.run([sys.executable, "-c", f"import {probe}"],
                                   capture_output=True, timeout=60)
            except Exception:
                return None
            if r.returncode != 0:
                return None
        return [sys.executable, str(path)]
    return resolve


def _setup_script_argv(script: str):
    """Run a setup script that prints a binary path on stdout, spawn that binary."""
    def resolve():
        path = ORACLE / script
        if not path.exists() or not shutil.which("bash"):
            return None
        try:
            out = subprocess.run(["bash", str(path)], capture_output=True, text=True,
                                 timeout=7200)
        except Exception:
            return None
        if out.returncode != 0:
            return None
        binary = out.stdout.strip().splitlines()[-1] if out.stdout.strip() else ""
        return [binary] if binary and Path(binary).exists() else None
    return resolve


def _lean_toolchain() -> str:
    tc = ROOT / "lean-toolchain"
    return tc.read_text().strip() if tc.exists() else "unknown"


def _flint_version() -> str:
    try:
        import flint
        return f"python-flint {getattr(flint, '__version__', '?')}"
    except Exception:
        return "unknown"


def _pari_version() -> str:
    try:
        import cypari2
        from importlib.metadata import version
        major, minor, patch = cypari2.Pari().version()
        return f"PARI/GP {major}.{minor}.{patch} (cypari2 {version('cypari2')})"
    except Exception:
        return "unknown"


SYSTEMS = {
    "hex-factor": SystemSpec("hex-factor", _hex_service_argv("factor"), _lean_toolchain),
    "hex-lattice": SystemSpec("hex-lattice", _hex_service_argv("factorLattice"), _lean_toolchain),
    "hex-fast": SystemSpec("hex-fast", _hex_service_argv("factorFast"), _lean_toolchain),
    "hex-classical-nodecline": SystemSpec(
        "hex-classical-nodecline", _hex_service_argv("factorClassicalNoDecline"), _lean_toolchain),
    "flint": SystemSpec("flint", _python_service_argv("bz_flint_service.py", "flint"), _flint_version),
    "pari": SystemSpec("pari", _python_service_argv("bz_pari_service.py", "cypari2"), _pari_version),
    "ntl": SystemSpec("ntl", _setup_script_argv("setup_bz_ntl_driver.sh"), lambda: "NTL ZZXFactoring"),
    "isabelle-bz": SystemSpec(
        "isabelle-bz", _setup_script_argv("setup_bz_isabelle.sh"),
        lambda: "AFP Berlekamp_Zassenhaus (afp-2026-05-29)"),
    "isabelle-lll": SystemSpec(
        "isabelle-lll", _setup_script_argv("setup_bz_lll_isabelle.sh"),
        lambda: "AFP LLL_Factorization (afp-2026-05-29)"),
}

DEFAULT_SYSTEMS = list(SYSTEMS.keys())


class Service:
    """A warm subprocess with a background reader thread, so a per-call read can
    be bounded by the cutoff and the process killed on a timeout."""

    def __init__(self, argv):
        self.argv = argv
        self.proc = None
        self.q: "queue.Queue[str]" = queue.Queue()
        self.reader = None
        self._spawn()

    def _spawn(self):
        self.proc = subprocess.Popen(
            self.argv, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, text=True, bufsize=1)
        self.q = queue.Queue()

        def pump(stream, q):
            for line in stream:
                q.put(line)
            q.put("")  # EOF sentinel

        self.reader = threading.Thread(target=pump, args=(self.proc.stdout, self.q), daemon=True)
        self.reader.start()

    def respawn(self):
        self.kill()
        self._spawn()

    def kill(self):
        if self.proc and self.proc.poll() is None:
            try:
                self.proc.kill()
            except Exception:
                pass
        if self.proc:
            try:
                self.proc.wait(timeout=5)
            except Exception:
                pass

    def call(self, request: dict, timeout: float):
        """Return (reply_dict, elapsed_nanos) on success, or (None, None) on
        timeout/death. On timeout the caller should respawn."""
        line = json.dumps(request, separators=(",", ":")) + "\n"
        start = time.perf_counter_ns()
        try:
            self.proc.stdin.write(line)
            self.proc.stdin.flush()
        except Exception:
            return None, None
        try:
            reply = self.q.get(timeout=timeout)
        except queue.Empty:
            return None, None
        elapsed = time.perf_counter_ns() - start
        if reply == "":
            return None, None  # process died / EOF
        try:
            return json.loads(reply), elapsed
        except Exception:
            return {"ok": False, "error": f"unparseable reply: {reply[:200]}"}, elapsed


def degree_multiset(reply: dict):
    """Sorted factor-degree multiset (counting multiplicity) from an ok reply, or
    None if the reply is a decline / not ok."""
    if not reply.get("ok"):
        return None
    result = reply.get("result")
    if result is None:
        return None
    degrees = []
    for fac in result.get("factors", []):
        deg = len(fac["coeffs"]) - 1
        degrees.extend([deg] * int(fac.get("multiplicity", 1)))
    return sorted(degrees)


def classify(reply, elapsed):
    if reply is None:
        return "timeout"
    if not reply.get("ok"):
        return "error"
    if reply.get("result") is None:
        return "declined"
    return "ok"


def measure_overhead(service: Service, timeout: float) -> "int | None":
    samples = []
    for _ in range(OVERHEAD_REPEATS):
        reply, elapsed = service.call(OVERHEAD_INPUT, timeout)
        if reply is None:
            service.respawn()
            continue
        samples.append(elapsed)
    if not samples:
        return None
    samples.sort()
    return samples[len(samples) // 2]


def _order_for_termination(instances):
    """Return instances ordered so each family is contiguous and degree-
    ascending (families in first-seen order), the layout the early-termination
    run counter relies on. Self-contained so correctness does not depend on the
    caller's ordering."""
    family_order = {}
    for inst in instances:
        family_order.setdefault(inst["family"], len(family_order))
    return sorted(instances, key=lambda r: (family_order[r["family"]], r["degree"], r["name"]))


def sweep_system(name: str, argv, instances, cutoff: float, early_terminate_run=0):
    """Sweep one system across all instances; returns (records, overhead_nanos).

    When ``early_terminate_run > 0``, instances are reordered (family-contiguous,
    degree-ascending) and a run of that many consecutive timeouts within a
    ``MONOTONIC_FAMILIES`` family caps the family: its remaining higher-degree
    instances are recorded as timeouts (``early_terminated``) without being run.
    A solve resets the run counter. With early termination off, the caller's
    order is preserved.
    """
    if early_terminate_run > 0:
        instances = _order_for_termination(instances)
    cutoff_ns = int(cutoff * 1e9)
    service = Service(argv)
    overhead = measure_overhead(service, cutoff)
    records = []
    current_family = None
    timeout_run = 0
    capped = False
    for inst in instances:
        if inst["family"] != current_family:
            current_family = inst["family"]
            timeout_run = 0
            capped = False
        monotonic = early_terminate_run > 0 and inst["family"] in MONOTONIC_FAMILIES
        if monotonic and capped:
            records.append(_record(name, inst, "timeout", None, None, None, None,
                                   None, early_terminated=True))
            continue
        request = {"coeffs": inst["coeffs"]}
        # First call decides the repeat policy and gives the degree multiset.
        reply, elapsed = service.call(request, cutoff)
        if reply is None:
            # Distinguish a real timeout (process still alive, we kill it) from a
            # process that died on its own (crash / EOF), which is an error.
            dead = service.proc.poll() is not None
            service.respawn()
            records.append(_record(name, inst, "error" if dead else "timeout",
                                   None, None, None, None, None))
            if monotonic and not dead:
                timeout_run += 1
                if timeout_run >= early_terminate_run:
                    capped = True
            continue
        status = classify(reply, elapsed)
        degrees = degree_multiset(reply)
        factor_count = len(degrees) if degrees is not None else None
        # Median-of-5 only when the input is cheap (first call under 1 s).
        times = [elapsed]
        if elapsed is not None and elapsed < 1e9 and status == "ok":
            for _ in range(4):
                r2, e2 = service.call(request, cutoff)
                if r2 is None:
                    service.respawn()
                    break
                # A repeat that disagrees with the first answer (non-ok, or a
                # different factorization) is an anomaly: stop collecting timings
                # rather than fold an inconsistent sample into the median.
                if classify(r2, e2) != "ok" or degree_multiset(r2) != degrees:
                    break
                times.append(e2)
        times = [t for t in times if t is not None]
        median = sorted(times)[len(times) // 2] if times else None
        records.append(_record(name, inst, status, median,
                                min(times) if times else None,
                                max(times) if times else None,
                                factor_count, degrees))
        if monotonic:
            if status == "ok":
                timeout_run = 0
            elif status == "timeout":
                timeout_run += 1
                if timeout_run >= early_terminate_run:
                    capped = True
    service.kill()
    return records, overhead


def _record(system, inst, status, median, lo, hi, factor_count, degrees,
            early_terminated=False):
    rec = {
        "system": system,
        "family": inst["family"],
        "name": inst["name"],
        "degree": inst["degree"],
        "status": status,
        "median_nanos": median,
        "min_nanos": lo,
        "max_nanos": hi,
        "factor_count": factor_count,
        # kept for the cross-check pass; dropped before serialization
        "_degrees": degrees,
    }
    if early_terminated:
        rec["early_terminated"] = True
    return rec


def cross_check(records, instances):
    """Return a list of mismatch descriptions across all systems that answered,
    plus expectedFactorDegrees where present. Empty list == all agree."""
    by_name = {inst["name"]: inst for inst in instances}
    answers: dict = {}
    for rec in records:
        if rec["status"] == "ok" and rec["_degrees"] is not None:
            answers.setdefault(rec["name"], {})[rec["system"]] = rec["_degrees"]
    mismatches = []
    for name, per_system in answers.items():
        inst = by_name[name]
        expected = inst.get("expectedFactorDegrees")
        # Bucket distinct answers.
        buckets: dict = {}
        for system, degs in per_system.items():
            buckets.setdefault(tuple(degs), []).append(system)
        if expected is not None:
            for degs, systems in buckets.items():
                if list(degs) != expected:
                    mismatches.append({
                        "name": name, "kind": "expected",
                        "expected": expected, "got": list(degs), "systems": systems})
        if len(buckets) > 1:
            mismatches.append({
                "name": name, "kind": "pairwise",
                "answers": {",".join(sorted(sys)): list(degs) for degs, sys in buckets.items()}})
    return mismatches


def env_block(exe_name: str) -> dict:
    def git(args):
        try:
            return subprocess.run(["git", "-C", str(ROOT)] + args, capture_output=True,
                                  text=True).stdout.strip()
        except Exception:
            return ""
    commit = git(["rev-parse", "HEAD"]) or None
    dirty = git(["status", "--porcelain"])
    now = time.time()
    return {
        "lean_version": None,
        "lean_toolchain": _lean_toolchain(),
        "platform_target": None,
        "os": platform.system().lower(),
        "arch": platform.machine(),
        "cpu_model": platform.processor() or None,
        "cpu_cores": os.cpu_count(),
        "hostname": socket.gethostname(),
        "exe_name": exe_name,
        "lean_bench_version": None,
        "git_commit": commit,
        "git_dirty": bool(dirty) if commit else None,
        "timestamp_unix_ms": int(now * 1000),
        "timestamp_iso": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)),
    }


def load_corpus(path: Path, family=None, limit=None, combined_only=False):
    instances = []
    for line in path.read_text().splitlines():
        if not line.strip():
            continue
        rec = json.loads(line)
        if family and rec["family"] != family:
            continue
        if combined_only and not rec.get("combined"):
            continue
        instances.append(rec)
    if limit:
        instances = instances[:limit]
    return instances


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--corpus", type=Path, default=CORPUS_PATH)
    p.add_argument("--systems", default=",".join(DEFAULT_SYSTEMS),
                   help="comma-separated subset of: " + ", ".join(DEFAULT_SYSTEMS))
    p.add_argument("--cutoff", type=float, default=10.0, help="per-call cutoff seconds (default 10)")
    p.add_argument("--family", default=None, help="restrict to one family")
    p.add_argument("--limit", type=int, default=None, help="cap instances (for quick runs)")
    p.add_argument("--combined-only", action="store_true", help="only mix-doctrine combined instances")
    p.add_argument("--output", type=Path, default=None)
    p.add_argument("--skip-unavailable", action="store_true",
                   help="silently skip systems whose service cannot be spawned")
    p.add_argument("--early-terminate-run", type=int, default=DEFAULT_EARLY_TERMINATE_RUN,
                   help=f"stop a system on a monotonic family after this many consecutive "
                        f"timeouts (default {DEFAULT_EARLY_TERMINATE_RUN}; families: "
                        f"{', '.join(sorted(MONOTONIC_FAMILIES))})")
    p.add_argument("--no-early-terminate", dest="early_terminate", action="store_false",
                   help="run every instance in full (disable monotonic early termination)")
    p.set_defaults(early_terminate=True)
    args = p.parse_args()

    early_run = args.early_terminate_run if args.early_terminate else 0

    corpus_bytes = args.corpus.read_bytes()
    corpus_sha = hashlib.sha256(corpus_bytes).hexdigest()
    instances = load_corpus(args.corpus, args.family, args.limit, args.combined_only)
    requested = [s.strip() for s in args.systems.split(",") if s.strip()]
    unknown = [s for s in requested if s not in SYSTEMS]
    if unknown:
        p.error(f"unknown systems: {unknown}; choose from {list(SYSTEMS)}")

    print(f"corpus: {args.corpus.relative_to(ROOT)} ({len(instances)} instances, "
          f"sha256 {corpus_sha[:12]})", file=sys.stderr)
    print(f"cutoff: {args.cutoff}s   systems: {requested}", file=sys.stderr)

    all_records = []
    overheads = {}
    versions = {}
    for name in requested:
        spec = SYSTEMS[name]
        argv = spec.resolve()
        if argv is None:
            if not args.skip_unavailable:
                print(f"[fail] {name}: service unavailable; pass --skip-unavailable "
                      f"to record a partial sweep instead", file=sys.stderr)
                return 2
            print(f"[skip] {name}: service unavailable", file=sys.stderr)
            continue
        versions[name] = spec.version()
        print(f"[run ] {name}: {argv[0].split('/')[-1]} ...", file=sys.stderr)
        t0 = time.time()
        records, overhead = sweep_system(name, argv, instances, args.cutoff, early_run)
        overheads[name] = overhead
        all_records.extend(records)
        solved = sum(1 for r in records if r["status"] == "ok")
        skipped = sum(1 for r in records if r.get("early_terminated"))
        skip_note = f", {skipped} early-terminated" if skipped else ""
        print(f"       {name}: {solved}/{len(records)} solved in {time.time()-t0:.1f}s "
              f"(overhead {overhead} ns{skip_note})", file=sys.stderr)

    mismatches = cross_check(all_records, instances)

    for rec in all_records:
        rec.pop("_degrees", None)

    report = {
        "env": env_block("factor_sweep"),
        "config": {
            "cutoff_seconds": args.cutoff,
            "repeats_policy": "median-of-5 when first call < 1s, else single call",
            "overhead_repeats": OVERHEAD_REPEATS,
            "corpus_path": str(args.corpus.relative_to(ROOT)),
            "corpus_sha256": corpus_sha,
            "early_terminate_run": early_run,
            "early_terminate_families": sorted(MONOTONIC_FAMILIES) if early_run else [],
            "systems": requested,
            "system_versions": versions,
            "per_system_overhead_nanos": overheads,
        },
        "results": all_records,
        "cross_check": {"mismatches": mismatches, "ok": not mismatches},
    }

    host = report["env"]["hostname"] or "host"
    gitsha = (report["env"]["git_commit"] or "nogit")[:8]
    output = args.output or (ROOT / "reports" / "bench-results" /
                             f"hexbz-factor-sweep-{gitsha}-{host}.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    try:
        shown = output.relative_to(ROOT)
    except ValueError:
        shown = output
    print(f"wrote {shown}", file=sys.stderr)
    print(f"sha256 {hashlib.sha256(output.read_bytes()).hexdigest()}", file=sys.stderr)

    if mismatches:
        print(f"CROSS-CHECK FAILED: {len(mismatches)} mismatch(es)", file=sys.stderr)
        for m in mismatches[:10]:
            print("  " + json.dumps(m), file=sys.stderr)
        return 1
    print("cross-check: all answering systems agree", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
