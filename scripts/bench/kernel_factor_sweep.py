#!/usr/bin/env python3
"""Time how long the Lean **kernel** takes to evaluate `Hex.factor` per instance.

With `native_decide` banned, the trusted way to run a hex computation inside a
proof is kernel reduction (`decide +kernel`). This harness measures that cost
directly on the factorization corpus: for each instance it

1. runs the *compiled* `Hex.factor` (via the warm `hexbz_factor_service`) to get
   hex's exact `Factorization` output, then
2. generates a one-line theorem
   `example : Hex.factor <f> = <that exact factorization> := by decide +kernel`
   and times a fresh `lean` invocation checking it.

Forcing the equality against the compiled answer makes the kernel evaluate
`factor` to a full normal form (every factor coefficient, not just the array
spine), so the wall time is honest kernel-evaluation cost. It also double-checks
that kernel reduction agrees with compiled evaluation.

Instances that exceed the wall timeout, `maxRecDepth`, or `maxHeartbeats` are
recorded as **censored** points (status `timeout` / `maxRecDepth` /
`maxHeartbeats`); on a survival chart these read as a curve that flattens where
kernel `decide` stops being viable. A fixed per-invocation import baseline is
measured once and reported so the marginal kernel time can be recovered.

This is a comparator/diagnostic sweep, **not CI** (see
SPEC/benchmarking.md § Cross-system comparator sweeps). It measures the kernel,
not a hex-internal performance claim, so the one-harness rule stays intact.

Example (frontier probe, small degrees, tight timeout):

    python3 scripts/bench/kernel_factor_sweep.py --max-degree 32 --timeout 30
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import socket
import subprocess
import sys
import time
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
CORPUS_PATH = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
HEX_SERVICE = ROOT / ".lake" / "build" / "bin" / "hexbz_factor_service"

# Kernel-reduction limits. maxRecDepth guards structural recursion depth;
# maxHeartbeats=0 disables the heartbeat cutoff so the wall-clock `--timeout`
# is the sole limit (a censored point is then always a genuine time wall).
DEFAULT_MAX_REC_DEPTH = 100000
DEFAULT_MAX_HEARTBEATS = 0

# Families whose kernel cost is NOT monotone in degree, so a single cutoff-hit is
# not the viability wall and the sweep must keep exploring higher degrees.
# Cyclotomics reorder cost by the number of modular factors, not degree.
NON_MONOTONE_FAMILIES = {"cyclotomic", "cyclotomic-products"}


def lean_env():
    out = subprocess.run(["lake", "env", "printenv", "LEAN_PATH"],
                         cwd=ROOT, capture_output=True, text=True)
    env = dict(os.environ)
    if out.returncode == 0 and out.stdout.strip():
        env["LEAN_PATH"] = out.stdout.strip()
    return env


def hex_factor(coeffs, service):
    """Return (scalar, [(coeffs, mult), ...]) from the compiled hex factorizer."""
    service.stdin.write(json.dumps({"coeffs": coeffs}) + "\n")
    service.stdin.flush()
    reply = json.loads(service.stdout.readline())
    if not reply.get("ok") or reply.get("result") is None:
        return None
    r = reply["result"]
    return r["scalar"], [(f["coeffs"], f["multiplicity"]) for f in r["factors"]]


def coeff_array(coeffs):
    return "#[" + ",".join(str(c) for c in coeffs) + "]"


def gen_theorem(coeffs, factorization, max_rec, max_heartbeats):
    scalar, factors = factorization
    facs = ",".join(f"(DensePoly.ofCoeffs {coeff_array(c)}, {m})" for c, m in factors)
    return (
        "import HexBerlekampZassenhaus.Basic\n"
        "open Hex\n"
        f"set_option maxRecDepth {max_rec} in\n"
        f"set_option maxHeartbeats {max_heartbeats} in\n"
        f"example : Hex.factor (DensePoly.ofCoeffs {coeff_array(coeffs)})\n"
        f"    = ⟨{scalar}, #[{facs}]⟩ := by decide +kernel\n"
    )


def run_lean(source, env, timeout, workdir):
    path = workdir / "KernelFactor.lean"
    path.write_text(source)
    start = time.perf_counter_ns()
    try:
        proc = subprocess.run(["lean", str(path)], env=env, capture_output=True,
                              text=True, timeout=timeout)
    except subprocess.TimeoutExpired:
        return "timeout", None, ""
    elapsed = time.perf_counter_ns() - start
    if proc.returncode == 0:
        return "ok", elapsed, ""
    err = (proc.stdout + proc.stderr)
    low = err.lower()
    if "maxrecdepth" in low or "maximum recursion depth" in low:
        return "maxRecDepth", elapsed, err[:400]
    if "maxheartbeats" in low or "deterministic timeout" in low:
        return "maxHeartbeats", elapsed, err[:400]
    return "error", elapsed, err[:400]


def import_baseline(env, workdir, repeats=3):
    path = workdir / "Baseline.lean"
    path.write_text("import HexBerlekampZassenhaus.Basic\nopen Hex\n")
    samples = []
    for _ in range(repeats):
        start = time.perf_counter_ns()
        subprocess.run(["lean", str(path)], env=env, capture_output=True, text=True)
        samples.append(time.perf_counter_ns() - start)
    samples.sort()
    return samples[len(samples) // 2]


def env_block():
    def git(args):
        try:
            return subprocess.run(["git", "-C", str(ROOT)] + args,
                                  capture_output=True, text=True).stdout.strip()
        except Exception:
            return ""
    commit = git(["rev-parse", "HEAD"]) or None
    dirty = git(["status", "--porcelain"])
    toolchain = (ROOT / "lean-toolchain").read_text().strip() if (ROOT / "lean-toolchain").exists() else None
    now = time.time()
    return {
        "lean_toolchain": toolchain,
        "os": platform.system().lower(),
        "arch": platform.machine(),
        "cpu_cores": os.cpu_count(),
        "hostname": socket.gethostname(),
        "exe_name": "kernel_factor_sweep",
        "git_commit": commit,
        "git_dirty": bool(dirty) if commit else None,
        "timestamp_unix_ms": int(now * 1000),
        "timestamp_iso": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime(now)),
    }


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--corpus", type=Path, default=CORPUS_PATH)
    p.add_argument("--timeout", type=float, default=60.0, help="per-instance wall timeout (s)")
    p.add_argument("--max-degree", type=int, default=None,
                   help="skip instances above this degree (frontier probing)")
    p.add_argument("--family", default=None)
    p.add_argument("--combined-only", action="store_true")
    p.add_argument("--max-rec-depth", type=int, default=DEFAULT_MAX_REC_DEPTH)
    p.add_argument("--max-heartbeats", type=int, default=DEFAULT_MAX_HEARTBEATS)
    p.add_argument("--explore-stop-after", type=int, default=3,
                   help="for non-monotone families (cyclotomic*), stop after this "
                        "many consecutive censored points; monotone families always "
                        "stop at the first cutoff-hit")
    p.add_argument("--output", type=Path, default=None)
    args = p.parse_args()

    if not HEX_SERVICE.exists():
        sys.exit(f"missing {HEX_SERVICE}; run `lake build hexbz_factor_service`")

    corpus_bytes = args.corpus.read_bytes()
    corpus_sha = hashlib.sha256(corpus_bytes).hexdigest()
    instances = []
    for line in args.corpus.read_text().splitlines():
        if not line.strip():
            continue
        rec = json.loads(line)
        if args.family and rec["family"] != args.family:
            continue
        if args.combined_only and not rec.get("combined"):
            continue
        if args.max_degree and rec["degree"] > args.max_degree:
            continue
        instances.append(rec)
    # Ascending degree within family so the frontier (and early-stop) is meaningful.
    instances.sort(key=lambda r: (r["family"], r["degree"], r["name"]))

    env = lean_env()
    workdir = ROOT / ".lake" / "kernel-factor-tmp"
    workdir.mkdir(parents=True, exist_ok=True)

    print("measuring import baseline ...", file=sys.stderr)
    baseline = import_baseline(env, workdir)
    print(f"import baseline: {baseline/1e9:.2f}s (subtracted for kernel-only time)", file=sys.stderr)

    service = subprocess.Popen([str(HEX_SERVICE), "--entry", "factor"],
                               stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                               stderr=subprocess.DEVNULL, text=True, bufsize=1)

    results = []
    censored_streak = {}
    for inst in instances:
        fam = inst["family"]
        # Monotone families (kernel cost rises with degree) stop at the first
        # cutoff-hit — everything above just hammers the cutoff. The non-monotone
        # families keep exploring: cyclotomic cost tracks the modular-factor count,
        # not degree (e.g. Phi_28 finishes where Phi_22/Phi_24 time out), so a
        # single failure there is not the wall.
        stop_after = args.explore_stop_after if fam in NON_MONOTONE_FAMILIES else 1
        if censored_streak.get(fam, 0) >= stop_after:
            continue  # frontier passed for this family
        factorization = hex_factor(inst["coeffs"], service)
        if factorization is None:
            results.append(_rec(inst, "declined-compiled", None, None, baseline))
            continue
        source = gen_theorem(inst["coeffs"], factorization,
                             args.max_rec_depth, args.max_heartbeats)
        status, elapsed, _err = run_lean(source, env, args.timeout, workdir)
        kernel_only = None
        if elapsed is not None:
            kernel_only = max(0, elapsed - baseline)
        results.append(_rec(inst, status, elapsed, kernel_only, baseline))
        if status == "ok":
            censored_streak[fam] = 0
        else:
            censored_streak[fam] = censored_streak.get(fam, 0) + 1
        secs = f"{elapsed/1e9:.1f}s" if elapsed else "-"
        print(f"  {fam:22s} {inst['name']:20s} deg {inst['degree']:4d}  "
              f"{status:12s} total {secs}", file=sys.stderr)

    # Shut the compiled service down, but never let a shutdown hiccup lose the
    # whole run's data — the record is written below regardless.
    try:
        service.stdin.close()
        service.wait(timeout=5)
    except Exception:
        service.kill()

    report = {
        "env": env_block(),
        "config": {
            "mode": "kernel-factor",
            "proposition": "Hex.factor f = <compiled Factorization> by decide +kernel",
            "timeout_seconds": args.timeout,
            "max_rec_depth": args.max_rec_depth,
            "max_heartbeats": args.max_heartbeats,
            "import_baseline_nanos": baseline,
            "corpus_path": str(args.corpus.relative_to(ROOT)),
            "corpus_sha256": corpus_sha,
        },
        "results": results,
    }
    host = report["env"]["hostname"] or "host"
    gitsha = (report["env"]["git_commit"] or "nogit")[:8]
    output = args.output or (ROOT / "reports" / "bench-results" /
                             f"hexbz-kernel-factor-{gitsha}-{host}.json")
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(json.dumps(report, indent=2) + "\n")
    ok = sum(1 for r in results if r["status"] == "ok")
    try:
        shown = output.relative_to(ROOT)
    except ValueError:
        shown = output
    print(f"\n{ok}/{len(results)} kernel-checked; wrote {shown}", file=sys.stderr)
    print(f"sha256 {hashlib.sha256(output.read_bytes()).hexdigest()}", file=sys.stderr)


def _rec(inst, status, total_nanos, kernel_nanos, baseline):
    return {
        "family": inst["family"],
        "name": inst["name"],
        "degree": inst["degree"],
        "status": status,
        "total_nanos": total_nanos,
        "kernel_nanos": kernel_nanos,
    }


if __name__ == "__main__":
    main()
