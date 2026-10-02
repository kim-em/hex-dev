#!/usr/bin/env python3
"""Measure imported sparse graph_iso proofs with adjacent import baselines.

Run after building HexGraphIsoSparseProofProbe.
Every completed sample is flushed immediately; existing evidence is never
overwritten. CFI uses a separately recorded timeout and larger Lean limits.
"""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench import fresh_module_sweep as fresh  # noqa: E402
from scripts.bench.graphiso_kernel_cost import _profile  # noqa: E402

PREFIX = "HexGraphIso.SparseProofProbe."
CASES = ("Positive12", "Negative12", "Coloured10Pos", "Coloured10Neg")
AXIOMS = ["propext", "Classical.choice", "Quot.sound"]


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, type=Path)
    parser.add_argument("--samples", type=int, default=4)
    parser.add_argument("--timeout", type=float, default=120)
    parser.add_argument("--cfi", action="store_true")
    parser.add_argument("--cfi-timeout", type=float, default=600)
    args = parser.parse_args()
    if args.samples <= 0 or args.samples % 2:
        parser.error("samples must be positive and even")
    if min(args.timeout, args.cfi_timeout) <= 0:
        parser.error("timeouts must be positive")
    cpus = sorted(os.sched_getaffinity(0))
    cpu = cpus[os.getpid() % len(cpus)]
    os.sched_setaffinity(0, {cpu})
    cases = list(CASES) + (["Cfi"] if args.cfi else [])
    spec = fresh.SweepSpec(
        description=__doc__,
        pairs=tuple(fresh.ProbePair(case, fresh.ProbeModule(PREFIX + "Baseline"),
                    fresh.ProbeModule(PREFIX + case), {}) for case in cases),
        probe_target="HexGraphIsoSparseProofProbe", schema="sparse-replay-v1",
        measurement="adjacent-fresh-module-builds", output_stem="sparse-replay")
    before = fresh.source_hashes(spec, Path(__file__))
    env = fresh.environment()
    timer = fresh.time_binary()
    if timer is None:
        parser.error("GNU time is required to record peak RSS")
    args.out.parent.mkdir(parents=True, exist_ok=True)
    with args.out.open("x") as out:
        def emit(row):
            out.write(json.dumps(row, sort_keys=True) + "\n")
            out.flush()
        emit(dict(kind="context", environment=env, source_sha256=before,
                  cpu=cpu, lean_workers=os.environ.get("LEAN_NUM_THREADS"),
                  samples=args.samples, cases=cases,
                  timeout_s=args.timeout, cfi_timeout_s=args.cfi_timeout,
                  cleanup="SIGKILL entire process group on timeout"))
        for round_index in range(args.samples):
            for case in fresh.rotate(cases, round_index):
                pair = {}
                order = ["Baseline", case] if round_index % 2 == 0 else [case, "Baseline"]
                for name in order:
                    module = PREFIX + name
                    fresh.remove_module_outputs(module)
                    command = ["lake", "build", f"+{module}:olean"]
                    timeout = args.cfi_timeout if case == "Cfi" else args.timeout
                    start = time.monotonic()
                    row = dict(kind="sample", round=round_index, case=case,
                               module=module, command=command, timeout_s=timeout,
                               load_before=os.getloadavg())
                    proc = subprocess.Popen(
                        [timer, "-f", fresh.RSS_MARKER + "%M", *command],
                        cwd=ROOT, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                        text=True, start_new_session=True)
                    try:
                        output, _ = proc.communicate(timeout=timeout)
                    except subprocess.TimeoutExpired:
                        try:
                            os.killpg(proc.pid, signal.SIGKILL)
                        except ProcessLookupError:
                            pass
                        output, _ = proc.communicate()
                        row["timeout"] = True
                    profile = "cumulative profiling times:" + output.rsplit("cumulative profiling times:", 1)[-1]
                    row.update(wall_s=time.monotonic() - start, returncode=proc.returncode,
                               output=output, profile_s=_profile(profile),
                               load_after=os.getloadavg(),
                               artifacts=fresh.artifact_sizes(module, Path("bench")),
                               axioms=fresh.parse_axioms(output))
                    rss = output.rsplit(fresh.RSS_MARKER, 1)
                    row["peak_rss_kb"] = int(rss[1].splitlines()[0]) if len(rss) == 2 else None
                    row["ok"] = proc.returncode == 0 and row["axioms"] == (None if name == "Baseline" else AXIOMS)
                    emit(row)
                    print(f"round {round_index + 1}: {name} {row['wall_s']:.3f}s, "
                          f"peak {row['peak_rss_kb']} KiB, ok={row['ok']}", flush=True)
                    if not row["ok"]:
                        return 1
                    pair[name] = row["wall_s"]
                emit(dict(kind="pair", round=round_index, case=case, order=order,
                          delta_s=pair[case] - pair["Baseline"]))
        unchanged = fresh.source_hashes(spec, Path(__file__)) == before
        emit(dict(kind="completion", source_unchanged=unchanged,
                  release_quality=unchanged and not env["git_dirty"]))
        return 0 if unchanged else 1


if __name__ == "__main__":
    raise SystemExit(main())
