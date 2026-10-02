#!/usr/bin/env python3
"""Run the stage-2 full-scan models using lean-bench's trial-major schedule.

The selected CPU and host activity are context, never sample rejection rules.
Every completed sample is retained. A rerun, if warranted by an inconclusive
result, must use a new output path and the unchanged command and source.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import socket
import subprocess
import time

import idle_core
import pminusone_stage2_fixtures as fixtures

ROOT = Path(__file__).resolve().parents[2]
EXE = ROOT / ".lake/build/bin/hexprimality_bench"
SOURCES = [
    "HexPrimality/PMinusOne.lean", "HexPrimality/Search.lean",
    "HexPrimality/Construction.lean", "HexIntFactor/Factor.lean",
    "bench/HexPrimality/Bench.lean", "bench/HexPrimality/PMinusOneFixtures.lean",
    "conformance-fixtures/HexPrimality/pminusone-stage2.jsonl",
    "scripts/bench/pminusone_stage2_fixtures.py",
    "scripts/bench/pminusone_stage2_sweep.py", "lean-toolchain", "lake-manifest.json",
]


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--outer-trials", type=int, default=5)
    parser.add_argument("--enumeration", action="store_true", help="measure the shared sieve/readback model")
    args = parser.parse_args()
    if args.outer_trials < 1:
        parser.error("outer-trials must be positive")
    output = args.output.resolve()
    native = output.with_suffix(".native.json")
    log = output.with_suffix(".log")
    if any(path.exists() for path in (output, native, log)):
        parser.error("refusing to overwrite retained measurements; select a new output path")
    rows = [json.loads(line) for line in fixtures.FIXTURES.read_text().splitlines()]
    fixtures.verify(rows)
    for family, path in fixtures.LEAN_FIXTURES.items():
        assert path.read_text() == fixtures.render_lean(rows, family)
    cpu = idle_core.pick()
    allowed = os.sched_getaffinity(0)
    if cpu not in allowed:
        cpu = min(allowed)
    os.sched_setaffinity(0, {cpu})
    bench_filter = "runSieve" if args.enumeration else "Stage2.Bits"
    command = [str(EXE), "run", "--filter", bench_filter, "--outer-trials",
               str(args.outer_trials), "--warmup-fraction", "0", "--export-file", str(native)]
    output.parent.mkdir(parents=True, exist_ok=True)
    metadata = {
        "command": command, "cpu": cpu, "affinity": sorted(os.sched_getaffinity(0)),
        "hostname": socket.gethostname(), "platform": platform.platform(),
        "load_before": os.getloadavg(), "source_sha256": {p: sha(ROOT / p) for p in SOURCES},
        "executable_sha256": sha(EXE), "fixture_count": len(rows),
        "schedule": "lean-bench fixed trial-major; all declared nonempty rungs",
        "sample_policy": "retain every completed sample; no activity rejection",
        "git_head": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "trace_modes": [] if args.enumeration else ["batches", "counters"],
        "modulus_bits": [] if args.enumeration else [64, 128, 256, 512],
        "model": "N * sqrt(N)" if args.enumeration else "210 + floor(last_interval_prime/210) + 2*interval_prime_count",
        "initial_giant_exponent": 0, "initial_power_multiplications": 0,
        "working_residue_bound": 252,
    }
    output.write_text(json.dumps({"metadata": metadata, "status": "running"}, indent=2) + "\n")
    print(f"Measuring {bench_filter} on CPU {cpu}; retaining output in {output}", flush=True)
    start = time.monotonic()
    with log.open("w") as stream:
        completed = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
    metadata.update(elapsed_seconds=time.monotonic() - start, load_after=os.getloadavg(),
                    exit_code=completed.returncode)
    data = {"metadata": metadata, "status": "finished",
            "native": json.loads(native.read_text()) if native.exists() else None}
    output.write_text(json.dumps(data, indent=2) + "\n")
    print(f"lean-bench exited {completed.returncode}; log: {log}", flush=True)
    return completed.returncode


if __name__ == "__main__":
    raise SystemExit(main())
