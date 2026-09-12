#!/usr/bin/env python3
"""Collect row-reduce field sweeps and adjacent AB/BA FLINT comparisons.

All completed measurements are retained. CPU leases only coordinate placement;
load is recorded without screening or rejecting samples. Use a fresh output
prefix for the one permitted unchanged rerun of inconclusive registrations.
"""
from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import time


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("prefix", type=Path)
    parser.add_argument("--phase", choices=("scientific", "comparisons"), default="scientific")
    parser.add_argument("--names", nargs="*", help="Specific unchanged registrations for a rerun")
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[2]
    source = root / "bench/HexRowReduce/Bench.lean"
    exe = root / ".lake/build/bin/hexrowreduce_bench"
    prefix = args.prefix.resolve()
    prefix.parent.mkdir(parents=True, exist_ok=True)
    meta_path = Path(str(prefix) + ".meta.json")
    if meta_path.exists():
        raise FileExistsError(f"refusing to overwrite completed run metadata: {meta_path}")
    cpus = sorted(os.sched_getaffinity(0))
    offset = os.getpid() % len(cpus)
    for cpu in cpus[offset:] + cpus[:offset]:
        lease = open(f"/tmp/hex-bench-cpu-{cpu}.lock", "a")
        try:
            fcntl.flock(lease, fcntl.LOCK_EX | fcntl.LOCK_NB)
            break
        except BlockingIOError:
            lease.close()
    else:
        raise RuntimeError("all measurement CPU leases are held")
    os.sched_setaffinity(0, {cpu})
    os.environ["LEAN_NUM_THREADS"] = "1"
    sources = ["bench/HexRowReduce/Bench.lean", "HexRowReduce/Inverse.lean",
               "HexRowReduce/Solve.lean", "scripts/oracle/flint_bench_driver.py",
               "scripts/bench/row_reduce_fields.py"]
    metadata = {
        "source_commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip(),
        "source_sha256": {p: hashlib.sha256((root / p).read_bytes()).hexdigest() for p in sources},
        "cpu": cpu, "hostname": os.uname().nodename,
        "load_before": Path("/proc/loadavg").read_text().strip(),
        "phase": args.phase,
        "schedule": "fixed trial-major" if args.phase == "scientific" else "four adjacent AB/BA blocks",
        "commands": [],
    }

    def save():
        meta_path.write_text(json.dumps(metadata, indent=2) + "\n")

    def run(argv, suffix):
        output = Path(str(prefix) + suffix + ".json")
        command = [str(exe), *argv, "--export-file", str(output)]
        print("starting", suffix or "scientific", "on CPU", cpu, flush=True)
        start = time.monotonic()
        with open(str(prefix) + suffix + ".log", "w") as log:
            result = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
        metadata["commands"].append({"argv": command, "exit_code": result.returncode,
                                     "seconds": time.monotonic() - start})
        save()
        print("finished", suffix or "scientific", "exit", result.returncode, flush=True)
        return result.returncode

    save()
    failures = 0
    if args.phase == "scientific":
        section = source.read_text().split("namespace Field\n", 1)[1]
        names = args.names or ["Hex.RowReduceBench.Field." + n for n in
                              re.findall(r"^setup_benchmark (\w+)", section, re.M)]
        failures += run(["run", *names], "") != 0
    else:
        for n in (8, 16, 32):
            for op in ("Inverse", "Solve"):
                arms = [f"Hex.RowReduceBench.Field.{engine}{op}{n}" for engine in ("lean", "flint")]
                for block in range(4):
                    order = arms if block % 2 == 0 else arms[::-1]
                    failures += run(["compare", *order, "--repeats", "1"], f"-{op.lower()}-{n}-{block}") != 0
        failures += run(["run", "Hex.RowReduceBench.runFlintOverhead", "--repeats", "4"], "-overhead") != 0
    metadata["load_after"] = Path("/proc/loadavg").read_text().strip()
    save()
    return int(failures != 0)


if __name__ == "__main__":
    raise SystemExit(main())
