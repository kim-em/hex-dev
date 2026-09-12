#!/usr/bin/env python3
"""Adjacent AB/BA comparisons of two compiled sparse benchmark executables.

Cases are NAME:MODE:ITERATIONS. Iteration counts and the even number of
blocks are fixed before measurement. Every result, failure, and host-load
observation is appended to the output; load never rejects a sample.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import sys
import time

sys.path.insert(0, str(Path(__file__).resolve().parent))
from graphiso_sweep import run_group


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--before", type=Path, required=True)
    p.add_argument("--after", type=Path, required=True)
    p.add_argument("--corpus", type=Path, required=True)
    p.add_argument("--case", action="append", required=True)
    p.add_argument("--blocks", type=int, default=4)
    p.add_argument("--out", type=Path, required=True)
    args = p.parse_args()
    if args.blocks <= 0 or args.blocks % 2:
        p.error("blocks must be positive and even")
    cases = [(name, mode, int(count)) for name, mode, count in
             (case.split(":") for case in args.case)]
    if any(count <= 0 for _, _, count in cases):
        p.error("iteration counts must be positive")
    allowed = sorted(os.sched_getaffinity(0))
    cpu = allowed[os.getpid() % len(allowed)]
    binaries = {"A": args.before.resolve(), "B": args.after.resolve()}
    pairs = {}
    args.out.parent.mkdir(parents=True, exist_ok=True)
    # Refuse to overwrite evidence from a completed or interrupted comparison.
    with args.out.open("x") as out:
        def emit(row):
            out.write(json.dumps(row, sort_keys=True) + "\n")
            out.flush()
        emit(dict(kind="context", host=platform.node(), cpu=cpu,
                  blocks=args.blocks, cases=cases, toolchain=Path("lean-toolchain").read_text().strip(),
                  binaries={arm: dict(path=str(path), sha256=sha(path))
                            for arm, path in binaries.items()},
                  inputs={name: sha(args.corpus / f"{name}.graph") for name, _, _ in cases}))
        for block in range(args.blocks):
            for name, mode, count in cases:
                results = {}
                for arm in ("AB" if block % 2 == 0 else "BA"):
                    command = ["taskset", "-c", str(cpu), str(binaries[arm]),
                               str(args.corpus / f"{name}.graph"), mode, str(count)]
                    row = dict(kind="sample", block=block, arm=arm, name=name,
                               mode=mode, iterations=count, command=command,
                               started=time.time(), load_before=os.getloadavg())
                    try:
                        run = run_group(command, timeout=300)
                        row.update(returncode=run.returncode, stdout=run.stdout, stderr=run.stderr)
                        if run.returncode == 0:
                            try:
                                results[arm] = json.loads(run.stdout)
                                row["result"] = results[arm]
                            except json.JSONDecodeError as exc:
                                row["parse_error"] = str(exc)
                    except subprocess.TimeoutExpired as exc:
                        row.update(timeout=True, stdout=exc.stdout or "",
                                   stderr=exc.stderr or "")
                    row.update(finished=time.time(), load_after=os.getloadavg())
                    emit(row)
                    if "result" not in row:
                        raise RuntimeError(f"measurement failed; retained in {args.out}")
                if results["A"]["sink"] != results["B"]["sink"]:
                    raise RuntimeError("result digest changed")
                ratio = results["B"]["elapsed_ns"] / results["A"]["elapsed_ns"]
                pairs.setdefault((name, mode), []).append(ratio)
                print(f"block {block} {name} {mode}: B/A={ratio:.4f}", flush=True)
        for (name, mode), ratios in pairs.items():
            emit(dict(kind="summary", name=name, mode=mode, ratios=ratios,
                      median_ratio=statistics.median(ratios)))


if __name__ == "__main__":
    main()
