#!/usr/bin/env python3
"""Retain every compiled raw-splitter sample in a fixed shared-host schedule."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import platform
import subprocess
import sys
from datetime import datetime, timezone
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from cpu_lease import cpu_lease


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def run(exe: Path, row: dict, arm: str, step_cap: int, seed: int) -> dict:
    command = [str(exe), str(row["n"]), arm, str(step_cap), "16", "128", str(seed), "8", "262144"]
    sample = json.loads(subprocess.check_output(command, text=True, timeout=300))
    sample.update(name=row["name"], kind=row["kind"], bits=row["bits"], type="sample")
    return sample


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--exe", type=Path, default=Path(".lake/build/bin/hexprimality_squfof_measure"))
    parser.add_argument("--corpus", type=Path, default=Path("conformance-fixtures/HexPrimality/squfof-corpus.jsonl"))
    parser.add_argument("--output", type=Path, default=Path("reports/bench-results/hex-primality-squfof-native.jsonl"))
    args = parser.parse_args()
    rows = [json.loads(line) for line in args.corpus.read_text().splitlines() if line]
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    context = dict(
        type="context", host=platform.node(), platform=platform.platform(),
        processor=platform.processor(), cpu=cpu, affinity=sorted(os.sched_getaffinity(0)),
        load_start=os.getloadavg(), started=datetime.now(timezone.utc).isoformat(),
        git=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        executable_sha256=digest(args.exe), corpus_sha256=digest(args.corpus),
        schedule="two trial-major adjacent AB/BA blocks, then fixed policy arms",
        multiplier_caps=[16], step_caps=[65536, 131072, 262144], queue_capacity=128,
        rho_seeds=[1, 27, 10452], rho_restarts=8, rho_inner_requested=262144,
    )
    args.output.parent.mkdir(parents=True, exist_ok=True)
    with args.output.open("w") as handle:
        def write(item: dict) -> None:
            handle.write(json.dumps(item, separators=(",", ":")) + "\n")
            handle.flush()

        write(context)
        for trial in range(2):
            for row in rows:
                order = ("squfof", "rho") if trial == 0 else ("rho", "squfof")
                for position, arm in enumerate(order):
                    sample = run(args.exe, row, arm, 65536, 1)
                    sample.update(phase="adjacent", trial=trial, position=position)
                    write(sample)
                    print(row["name"], trial, arm, sample["status"], sample["nanos"], flush=True)
        for row in rows:
            for arm, cap, seed in (("squfof", 131072, 1), ("squfof", 262144, 1),
                                   ("reverse", 262144, 1), ("rho", 65536, 27),
                                   ("rho", 65536, 10452)):
                sample = run(args.exe, row, arm, cap, seed)
                sample.update(phase="policy")
                write(sample)
                print(row["name"], "policy", arm, cap, seed, sample["status"], flush=True)
        write(dict(type="end", finished=datetime.now(timezone.utc).isoformat(),
                   load_end=os.getloadavg()))
    lease.close()


if __name__ == "__main__":
    main()
