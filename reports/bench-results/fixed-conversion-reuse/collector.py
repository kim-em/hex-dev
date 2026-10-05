#!/usr/bin/env python3
"""Measure scalar arithmetic before/after certified fixed-conversion reuse.

Both directories contain frozen executables, source snapshots and metadata.json.
Four trial-major blocks alternate adjacent AB/BA arms. Keep every completed arm;
do not filter host activity, retry failures or fit a complexity model.
"""
from __future__ import annotations

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.cpu_lease import cpu_lease

FAMILIES = {"Add": [2, 4, 8], "Sqrt": [2, 4, 8]}


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    directories = {"Before": args.before.resolve(), "After": args.after.resolve()}
    sources = {
        arm: json.loads((directory / "metadata.json").read_text())
        for arm, directory in directories.items()
    }
    bench = "bench/HexRealAlgebraic/Bench.lean"
    if sources["Before"]["sources"][bench] != sources["After"]["sources"][bench]:
        raise SystemExit("Benchmark source differs between compiled arms")
    executables = {}
    for arm, metadata in sources.items():
        if metadata["status"]:
            raise SystemExit(f"{arm} was compiled from a dirty source checkout")
        binary = metadata["binaries"]["hexrealalgebraic_bench"]
        executables[arm] = Path(binary["path"])
        if digest(executables[arm]) != binary["sha256"]:
            raise SystemExit(f"Frozen {arm} executable hash changed")
        for name, expected in metadata["sources"].items():
            snapshot = directories[arm] / (name.replace("/", "-") + ".txt")
            if digest(snapshot) != expected:
                raise SystemExit(f"Source snapshot changed: {arm} {name}")

    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    for arm, directory in directories.items():
        for snapshot in directory.glob("*.txt"):
            shutil.copyfile(snapshot, output / f"{arm}-{snapshot.name}")
    shutil.copyfile(Path(__file__), output / "collector.py")
    cpu, lease = cpu_lease()
    os.sched_setaffinity(0, {cpu})
    metadata = {
        "sources": sources,
        "families": FAMILIES,
        "cpu": cpu,
        "host": os.uname().nodename,
        "load_start": os.getloadavg(),
        "start": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "schedule": "Four trial-major blocks, adjacent Before/After arms, alternating AB/BA",
        "boundary": "Identical prepared operands and canonical polynomial/sign result guards. "
                    "Preparation and separate warmup excluded; registered caps unchanged. "
                    "Each arm uses one fixed batch with a 50 ms floor. Descriptive comparison, "
                    "no scientific mode admission or portable timing budget.",
        "arms": [],
    }

    def save() -> None:
        (output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")

    save()
    try:
        for trial in range(4):
            order = ["Before", "After"] if trial % 2 == 0 else ["After", "Before"]
            for operation, sizes in FAMILIES.items():
                for size in sizes:
                    for arm in order:
                        label = f"{operation}-{size}-{trial}-{arm}"
                        command = [
                            str(executables[arm]), "run",
                            f"Hex.RealAlgebraicScaling.run{operation}{size}",
                            "--repeats", "1", "--min-total-seconds", "0.05",
                            "--export-file", str(output / f"{label}.json"),
                        ]
                        start = time.monotonic()
                        with (output / f"{label}.log").open("w") as log:
                            result = subprocess.run(command, cwd=ROOT, stdout=log,
                                                    stderr=subprocess.STDOUT, check=False)
                        metadata["arms"].append({
                            "operation": operation, "size": size, "trial": trial,
                            "arm": arm, "order": order, "command": command,
                            "exit_code": result.returncode,
                            "elapsed_seconds": time.monotonic() - start,
                            "output": f"{label}.json",
                        })
                        save()
                        print(label, "exit", result.returncode, flush=True)
    finally:
        metadata["load_end"] = os.getloadavg()
        metadata["binaries_unchanged"] = all(
            digest(executables[arm]) == sources[arm]["binaries"]["hexrealalgebraic_bench"]["sha256"]
            for arm in executables
        )
        metadata["artifacts"] = {
            path.name: digest(path) for path in output.iterdir()
            if path.is_file() and path.name != "metadata.json"
        }
        save()
        lease.close()


if __name__ == "__main__":
    main()
