#!/usr/bin/env python3
"""Measure existing API anchors before/after certified isolation reuse.

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
    selection = parser.add_mutually_exclusive_group()
    selection.add_argument("--conversion-only", action="store_true",
                        help="Measure the existing fixed-field conversion anchor instead of scalar consumers")
    selection.add_argument("--canonical-arithmetic-only", action="store_true",
                           help="Measure existing canonical addition, multiplication and common-field powers")
    selection.add_argument("--roots-only", action="store_true",
                           help="Measure RealAlgebraicPoly.roots on existing degree families")
    selection.add_argument("--filter-roots-only", action="store_true",
                           help="Measure the existing reducible-parent X^4-1 filter control")
    args = parser.parse_args()
    directories = {"Before": args.before.resolve(), "After": args.after.resolve()}
    sources = {
        arm: json.loads((directory / "metadata.json").read_text())
        for arm, directory in directories.items()
    }
    number_field = args.conversion_only or args.canonical_arithmetic_only
    executable = "hexnumberfield_bench" if number_field else "hexrealalgebraic_bench"
    bench = "bench/HexNumberField/Bench.lean" if number_field else "bench/HexRealAlgebraic/Bench.lean"
    targets = {"FixedConversion": "Hex.NumberFieldBench.runQAdjoinCanonical",
               "CanonicalAdd": "Hex.NumberFieldBench.runAlgebraicAdd",
               "CanonicalMul": "Hex.NumberFieldBench.runAlgebraicMul",
               "CommonPowers": "Hex.NumberFieldBench.runCommonPowers"}
    families = ({"FixedConversion": [2]} if args.conversion_only else
                {"CanonicalAdd": [4], "CanonicalMul": [2], "CommonPowers": [16]}
                if args.canonical_arithmetic_only else {"FilterRoots": [4]}
                if args.filter_roots_only else
                {"RationalRoots": [2, 4, 8], "QuadraticRoots": [1, 2, 4]}
                if args.roots_only else FAMILIES)
    if sources["Before"]["sources"][bench] != sources["After"]["sources"][bench]:
        raise SystemExit("Benchmark source differs between compiled arms")
    executables = {}
    for arm, metadata in sources.items():
        if metadata["status"]:
            raise SystemExit(f"{arm} was compiled from a dirty source checkout")
        binary = metadata["binaries"][executable]
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
        "families": families,
        "cpu": cpu,
        "host": os.uname().nodename,
        "load_start": os.getloadavg(),
        "start": datetime.datetime.now(datetime.timezone.utc).isoformat(),
        "schedule": "Four trial-major blocks, adjacent Before/After arms, alternating AB/BA",
        "boundary": "Existing unchanged benchmark input and expected result fingerprint. "
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
            for operation, sizes in families.items():
                for size in sizes:
                    for arm in order:
                        label = f"{operation}-{size}-{trial}-{arm}"
                        target = (targets[operation] if number_field else
                                  "Hex.RealAlgebraicBench.runFilterRoots" if args.filter_roots_only else
                                  f"Hex.RealAlgebraicBench.run{operation}{size}" if args.roots_only
                                  else f"Hex.RealAlgebraicScaling.run{operation}{size}")
                        command = [
                            str(executables[arm]), "run",
                            target,
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
            digest(executables[arm]) == sources[arm]["binaries"][executable]["sha256"]
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
