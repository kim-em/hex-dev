#!/usr/bin/env python3
"""Compare canonical conversion and interval signs on the same common-field fixtures."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess
import time

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
BLOCKS = 6


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path)
    parser.add_argument("output", type=Path)
    parser.add_argument("--mode", choices=("fixtures", "scalars"), default="fixtures")
    args = parser.parse_args()
    executable = args.executable.resolve()
    if not executable.is_file():
        parser.error("executable does not exist")
    args.output.mkdir(parents=True, exist_ok=False)
    cpu, lease = cpu_lease()
    affinity = os.sched_getaffinity(0)
    os.sched_setaffinity(0, {cpu})
    metadata = {
        "schema": "hex-field-sign-paired-v1", "blocks": BLOCKS, "mode": args.mode,
        "host": platform.node(), "platform": platform.platform(),
        "cpu": cpu, "originalAffinity": sorted(affinity),
        "loadBefore": os.getloadavg(), "executable": str(executable),
        "executableSha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT,
                                            text=True).strip(),
        "dirty": subprocess.check_output(["git", "status", "--porcelain"], cwd=ROOT,
                                         text=True),
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "sources": {
            path: hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in [
                "HexRealAlgebraic/FieldSign.lean",
                "conformance/HexSignDet/CommonField.lean",
                "conformance/HexSignDet/EmitCommonFields.lean",
                "scripts/bench/field_sign_paired.py",
            ]
        },
    }
    (args.output / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    expected = None
    samples = []
    with (args.output / "samples.jsonl").open("w") as stream:
        for block in range(BLOCKS):
            arms = ["legacy", "interval"] if block % 2 == 0 else ["interval", "legacy"]
            for position, arm in enumerate(arms):
                command = [str(executable)] + (["--scalars"] if args.mode == "scalars" else [])
                command += ["--legacy"] if arm == "legacy" else []
                start = time.perf_counter_ns()
                result = subprocess.run(command, capture_output=True)
                elapsed = time.perf_counter_ns() - start
                sample = {
                    "block": block, "position": position, "arm": arm,
                    "elapsedNanos": elapsed, "returncode": result.returncode,
                    "stdoutSha256": hashlib.sha256(result.stdout).hexdigest(),
                    "load": os.getloadavg(),
                }
                stream.write(json.dumps(sample) + "\n")
                stream.flush()
                samples.append(sample)
                (args.output / f"{block}-{arm}.stderr").write_bytes(result.stderr)
                if expected is None and result.returncode == 0:
                    expected = result.stdout
                    (args.output / "fixtures.jsonl").write_bytes(expected)
                if result.returncode or result.stdout != expected:
                    (args.output / f"{block}-{arm}.jsonl").write_bytes(result.stdout)
                    raise RuntimeError("fixture execution failed or the two arms disagree")
                if args.mode == "fixtures" and result.stdout != (
                    ROOT / "conformance-fixtures/HexSignDet/common-fields.jsonl"
                ).read_bytes():
                    raise RuntimeError("output differs from the committed oracle fixtures")
    medians = {
        arm: statistics.median(s["elapsedNanos"] for s in samples if s["arm"] == arm)
        for arm in ["legacy", "interval"]
    }
    ratios = []
    for block in range(BLOCKS):
        pair = {s["arm"]: s["elapsedNanos"] for s in samples if s["block"] == block}
        ratios.append(pair["legacy"] / pair["interval"])
    (args.output / "summary.json").write_text(json.dumps({
        "medianNanos": medians,
        "legacyOverInterval": medians["legacy"] / medians["interval"],
        "blockRatios": ratios, "medianBlockRatio": statistics.median(ratios),
        "completedSamples": len(samples), "reruns": 0,
    }, indent=2) + "\n")
    lease.close()
    print(json.dumps(medians))


if __name__ == "__main__":
    main()
