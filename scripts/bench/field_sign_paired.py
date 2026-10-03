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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("executable", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    executable = args.executable.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    cpu, lease = cpu_lease()
    affinity = os.sched_getaffinity(0)
    os.sched_setaffinity(0, {cpu})
    metadata = {
        "schema": "hex-field-sign-paired-v1", "blocks": 6,
        "host": platform.node(), "platform": platform.platform(),
        "cpu": cpu, "originalAffinity": sorted(affinity),
        "loadBefore": os.getloadavg(), "executable": str(executable),
        "executableSha256": hashlib.sha256(executable.read_bytes()).hexdigest(),
        "revision": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
        "toolchain": Path("lean-toolchain").read_text().strip(),
        "sources": {
            path: hashlib.sha256(Path(path).read_bytes()).hexdigest() for path in [
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
        for block in range(6):
            arms = ["legacy", "interval"] if block % 2 == 0 else ["interval", "legacy"]
            for position, arm in enumerate(arms):
                command = [str(executable)] + (["--legacy"] if arm == "legacy" else [])
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
                if expected is None:
                    expected = result.stdout
                    (args.output / "fixtures.jsonl").write_bytes(expected)
                if result.returncode or result.stdout != expected:
                    (args.output / f"{block}-{arm}.jsonl").write_bytes(result.stdout)
                    raise RuntimeError("fixture execution failed or the two arms disagree")
    medians = {
        arm: statistics.median(s["elapsedNanos"] for s in samples if s["arm"] == arm)
        for arm in ["legacy", "interval"]
    }
    (args.output / "summary.json").write_text(json.dumps({
        "medianNanos": medians,
        "legacyOverInterval": medians["legacy"] / medians["interval"],
        "completedSamples": len(samples), "reruns": 0,
    }, indent=2) + "\n")
    lease.close()
    print(json.dumps(medians))


if __name__ == "__main__":
    main()
