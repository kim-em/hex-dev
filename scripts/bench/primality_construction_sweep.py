#!/usr/bin/env python3
"""Adjacent-arm fresh-module measurements for reusable Curve25519 certificates."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from scripts.bench.idle_core import pick

PREFIX = "HexPrimality.ProofProbe.Curve25519."
PAIRS = (
    ("input", "Baseline", "Input"),
    ("search", "Input", "Search"),
    ("literal", "Input", "Literal"),
    ("render", "Literal", "Render"),
    ("replay", "Literal", "Replay"),
    ("complete", "Baseline", "Tactic"),
    ("certificate-comparison", "Reference", "Replay"),
)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--blocks", type=int, default=4)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.blocks < 2 or args.blocks % 2:
        parser.error("--blocks must be positive and even, at least two")
    cpu = pick()
    modules = sorted({arm for _, a, b in PAIRS for arm in (a, b)})
    subprocess.run(["lake", "build", *[PREFIX + m for m in modules]], cwd=ROOT, check=True)
    record = {
        "host": platform.node(), "platform": platform.platform(), "cpu": cpu,
        "toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
        "diff_sha256": hashlib.sha256(subprocess.check_output(["git", "diff"], cwd=ROOT)).hexdigest(),
        "protocol": "adjacent arms, AB/BA alternating blocks; every completed sample retained",
        "checker_source_sha256": {
            name: hashlib.sha256((ROOT / name).read_bytes()).hexdigest()
            for name in ("HexPrimality/Cert.lean", "HexPrimality/Table.lean")},
        "certificates": {"reference": {"nonleaf_nodes": 5, "entries": 10},
                         "generated": {"nonleaf_nodes": 3, "entries": 8, "attempts": 29}},
        "samples": [],
    }
    args.output.parent.mkdir(parents=True, exist_ok=True)
    def save() -> None:
        args.output.write_text(json.dumps(record, indent=2) + "\n")
    for block in range(args.blocks):
        for component, a, b in PAIRS:
            for arm in ((a, b) if block % 2 == 0 else (b, a)):
                module = PREFIX + arm
                artifact = ROOT / ".lake/build/lib/lean" / Path(module.replace(".", "/") + ".olean")
                artifact.unlink(missing_ok=True)
                source = ROOT / "bench" / Path(module.replace(".", "/") + ".lean")
                before = os.getloadavg()
                start = time.perf_counter()
                result = subprocess.run(["taskset", "-c", str(cpu), "lake", "build", module],
                                        cwd=ROOT, capture_output=True, text=True)
                sample = {
                    "block": block, "component": component, "arm": arm,
                    "seconds": time.perf_counter() - start, "returncode": result.returncode,
                    "load_before": before, "load_after": os.getloadavg(),
                    "source_bytes": source.stat().st_size,
                    "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
                    "olean_bytes": artifact.stat().st_size if artifact.exists() else None,
                    "stdout": result.stdout, "stderr": result.stderr,
                }
                record["samples"].append(sample)
                save()
                print(f"{block} {component} {arm}: {sample['seconds']:.3f}s", flush=True)
                if result.returncode:
                    raise SystemExit(result.returncode)
    save()


if __name__ == "__main__":
    main()
