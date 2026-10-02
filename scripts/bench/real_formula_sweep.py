#!/usr/bin/env python3
"""Run shared-host real-formula evidence through the LeanBench compiled benchmark harness."""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))

from scripts.bench.cpu_lease import cpu_lease


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("track", choices=["compiled"])
    parser.add_argument("--output", type=Path, required=True)
    args, forwarded = parser.parse_known_args()
    os.chdir(ROOT)
    cpu, lease = cpu_lease()
    try:
        os.sched_setaffinity(0, {cpu})
        args.output.parent.mkdir(parents=True, exist_ok=True)
        command = [".lake/build/bin/hexrealformula_bench", "run", "--filter",
                   "Hex.RealFormula.Bench", "--export-file", str(args.output), *forwarded]
        paths = [Path("bench/HexRealFormula/Bench.lean"), Path("HexRealFormula.lean"),
                 *sorted(Path("HexRealFormula").glob("*.lean")),
                 Path("HexMvPoly/Mono.lean"), Path("HexMvPoly/Kernel.lean"),
                 Path("scripts/bench/real_formula_sweep.py"), Path("lean-toolchain"),
                 Path("lake-manifest.json")]
        context = {
            "command": command, "cpu": cpu, "host": platform.node(),
            "platform": platform.platform(), "load": os.getloadavg(),
            "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
            "dirty": bool(subprocess.check_output(["git", "status", "--porcelain"])),
            "source_sha256": {str(p): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        }
        args.output.with_suffix(".context.json").write_text(json.dumps(context, indent=2) + "\n")
        return subprocess.run(command).returncode
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
