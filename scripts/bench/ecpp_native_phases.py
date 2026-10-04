#!/usr/bin/env python3
"""Serial trial-major fresh-module measurements for native ECPP proof phases."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import re
import subprocess
import time

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
MODULES = ["NativeBaseline", "NativeReify", "NativeDirect", "Native256_0"]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "reports/ecpp/native/phases.json")
    parser.add_argument("--native512", action="store_true")
    args = parser.parse_args()
    modules = ["Native512Baseline", "Native512Reify", "Native512Direct"] if args.native512 else MODULES
    if args.output.exists():
        parser.error("output already exists; preserve completed phase measurements")
    cpu, lease = cpu_lease()
    report = dict(host=os.uname().nodename, cpu=cpu,
                  source=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                  lean=subprocess.check_output(["lake", "--version"], cwd=ROOT, text=True).strip(),
                  source_hashes={name: hashlib.sha256((ROOT / "bench/HexECPPMathlib/ProofProbe" / (name + ".lean")).read_bytes()).hexdigest() for name in modules},
                  samples=[])
    for trial in range(4):
        for name in modules:
            module = "HexECPPMathlib.ProofProbe." + name
            relative = Path(*module.split("."))
            for suffix in (".olean", ".olean.private", ".olean.server", ".ilean", ".trace", ".olean.hash"):
                (ROOT / ".lake/build/lib/lean" / relative).with_suffix(suffix).unlink(missing_ok=True)
            start = time.monotonic_ns()
            command = ["taskset", "-c", str(cpu), "lake", "build", "+" + module + ":olean"]
            timer = shutil.which("time")
            if timer:
                command = [timer, "-f", "HEX_RSS_KB=%M"] + command
            result = subprocess.run(command, cwd=ROOT, capture_output=True, text=True)
            build_line = next((line for line in result.stdout.splitlines()
                               if re.search(r"Built " + re.escape(module) + r" \(", line)), None)
            sample = dict(rebuilt=build_line is not None, build_line=build_line,
                          trial=trial, module=module, wall_ns=time.monotonic_ns() - start,
                          returncode=result.returncode, loadavg=list(os.getloadavg()))
            for line in result.stderr.splitlines():
                if line.startswith("HEX_RSS_KB="):
                    sample["rss_kb"] = int(line.split("=")[1])
            if result.returncode:
                sample["output"] = result.stdout + result.stderr
            report["samples"].append(sample)
            args.output.write_text(json.dumps(report, indent=2) + "\n")
            print(trial, name, round(sample["wall_ns"] / 1e9, 3), result.returncode, flush=True)
            if result.returncode:
                raise RuntimeError(sample["output"])
            if build_line is None:
                raise RuntimeError("fresh target did not rebuild: " + result.stdout)
    # Keep the lease alive through the entire schedule.
    lease.close()


if __name__ == "__main__":
    main()
