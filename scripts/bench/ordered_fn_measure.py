#!/usr/bin/env python3
"""Measure compiled ordered rational-function operations with the lean-bench trial-major schedule.

Every completed sample is retained. CPU placement does not require an idle CPU.
"""

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
from scripts.bench.structural_tactic_sweep import acquire_cpu


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--filter", default="Hex.OrderedFnBench")
    parser.add_argument("--names", nargs="*", default=[])
    args = parser.parse_args()
    args.output = args.output.resolve()
    os.chdir(ROOT)
    require_clean = subprocess.check_output(["git", "status", "--porcelain"], text=True)
    if require_clean:
        raise RuntimeError("commit source changes before recording runtime evidence")
    subprocess.run(["lake", "build", "hexorderedfn_bench"], check=True)
    cpu, lease = acquire_cpu()
    try:
        os.sched_setaffinity(0, {cpu})
        os.environ["LEAN_NUM_THREADS"] = "1"
        args.output.mkdir(parents=True, exist_ok=False)
        exe = ROOT / ".lake/build/bin/hexorderedfn_bench"
        command = [str(exe), "run", "--filter", args.filter,
                   "--export-file", str(args.output / "runtime.json"), *args.names]
        context = {"command": command, "cpu": cpu, "host": platform.node(),
                   "platform": platform.platform(), "load_before": os.getloadavg(),
                   "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                   "executable_sha256": hashlib.sha256(exe.read_bytes()).hexdigest()}
        (args.output / "context.json").write_text(json.dumps(context, indent=2) + "\n")
        with (args.output / "runtime.log").open("w") as log:
            result = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT)
        context.update(returncode=result.returncode, load_after=os.getloadavg())
        (args.output / "context.json").write_text(json.dumps(context, indent=2) + "\n")
        return result.returncode
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
