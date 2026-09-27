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


def paired_arithmetic(exe, output):
    """Compare canonical subtraction and ordered comparison in adjacent arms."""
    names = ["Hex.OrderedFnBench.subtraction", "Hex.OrderedFnBench.comparison"]
    schedule = {"parameters": [128, 256, 512, 1024, 2048, 4096, 8192, 16384],
                "trials": 4, "target_nanos": 1000000000, "timeout_seconds": 60,
                "names": names, "order": "trial-major; AB on even trials, BA on odd trials"}
    (output / "schedule.json").write_text(json.dumps(schedule, indent=2) + "\n")
    with (output / "paired.jsonl").open("w") as rows:
        for trial in range(schedule["trials"]):
            for param in schedule["parameters"]:
                for name in names if trial % 2 == 0 else names[::-1]:
                    command = [str(exe), "_child", "--bench", name, "--param", str(param),
                               "--target-nanos", str(schedule["target_nanos"])]
                    stem = output / f"{trial}-{param}-{name.rsplit('.', 1)[-1]}"
                    # Write directly to files so a failure or timeout retains partial output.
                    with stem.with_suffix(".stdout").open("w") as stdout, \
                            stem.with_suffix(".stderr").open("w") as stderr:
                        result = subprocess.run(command, stdout=stdout, stderr=stderr,
                                                timeout=schedule["timeout_seconds"])
                    result.check_returncode()
                    row = json.loads(stem.with_suffix(".stdout").read_text())
                    if row["status"] != "ok":
                        raise RuntimeError(f"unsuccessful measurement: {stem}")
                    row["trial_index"] = trial
                    rows.write(json.dumps(row) + "\n")
                    rows.flush()
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--filter", default="Hex.OrderedFnBench")
    parser.add_argument("--names", nargs="*", default=[])
    parser.add_argument("--paired-arithmetic", action="store_true")
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
        # The parent needs workers for pipe reads and its timeout task.
        # CPU affinity still confines the measurement to one selected CPU.
        os.environ["LEAN_NUM_THREADS"] = "4"
        args.output.mkdir(parents=True, exist_ok=False)
        exe = ROOT / ".lake/build/bin/hexorderedfn_bench"
        command = [str(exe), "run", "--filter", args.filter,
                   "--export-file", str(args.output / "runtime.json"), *args.names]
        context = {"command": command, "cpu": cpu, "host": platform.node(),
                   "platform": platform.platform(), "load_before": os.getloadavg(),
                   "lean_num_threads": os.environ["LEAN_NUM_THREADS"],
                   "commit": subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                   "executable_sha256": hashlib.sha256(exe.read_bytes()).hexdigest()}
        (args.output / "context.json").write_text(json.dumps(context, indent=2) + "\n")
        if args.paired_arithmetic:
            context["command"] = [sys.executable, __file__, "--output", str(args.output),
                                  "--paired-arithmetic"]
        returncode = None
        try:
            if args.paired_arithmetic:
                returncode = paired_arithmetic(exe, args.output)
            else:
                with (args.output / "runtime.log").open("w") as log:
                    returncode = subprocess.run(command, stdout=log, stderr=subprocess.STDOUT).returncode
            return returncode
        finally:
            context.update(returncode=returncode, load_after=os.getloadavg(),
                           executable_sha256_after=hashlib.sha256(exe.read_bytes()).hexdigest())
            (args.output / "context.json").write_text(json.dumps(context, indent=2) + "\n")
    finally:
        lease.close()


if __name__ == "__main__":
    raise SystemExit(main())
