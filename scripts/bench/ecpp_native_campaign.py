#!/usr/bin/env python3
"""Run every frozen tuning/holdout subject through adjacent alternating routes."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--corpus", type=Path, default=ROOT / "reports/ecpp/native/corpus.json")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output already exists; preserve completed campaigns")
    corpus = json.loads(args.corpus.read_text())
    cpu, lease = cpu_lease()
    report = dict(cpu=cpu, host=os.uname().nodename,
                  source=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                  loadavg=list(os.getloadavg()), cases=[])
    for index, case in enumerate(corpus["cases"]):
        order = ["native", "construction"] if index % 2 == 0 else ["construction", "native"]
        row = dict(case, order="NC" if index % 2 == 0 else "CN")
        for arm in order:
            exe = "hexecpp_native" if arm == "native" else "hexecpp_compare"
            arguments = [str(case["subject"])] + ([str(case["seed"])] if arm == "native" else [])
            result = subprocess.run(["taskset", "-c", str(cpu), str(ROOT / ".lake/build/bin" / exe),
                                     *arguments], cwd=ROOT, capture_output=True, text=True)
            if result.returncode:
                row[arm] = dict(returncode=result.returncode, output=result.stdout + result.stderr)
                report["cases"].append(row)
                args.output.write_text(json.dumps(report, indent=2) + "\n")
                raise RuntimeError(row[arm]["output"])
            row[arm] = json.loads(result.stdout)
            print(case["id"], arm, flush=True)
        report["cases"].append(row)
        args.output.write_text(json.dumps(report, indent=2) + "\n")
    lease.close()


if __name__ == "__main__":
    main()
