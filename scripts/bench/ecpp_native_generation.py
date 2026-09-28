#!/usr/bin/env python3
"""Reproduce every successful campaign output through the public native bridge."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts/ci"))
from check_ecpp_pari import scratch_modules


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign", type=Path, action="append")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output already exists; preserve completed observations")
    campaigns = args.campaign or [ROOT / "reports/ecpp/native" / name
                                 for name in ("campaign-updated.json", "validation.json")]
    cases = [case for path in campaigns for case in json.loads(path.read_text())["cases"]
             if case["native"]["verdict"] == "success"]
    source = "import HexECPPMathlib.Native\n\nopen Lean\n\nset_option maxHeartbeats 0\n\n"
    source += "run_cmd Lean.Elab.Command.liftTermElabM do\n"
    for case in cases:
        source += f'''  let (rows, _) ← Hex.ECPP.Native.generate {case['subject']} {case['seed']}
  unless rows == {json.dumps(case['native']['rows'])} do
    throwError "public generation changed {case['id']}"
  logInfo "NATIVE_KERNEL {case['id']}"
'''
    cpu, lease = cpu_lease()
    with scratch_modules() as folder:
        (folder / "Generate.lean").write_text(source)
        start = time.monotonic_ns()
        result = subprocess.run(["taskset", "-c", str(cpu), "lake", "build",
                                 "+HexECPPMathlib." + folder.name + ".Generate:olean"],
                                cwd=ROOT, capture_output=True, text=True)
        output = result.stdout + result.stderr
        confirmations = [line for line in output.splitlines() if "NATIVE_KERNEL" in line]
        report = dict(source_commit=subprocess.check_output(["git", "rev-parse", "HEAD"],
                                                            cwd=ROOT, text=True).strip(),
                      host=os.uname().nodename, cpu=cpu, loadavg=list(os.getloadavg()),
                      lean=subprocess.check_output(["lake", "--version"], cwd=ROOT, text=True).strip(),
                      source=source, returncode=result.returncode,
                      wall_ns=time.monotonic_ns() - start, confirmations=confirmations)
        if result.returncode:
            report["output"] = [line for line in output.splitlines() if line.startswith("error:")]
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        if result.returncode or len(confirmations) != len(cases):
            raise RuntimeError(str(report.get("output", "missing confirmations")))
        print("confirmed", len(cases), "public native productions with kernel proofs")
    lease.close()


if __name__ == "__main__":
    main()
