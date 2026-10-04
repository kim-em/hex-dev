#!/usr/bin/env python3
"""Confirm capability gains against actual elaborator extension discovery."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "scripts/ci"))
from check_ecpp_pari import scratch_modules
from cpu_lease import cpu_lease


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--campaign", type=Path, default=ROOT / "reports/ecpp/native/campaign.json")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output already exists; preserve completed observations")
    campaign = json.loads(args.campaign.read_text())
    if campaign.get("split") == "holdout":
        cases = [dict(id=c["id"], subject=c["subject"], bits=512,
                      native=c["arms"]["native"]["result"],
                      construction=c["arms"]["construction"]["result"])
                 for c in campaign["cases"] if c["trial"] == 0]
    else:
        cases = campaign["cases"]
    cases = [c for c in cases
             if c["bits"] > 128 and c["native"]["verdict"] == "success"
             and c["construction"]["construction"]["verdict"].endswith("exhausted")]
    cpu, lease = cpu_lease()
    with scratch_modules() as folder:
        module = "HexECPPMathlib." + folder.name + ".Compare"
        source = '''import HexPrimality.Elab
import HexIntFactor.Primality

open Lean Hex.PrimalityTactic

-- Let the finite construction allocation finish independently of elaboration fuel.
set_option maxHeartbeats 0

run_cmd Lean.Elab.Command.liftTermElabM do
  unless constructionExtensionNames == [`HexIntFactor.PrimalityTactic.constructionExtension] do
    throwError "the current construction portfolio changed; update the comparator"
'''
        for case in cases:
            n = case["subject"]
            attempts = case["construction"]["construction"]["attempts"]
            retried = "true" if case["construction"]["construction"]["ecm_retry"] else "false"
            source += f'''  let (result, allocations) ← construct {n} Hex.Nat.constructionBudget
  unless allocations.any (fun (name, _) => name == ``Hex.Nat.ecmConstructionFactor) == {retried} do
    throwError "ECM extension allocation changed"
  match result with
  | .ok _ => throwError "expected full construction exhaustion for {n}"
  | .error f =>
    unless f.stop == .exhausted && f.attempts == {attempts} do
      throwError "construction outcome changed for {n}"
    logInfo m!"FULL_CONSTRUCTION {case['id']}: exhausted after {{f.attempts}} attempts"
'''
        (folder / "Compare.lean").write_text(source)
        start = time.monotonic_ns()
        result = subprocess.run(["taskset", "-c", str(cpu), "lake", "build", "+" + module + ":olean"],
                                cwd=ROOT, capture_output=True, text=True)
        output = result.stdout + result.stderr
        confirmations = [line for line in output.splitlines() if "FULL_CONSTRUCTION" in line]
        report = dict(cpu=cpu, host=os.uname().nodename,
                      source_commit=subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=ROOT, text=True).strip(),
                      lean=subprocess.check_output(["lake", "--version"], cwd=ROOT, text=True).strip(),
                      source=source, cases=[c["id"] for c in cases],
                      confirmations=confirmations, wall_ns=time.monotonic_ns() - start,
                      returncode=result.returncode)
        if result.returncode:
            report["output"] = output
        args.output.write_text(json.dumps(report, indent=2) + "\n")
        if result.returncode or len(confirmations) != len(cases):
            raise RuntimeError(output)
        print("actual elaborator construction confirmed", len(cases), "exhaustions")
    lease.close()


if __name__ == "__main__":
    main()
