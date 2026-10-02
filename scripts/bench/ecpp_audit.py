#!/usr/bin/env python3
"""Retain ECPP scientific runs and adjacent AB/BA regression comparisons."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import statistics
import subprocess

from cpu_lease import cpu_lease

ROOT = Path(__file__).resolve().parents[2]
BENCH = ROOT / ".lake/build/bin/hexecpp_bench"
FAMILIES = ["Hex.ECPPBench.runReplay", "Hex.ECPPBench.runProposal",
            "Hex.ECPPBench.runParse", "Hex.ECPPBench.runPreflight"]
# Operation-specific ceilings: twice the retained endpoint medians, rounded
# upward. Existing reports/ecpp/{compiled,native/compiled-updated}.json supply
# the baselines; these are per-call regression budgets, not subprocess caps.
BUDGETS = {"runCheck65": .00032, "runCheck256": .012, "runCheck512": .045,
           "runConvert65": .0016, "runConvert256": .17, "runConvert512": 1.05,
           "runNative128": .125, "runNative256": 1.45,
           "runNativeCheck": .010, "runNativeConvert": .14}


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", required=True, type=Path)
    parser.add_argument("--baseline", type=Path, help="compiled reference bench for AB/BA")
    parser.add_argument("--trials", type=int, default=5)
    args = parser.parse_args()
    if args.output.exists():
        parser.error("output exists; preserve completed runs")
    cpu, lease = cpu_lease()
    sources = ["lean-toolchain", "lake-manifest.json", "bench/HexECPP/Bench.lean",
               "scripts/bench/ecpp_audit.py", *[str(p) for p in sorted(Path("HexECPP").glob("*.lean"))]]
    report = dict(cpu=cpu, host=os.uname().nodename, platform=platform.platform(),
                  source=subprocess.check_output(["git", "rev-parse", "HEAD"], text=True).strip(),
                  source_hashes={p: sha(ROOT / p) for p in sources}, executable_sha256=sha(BENCH),
                  lean=subprocess.check_output(["lake", "--version"], text=True).strip(),
                  host_before=dict(loadavg=list(os.getloadavg())), commands=[],
                  budgets_seconds=BUDGETS, samples=[])
    directory = args.output.with_suffix(".artifacts")
    directory.mkdir(parents=True, exist_ok=False)

    def save() -> None:
        args.output.write_text(json.dumps(report, indent=2) + "\n")

    def run(command: list[str], cwd: Path = ROOT) -> str:
        print(" ".join(command), flush=True)
        result = subprocess.run(["taskset", "-c", str(cpu), *command], cwd=cwd,
                                capture_output=True, text=True)
        row = dict(command=command, cwd=str(cwd), returncode=result.returncode,
                   stdout=result.stdout, stderr=result.stderr, loadavg=list(os.getloadavg()))
        report["commands"].append(row)
        save()
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        return result.stdout

    try:
        if args.baseline:
            baseline = args.baseline.resolve()
            report["baseline_executable_sha256"] = sha(baseline)
            report["baseline_source"] = subprocess.check_output(
                ["git", "rev-parse", "HEAD"], cwd=baseline.parents[3], text=True).strip()
            # Trial-major, adjacent arms, alternating AB/BA across trials.
            for trial in range(args.trials):
                arms = [("A", baseline), ("B", BENCH)]
                if trial % 2:
                    arms.reverse()
                for name in BUDGETS:
                    for arm, exe in arms:
                        output = run([str(exe), "_child", "--bench", name, "--fixed",
                                      "--repeat-index", str(trial), "--min-total-nanos", "10000000"],
                                     cwd=exe.parents[3])
                        data = json.loads(output)
                        report["samples"].append(dict(trial=trial, arm=arm, target=name, data=data))
                        save()
            ratios = {}
            for name in BUDGETS:
                pairs = []
                for trial in range(args.trials):
                    values = {}
                    for sample in report["samples"]:
                        if sample["target"] == name and sample["trial"] == trial:
                            data = sample["data"]
                            if data["status"] != "ok" or data["result_hash"] != "0x1":
                                raise RuntimeError(f"invalid regression result: {sample}")
                            values[sample["arm"]] = data["total_nanos"] / data["inner_repeats"]
                    pairs.append(values["B"] / values["A"])
                ratios[name] = dict(paired_ratios=pairs, median=statistics.median(pairs))
            report["regression_ratios"] = ratios
        else:
            for name in FAMILIES:
                destination = directory / (name.rsplit(".", 1)[-1] + ".json")
                run([str(BENCH), "run", name, "--export-file", str(destination)])
            destination = directory / "endpoints.json"
            run([str(BENCH), "run", *BUDGETS, "--repeats", str(args.trials),
                 "--export-file", str(destination)])
            results = json.loads(destination.read_text())["results"]
            report["fixed_verdicts"] = {
                r["function"]: dict(median_seconds=r["median_nanos"] / 1e9,
                                    budget_seconds=BUDGETS[r["function"]],
                                    within_budget=r["median_nanos"] / 1e9 <= BUDGETS[r["function"]],
                                    hashes_agree=r["hashes_agree"],
                                    expected_hash_check=r["expected_hash_check"])
                for r in results}
        report["host_after"] = dict(loadavg=list(os.getloadavg()))
        report["artifact_sha256"] = {p.name: sha(p) for p in directory.iterdir() if p.is_file()}
        save()
    finally:
        lease.close()


if __name__ == "__main__":
    main()
