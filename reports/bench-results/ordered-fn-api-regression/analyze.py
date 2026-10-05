# Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
# Released under Apache 2.0 license as described in the file LICENSE.
# Authors: Kim Morrison
"""Recompute descriptive ratios from the retained adjacent OrderedFn arms.

This reads existing observations and raw outputs; it never runs benchmarks.
By default it checks analysis.json. --write replaces that derived file.
"""
import argparse
import hashlib
import json
from pathlib import Path
import statistics


def analyze(root):
    rows = [json.loads(line) for line in (root / "observations.jsonl").read_text().splitlines()]
    schedule = json.loads((root / "schedule.json").read_text())
    expected = []
    for trial in range(schedule["trials"]):
        for workload in schedule["workloads"]:
            for parameter in workload["parameters"]:
                for arm in (["baseline", "candidate"] if trial % 2 == 0 else ["candidate", "baseline"]):
                    expected.append((trial, workload["name"], parameter, arm))
    actual = [(r["trial"], r["name"], r["param"], r["arm"]) for r in rows]
    if actual != expected:
        raise ValueError("observations do not match the complete ordered schedule")
    failures = 0
    groups = {}
    for row in rows:
        stem = f'{row["trial"]}-{row["name"].rsplit(".", 1)[-1]}-{row["param"]}-{row["arm"]}'
        raw = json.loads((root / (stem + ".stdout")).read_text())
        (root / (stem + ".stderr")).read_bytes()
        if raw != row["observation"]:
            raise ValueError(f"raw stdout differs: {stem}")
        if row["returncode"] != 0 or raw["status"] != "ok":
            failures += 1
        groups.setdefault((row["name"], row["param"], row["trial"]), {})[row["arm"]] = raw
    if failures:
        raise ValueError(f"{failures} failed arms; retain and inspect them before computing ratios")
    summary = []
    for name in sorted({row["name"] for row in rows}):
        points = []
        for parameter in sorted({row["param"] for row in rows if row["name"] == name}):
            ratios = []
            hashes_agree = True
            for trial in range(schedule["trials"]):
                arms = groups[name, parameter, trial]
                ratios.append(arms["candidate"]["per_call_nanos"] / arms["baseline"]["per_call_nanos"])
                hashes_agree &= arms["candidate"]["result_hash"] == arms["baseline"]["result_hash"]
            points.append({"param": parameter, "ratios": ratios,
                           "median_ratio": statistics.median(ratios), "hashes_agree": hashes_agree})
        summary.append({"name": name,
                        "median_ratio": statistics.median(r for p in points for r in p["ratios"]),
                        "points": points, "all_hashes_agree": all(p["hashes_agree"] for p in points)})
    return {"completed_arms": len(rows), "failed_arms": failures, "summary": summary,
            "provenance_note": "Child env.git_commit/git_dirty are invocation-working-directory metadata. Baseline source provenance comes from sources.json exact clean checkout, pinned requirements, toolchain and frozen binary hash; baseline binary reproduces retained z3-final executable hash.",
            "scope": "Descriptive adjacent baseline/candidate comparison, retaining each trial and parameter. No after-the-fact threshold, statistical equivalence claim or causal attribution to the API patch."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--write", action="store_true", help="regenerate analysis.json from retained observations")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    context = json.loads((root / "context.json").read_text())
    if hashlib.sha256((root / "measure.py").read_bytes()).hexdigest() != context["script_sha256"]:
        raise ValueError("frozen measurement script hash differs from capture context")
    result = analyze(root)
    target = root / "analysis.json"
    if args.write:
        target.write_text(json.dumps(result, indent=2) + "\n")
    elif json.loads(target.read_text()) != result:
        raise ValueError("analysis.json differs from the recomputed observations")
    print(f'Verified {result["completed_arms"]} raw arms and all descriptive ratios; no performance verdict.')


if __name__ == "__main__":
    main()
