#!/usr/bin/env python3
"""Recompute the figures and exact before/after equality in the F4 report.

Inputs are the unpacked component/combined raw capsules. This is an untimed
analysis of completed observations; it does not collect or discard samples.
"""
from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
import statistics


def load(path: Path):
    return json.loads(path.read_text())


def mean(values):
    return math.exp(statistics.mean(map(math.log, values)))


def check(condition, message):
    if not condition:
        raise ValueError(message)


def campaign(directory: Path, comparator: bool = False):
    metadata = load(directory / "metadata.json")
    recorded = load(directory / "analysis.json")
    samples = metadata["samples"]
    pairs = {}
    families = {}
    candidate = []
    for sample in samples:
        key = sample["case"], sample["block"]
        check(sample["status"] == "ok" and sample["returncode"] == 0,
              f"unsuccessful sample: {directory.name}/{key}")
        check(sample["arm"] not in pairs.setdefault(key, {}), "duplicate arm")
        pairs[key][sample["arm"]] = sample
    check(len(samples) == 56 and len(pairs) == 28, "incomplete development campaign")
    for (case, block), arms in pairs.items():
        check(set(arms) == {"A", "B"}, "incomplete pair")
        a, b = arms["A"], arms["B"]
        check(a["complete_basis_equal"] and b["complete_basis_equal"], "basis mismatch")
        check(a["family"] == b["family"], "family mismatch")
        ratio = a["wall_nanos"] / b["wall_nanos"] if comparator else b["wall_nanos"] / a["wall_nanos"]
        families.setdefault(a["family"], []).append(ratio)
        if not comparator:
            outputs = []
            times = []
            for arm in ["A", "B"]:
                raw = load(directory / f"{case}-b{block}-{arm}.stdout")
                nanos = raw.pop("candidateNanos")
                times.append(nanos)
                retained = dict(arms[arm]["statistics"])
                check(retained.pop("candidate_nanos") == nanos, "candidate time differs from metadata")
                check(raw["statistics"] == retained, "counters differ from metadata")
                check(raw["scheduling"] == arms[arm]["scheduling"], "scheduling differs from metadata")
                outputs.append(raw)
            check(outputs[0] == outputs[1], f"complete JSON mismatch: {case}/{block}")
            candidate.append(times[1] / times[0])
    ratios = [r for values in families.values() for r in values]
    computed = dict(
        samples=len(samples), pairs=len(pairs), cpu=metadata["cpu"],
        median=statistics.median(ratios), minimum=min(ratios), maximum=max(ratios),
        per_family={family: mean(values) for family, values in families.items()},
        family_balanced_geomean=mean([mean(values) for values in families.values()]),
        peak_rss_kib={arm: max(s["peak_rss_kib"] for s in samples if s["arm"] == arm) for arm in ["A", "B"]},
        total_wall_nanos={arm: sum(s["wall_nanos"] for s in samples if s["arm"] == arm) for arm in ["A", "B"]})
    for key in ["median", "minimum", "maximum", "family_balanced_geomean"]:
        check(math.isclose(computed[key], recorded[key], rel_tol=1e-12), f"recorded {key} mismatch")
    check(computed["peak_rss_kib"] == recorded["peak_rss_kib"], "RSS mismatch")
    for family, value in computed["per_family"].items():
        check(math.isclose(value, recorded["per_family"][family], rel_tol=1e-12), "family mean mismatch")
    if candidate:
        computed["candidate_geomean"] = mean(candidate)
        computed["candidate_minimum"] = min(candidate)
        computed["candidate_maximum"] = max(candidate)
        old = load(directory / "candidate-analysis.json")
        check(math.isclose(mean(candidate), old["candidate_geomean"], rel_tol=1e-12), "candidate mean mismatch")
    return computed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--combined", type=Path, required=True)
    parser.add_argument("--scan-cache", type=Path, required=True)
    parser.add_argument("--driver-output", type=Path, required=True)
    parser.add_argument("--report", type=Path, required=True)
    args = parser.parse_args()
    report = args.report.read_text()
    results = {}
    labels = [
        ("before-after-selected", "New/selected baseline"),
        ("before-after", "New/pre-selection baseline"),
        ("msolve-l2", "Hex/msolve exact 2"),
        ("msolve-l42", "Hex/msolve probabilistic 42"),
        ("gamba-avx512", "Hex/GamBa AVX-512"),
        ("gamba-avx2", "Hex/GamBa AVX2")]
    for label, title in labels:
        a = campaign(args.combined / label, comparator=label.startswith(("msolve", "gamba")))
        results[label] = a
        row = (f"| {title} | {a['family_balanced_geomean']:.4f} | {a['median']:.4f} | "
               f"{a['minimum']:.4f}–{a['maximum']:.4f} | {a['cpu']} | "
               f"{a['peak_rss_kib']['A']}/{a['peak_rss_kib']['B']} |")
        check(row in report, f"report table mismatch: {label}")
    columns = ["before-after-selected", "msolve-l2", "msolve-l42", "gamba-avx512", "gamba-avx2"]
    for family in results[columns[0]]["per_family"]:
        row = "| " + family + " | " + " | ".join(f"{results[label]['per_family'][family]:.4f}" for label in columns) + " |"
        check(row in report, f"report family table mismatch: {family}")
    for label in ["gamba-avx512", "gamba-avx2"]:
        total = results[label]["total_wall_nanos"]
        row = f"| {label} | {total['A']/1e6:.3f} | {total['B']/1e6:.3f} | {total['A']/total['B']:.4f} |"
        check(row in report, "vendor total mismatch")
    selected = results["before-after-selected"]
    check(f"{100*(1-selected['family_balanced_geomean']):.1f}% less whole-process" in report, "headline percentage mismatch")
    for label, result in [("scan-cache", args.scan_cache), ("driver-output", args.driver_output)]:
        for suffix in (["before-after", "before-after-repeat"] if label == "scan-cache" else ["before-after"]):
            results[label + "/" + suffix] = campaign(result / suffix)
    cache = [results["scan-cache/" + suffix] for suffix in ["before-after", "before-after-repeat"]]
    driver = results["driver-output/before-after"]
    for metric in ["family_balanced_geomean", "candidate_geomean"]:
        check(f"{cache[0][metric]:.4f} and {cache[1][metric]:.4f}" in report, "component ratio mismatch")
    for metric in ["family_balanced_geomean", "candidate_geomean"]:
        check(f"{driver[metric]:.4f}" in report, "driver ratio mismatch")
    check(f"{driver['peak_rss_kib']['A']}/{driver['peak_rss_kib']['B']} KiB" in report, "driver RSS mismatch")
    for key in ["candidate_geomean", "candidate_minimum", "candidate_maximum"]:
        check(f"{selected[key]:.4f}" in report, "combined candidate ratio mismatch")
    print(json.dumps(dict(scope="Recomputed report figures and all before/after JSON fields except candidateNanos, including counters and scheduling", campaigns=results), indent=2))


if __name__ == "__main__":
    main()
