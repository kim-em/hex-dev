#!/usr/bin/env python3
"""Plot paired real-root API observations and retained external references."""
from pathlib import Path
import argparse
import importlib.util
import json
from statistics import median

import matplotlib
matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "real-root-isolation-reuse"
import matplotlib.pyplot as plt


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--after-label", default="Hex with reuse")
    args = parser.parse_args()
    spec = importlib.util.spec_from_file_location("pair_plot",
        Path(__file__).with_name("fixed-conversion-reuse.py"))
    helper = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(helper)
    meta = json.loads((args.input / "metadata.json").read_text())
    trials = meta.get("trials", list(range(4)))
    if set(meta["families"]) != {"RationalRoots", "QuadraticRoots"}:
        raise SystemExit("This plot requires the two polynomial-root degree families")
    rows, refs, summaries = [], [], []
    for arm in meta["arms"]:
        row, failure = helper.read_arm(args.input, arm)
        if failure:
            raise SystemExit(f"Invalid native observation: {failure}")
        result = json.loads((args.input / arm["output"]).read_text())["results"][0]
        row["whole_child_peak_rss_kb"] = max(p["peak_rss_kb"] for p in result["points"])
        rows.append(row)
    reference = json.loads((args.reference / "metadata.json").read_text())
    for arm in reference["arms"]:
        if arm["backend"] == "Native" or arm["protocol"]:
            continue
        row, failure = helper.read_arm(args.reference, arm)
        if failure:
            raise SystemExit(f"Invalid external reference: {failure}")
        refs.append({**row, "operation": arm["family"] + "Roots",
                     "size": arm["degree"], "arm": arm["backend"]})
    if len(rows) != 2 * len(trials) * sum(map(len, meta["families"].values())) or len(refs) != 48:
        raise SystemExit("Incomplete retained schedule")
    for ref in refs:
        native_hashes = {r["result_hash"] for r in rows
                         if r["operation"] == ref["operation"] and r["size"] == ref["size"]}
        if native_hashes != {ref["result_hash"]}:
            raise SystemExit(f"External fingerprint mismatch: {ref['operation']}/{ref['size']}")
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    assert len(axes) == len(meta["families"])
    for ax, (operation, sizes) in zip(axes, meta["families"].items()):
        for size in sizes:
            ratios = []
            for trial in trials:
                pair = {r["arm"]: r for r in rows if r["operation"] == operation
                        and r["size"] == size and r["trial"] == trial}
                if set(pair) != {"Before", "After"} or (
                        pair["Before"]["result_hash"] != pair["After"]["result_hash"]):
                    raise SystemExit(f"Incomplete or mismatched pair: {operation}/{size}/{trial}")
                ratios.append(pair["Before"]["nanos"] / pair["After"]["nanos"])
            summaries.append({"operation": operation, "size": size,
                "paired_ratios": ratios, "median_paired_ratio": median(ratios),
                "paired_ratio_min_max": [min(ratios), max(ratios)],
                "median_ms": {arm: median(r["nanos"] / 1e6 for r in rows
                    if r["operation"] == operation and r["size"] == size and r["arm"] == arm)
                    for arm in ("Before", "After")},
                "median_whole_child_peak_rss_mib": {arm: median(r["whole_child_peak_rss_kb"] / 1024
                    for r in rows if r["operation"] == operation and r["size"] == size
                    and r["arm"] == arm) for arm in ("Before", "After")}})
        for arm, data, label, color in [
                ("Before", rows, "Hex before", "#1f77b4"),
                ("After", rows, args.after_label, "#d62728"),
                ("Flint", refs, "FLINT (retained reference)", "#2ca02c"),
                ("Z3", refs, "Z3 RCF (retained reference)", "#9467bd")]:
            points = [r for r in data if r["operation"] == operation and r["arm"] == arm]
            medians, lows, highs = [], [], []
            for size in sizes:
                values = [r["nanos"] / 1e6 for r in points if r["size"] == size]
                if len(values) != (len(trials) if arm in ("Before", "After") else 4):
                    raise SystemExit(f"Incomplete curve: {operation}/{size}/{arm}")
                medians.append(median(values)); lows.append(min(values)); highs.append(max(values))
                ax.scatter([size] * len(values), values, s=15, color=color, alpha=.5)
            ax.plot(sizes, medians, "o-", color=color, label=label)
            ax.fill_between(sizes, lows, highs, color=color, alpha=.12)
        ax.set_xscale("log", base=2); ax.set_yscale("log")
        ax.set_xticks(sizes, labels=[str(n) for n in sizes])
        ax.set_xlabel("Input polynomial degree")
        ax.set_ylabel("Elapsed time per call (ms)")
        ax.set_title("$X^n-2$" if operation == "RationalRoots" else "$X^n-\\sqrt{2}$")
        ax.grid(alpha=.2, which="both"); ax.legend(fontsize=8)
    fig.suptitle("Actual real-root enumeration: all observations, medians and min–max ranges")
    fig.tight_layout()
    args.output.mkdir(parents=True, exist_ok=True)
    for extension in ("png", "svg", "pdf"):
        metadata = {"Date": None} if extension == "svg" else (
            {"CreationDate": None, "ModDate": None} if extension == "pdf" else None)
        fig.savefig(args.output / f"roots-comparison.{extension}", dpi=180, metadata=metadata)
    plt.close(fig)
    (args.output / "analysis.json").write_text(json.dumps({
        "native_source": str(args.input), "external_reference": str(args.reference),
        "native_rows": rows, "external_rows": refs, "summaries": summaries,
        "limits": "Four adjacent pairs per size, no fitted law. External arms are historical, "
                  "not contemporaneous pairs; external annihilation and protocol are included."
    }, indent=2) + "\n")
    print(json.dumps(summaries, indent=2))


if __name__ == "__main__":
    main()
