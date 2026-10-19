#!/usr/bin/env python3
"""Plot retained fixed-conversion pairs with historical external references."""
from __future__ import annotations

import argparse
import json
from pathlib import Path
from statistics import median

import matplotlib
matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "fixed-conversion-reuse"
import matplotlib.pyplot as plt


def read_arm(root, arm):
    path = root / arm["output"]
    result = json.loads(path.read_text())["results"][0] if path.exists() else None
    if arm["exit_code"] or not result:
        return None, {"arm": arm, "result": result, "reason": "failed execution or missing export"}
    points = result["points"]
    if (not points or any(p["status"] != "ok" for p in points)
            or not result.get("hashes_agree")
            or result.get("expected_hash_check", {}).get("status") != "match"
            or result.get("budget_truncated")):
        return None, {"arm": arm, "result": result, "reason": "failed, truncated or mismatched result"}
    return {**arm, "nanos": median(p["total_nanos"] / p["inner_repeats"] for p in points),
            "result_hash": result["observed_hash"]}, None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", type=Path, required=True)
    parser.add_argument("--reference", type=Path, required=True)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--direct", type=Path,
                        help="Optional fixed conversion anchor capture")
    args = parser.parse_args()
    metadata = json.loads((args.input / "metadata.json").read_text())
    reference = json.loads((args.reference / "metadata.json").read_text())
    rows, failures, references = [], [], []
    for arm in metadata["arms"]:
        row, failure = read_arm(args.input, arm)
        if failure:
            failures.append(failure)
        else:
            rows.append(row)
    for arm in reference["arms"]:
        if arm["operation"] not in metadata["families"] or arm["arm"] == "Native" or arm["control"]:
            continue
        row, failure = read_arm(args.reference, arm)
        if failure:
            failures.append(failure)
        else:
            references.append(row)
    summaries = []
    fig, axes = plt.subplots(1, 3 if args.direct else 2,
                             figsize=(16 if args.direct else 12, 5))
    for ax, (operation, sizes) in zip(axes, metadata["families"].items()):
        for size in sizes:
            pairs = []
            for trial in range(4):
                pair = {r["arm"]: r for r in rows
                        if r["operation"] == operation and r["size"] == size and r["trial"] == trial}
                if len(pair) != 2:
                    failures.append({"operation": operation, "size": size, "trial": trial,
                                     "reason": "incomplete pair"})
                    continue
                if pair["Before"]["result_hash"] != pair["After"]["result_hash"]:
                    failures.append({"operation": operation, "size": size, "trial": trial,
                                     "reason": "pair hash mismatch", "pair": pair})
                    continue
                pairs.append(pair["Before"]["nanos"] / pair["After"]["nanos"])
            summaries.append({"operation": operation, "size": size, "paired_ratios": pairs,
                              "median_paired_ratio": median(pairs) if pairs else None,
                              "median_ms": {arm: median(r["nanos"] / 1e6 for r in rows
                                  if r["operation"] == operation and r["size"] == size and r["arm"] == arm)
                                  for arm in ("Before", "After") if any(r["operation"] == operation
                                      and r["size"] == size and r["arm"] == arm for r in rows)}})
        for arm, data, color, style in [("Before", rows, "#1f77b4", "--o"),
                                       ("After", rows, "#9467bd", "-o"),
                                       ("Flint", references, "#ff7f0e", ":o"),
                                       ("Z3", references, "#2ca02c", ":o")]:
            xs, ys, lo, hi = [], [], [], []
            for size in sizes:
                values = [r["nanos"] / 1e6 for r in data
                          if r["operation"] == operation and r["size"] == size and r["arm"] == arm]
                if values:
                    xs.append(size); ys.append(median(values)); lo.append(min(values)); hi.append(max(values))
                    ax.scatter([size] * len(values), values, color=color, alpha=.25, s=14)
            label = arm + (" retained reference" if arm in ("Flint", "Z3") else " native")
            ax.plot(xs, ys, style, color=color, label=label)
            ax.fill_between(xs, lo, hi, color=color, alpha=.1)
        ax.set_title("Add (unchanged control)" if operation == "Add" else operation)
        ax.set_xscale("log", base=2); ax.set_yscale("log")
        ax.set_xticks(sizes, sizes); ax.set_xlabel("Operand algebraic degree")
        ax.set_ylabel("Operation + exact result guard (ms)"); ax.grid(alpha=.2); ax.legend(fontsize=8)
    direct = None
    if args.direct:
        direct_metadata = json.loads((args.direct / "metadata.json").read_text())
        direct_rows = []
        for arm in direct_metadata["arms"]:
            row, failure = read_arm(args.direct, arm)
            if failure:
                failures.append(failure)
            else:
                direct_rows.append(row)
        ratios = []
        for trial in range(4):
            pair = {r["arm"]: r for r in direct_rows if r["trial"] == trial}
            if len(pair) != 2 or pair["Before"]["result_hash"] != pair["After"]["result_hash"]:
                failures.append({"trial": trial, "reason": "incomplete or mismatched direct pair"})
            else:
                ratios.append(pair["Before"]["nanos"] / pair["After"]["nanos"])
        medians = {}
        for i, arm in enumerate(("Before", "After")):
            values = [r["nanos"] / 1e6 for r in direct_rows if r["arm"] == arm]
            if values:
                medians[arm] = median(values)
                axes[2].scatter([i] * len(values), values, alpha=.6,
                                color="#1f77b4" if arm == "Before" else "#9467bd")
                axes[2].plot([i - .2, i + .2], [median(values)] * 2, color="black")
        axes[2].set_xticks([0, 1], ["Before", "After"])
        axes[2].set_xlim(-.5, 1.5); axes[2].set_ylabel("Fixed conversion + result guard (ms)")
        axes[2].set_title("Direct conversion, degree 2"); axes[2].grid(alpha=.2)
        direct = {"rows": direct_rows, "paired_ratios": ratios,
                  "median_paired_ratio": median(ratios) if ratios else None,
                  "median_ms": medians}
    fig.suptitle("Reusing certified isolation in fixed-presentation conversion")
    footer = ("Four adjacent AB/BA pairs per rung; every completed sample retained. Prepared operands and separate warmup excluded.\n"
              "Native checks canonical polynomial/sign; external references include annihilation/sign arithmetic, JSON and cleanup.\n"
              "External curves reuse the retained scalar capture; they are not contemporaneous paired arms. No fitted model or admission claim.")
    fig.text(.01, .01, footer, fontsize=8, va="bottom")
    fig.tight_layout(rect=(0, .16, 1, .95))
    args.output.mkdir(parents=True, exist_ok=True)
    for extension in ("pdf", "png", "svg"):
        path = args.output / f"fixed-conversion-comparison.{extension}"
        fig.savefig(path, dpi=180)
        if extension == "svg":
            path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n")
    (args.output / "analysis.json").write_text(json.dumps({"rows": rows, "references": references,
        "failures": failures, "summary": summaries, "direct": direct,
        "reference_source": reference["source"]}, indent=2) + "\n")
    print(json.dumps(summaries, indent=2))
    if failures:
        raise SystemExit(f"{len(failures)} unsuccessful or incomplete observations retained in analysis.json")


if __name__ == "__main__":
    main()
