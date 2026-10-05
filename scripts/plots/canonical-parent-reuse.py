#!/usr/bin/env python3
"""Plot canonical parent-isolation pairs and source-scoped external references."""
from __future__ import annotations

import argparse
import importlib.util
import json
from pathlib import Path
from statistics import median

import matplotlib
matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "canonical-parent-reuse"
import matplotlib.pyplot as plt

spec = importlib.util.spec_from_file_location("conversion_plot",
    Path(__file__).with_name("fixed-conversion-reuse.py"))
conversion_plot = importlib.util.module_from_spec(spec)
spec.loader.exec_module(conversion_plot)


def load(root, predicate=lambda arm: True):
    metadata = json.loads((root / "metadata.json").read_text())
    rows = []
    for arm in metadata["arms"]:
        if not predicate(arm):
            continue
        row, failure = conversion_plot.read_arm(root, arm)
        if failure:
            raise SystemExit(f"Invalid observation: {root / arm['output']}: {failure}")
        rows.append(row)
    return metadata, rows


def summarize(metadata, rows):
    summaries = []
    for operation, sizes in metadata["families"].items():
        for size in sizes:
            ratios = []
            for trial in range(4):
                pair = {r["arm"]: r for r in rows if r["operation"] == operation
                        and r["size"] == size and r["trial"] == trial}
                if (set(pair) != {"Before", "After"}
                        or pair["Before"]["result_hash"] != pair["After"]["result_hash"]):
                    raise SystemExit(f"Incomplete or mismatched pair: {operation}/{size}/{trial}")
                ratios.append(pair["Before"]["nanos"] / pair["After"]["nanos"])
            summaries.append(dict(operation=operation, size=size, paired_ratios=ratios,
                median_paired_ratio=median(ratios), median_ms={arm: median(
                    r["nanos"] / 1e6 for r in rows if r["operation"] == operation
                    and r["size"] == size and r["arm"] == arm)
                    for arm in ("Before", "After")}))
    return summaries


def save(fig, output, name):
    for extension in ("png", "svg", "pdf"):
        path = output / f"{name}.{extension}"
        metadata = {"Date": None} if extension == "svg" else (
            {"CreationDate": None, "ModDate": None} if extension == "pdf" else None)
        fig.savefig(path, dpi=180, metadata=metadata)
        if extension == "svg":
            path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n")
    plt.close(fig)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("input", "canonical", "reference", "output"):
        parser.add_argument(f"--{name}", type=Path, required=True)
    args = parser.parse_args()
    metadata, rows = load(args.input)
    canonical_metadata, canonical = load(args.canonical)
    reference_metadata, references = load(args.reference, lambda a:
        a["operation"] in metadata["families"] and a["arm"] != "Native" and not a["control"])
    summary = summarize(metadata, rows)
    canonical_summary = summarize(canonical_metadata, canonical)
    args.output.mkdir(parents=True, exist_ok=True)
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    for ax, (operation, sizes) in zip(axes, metadata["families"].items()):
        for arm, data, color, style in [("Before", rows, "#1f77b4", "--o"),
                ("After", rows, "#9467bd", "-o"), ("Flint", references, "#ff7f0e", ":o"),
                ("Z3", references, "#2ca02c", ":o")]:
            xs, ys, lo, hi = [], [], [], []
            for size in sizes:
                values = [r["nanos"] / 1e6 for r in data if r["operation"] == operation
                          and r["size"] == size and r["arm"] == arm]
                if values:
                    xs.append(size); ys.append(median(values)); lo.append(min(values)); hi.append(max(values))
                    ax.scatter([size] * len(values), values, color=color, alpha=.3, s=15)
            ax.plot(xs, ys, style, color=color,
                    label=arm + (" retained reference" if arm in ("Flint", "Z3") else " native"))
            ax.fill_between(xs, lo, hi, color=color, alpha=.1)
        ax.set_title(operation); ax.set_xscale("log", base=2); ax.set_yscale("log")
        ax.set_xticks(sizes, sizes); ax.set_xlabel("Operand algebraic degree")
        ax.set_ylabel("Operation + exact result guard (ms)"); ax.grid(alpha=.2); ax.legend(fontsize=8)
    fig.suptitle("Reusing canonical parent isolation in arithmetic")
    fig.text(.01, .01, "Four adjacent AB/BA pairs per rung; all completed observations retained; operand preparation and separate warmup excluded.\n"
        "External curves reuse an earlier capture: exact annihilation/sign arithmetic, JSON and cleanup differ from the native canonical guard.\n"
        "These are host-specific API-route observations, with no fitted complexity model or portable budget.", fontsize=8)
    fig.tight_layout(rect=(0, .15, 1, .95))
    save(fig, args.output, "scalar-comparison")
    fig, axes = plt.subplots(1, 3, figsize=(12, 4))
    labels = {"CanonicalAdd": "Canonical sum, output degree 4",
              "CanonicalMul": "Canonical product, output degree 2",
              "CommonPowers": "Common powers, exponent limit 16"}
    for ax, operation in zip(axes, canonical_metadata["families"]):
        for i, arm in enumerate(("Before", "After")):
            values = [r["nanos"] / 1e6 for r in canonical
                      if r["operation"] == operation and r["arm"] == arm]
            ax.scatter([i] * len(values), values, color="#1f77b4" if i == 0 else "#9467bd")
            ax.plot([i - .2, i + .2], [median(values)] * 2, color="black")
        ax.set_xticks([0, 1], ["Before", "After"]); ax.set_xlim(-.5, 1.5)
        ax.set_title(labels[operation], fontsize=10); ax.set_ylabel("Operation + result guard (ms)")
        ax.grid(alpha=.2)
    fig.text(.01, .01, "Four adjacent AB/BA pairs for each fixed case. Distinct input meanings; these panels make no scaling claim.", fontsize=8)
    fig.tight_layout(rect=(0, .08, 1, 1))
    save(fig, args.output, "canonical-cases")
    (args.output / "analysis.json").write_text(json.dumps(dict(rows=rows, references=references,
        canonical_rows=canonical, summary=summary, canonical_summary=canonical_summary,
        reference_source=reference_metadata["source"]), indent=2) + "\n")
    print(json.dumps(summary + canonical_summary, indent=2))


if __name__ == "__main__":
    main()
