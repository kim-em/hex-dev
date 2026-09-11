#!/usr/bin/env python3
"""Plot the committed carrier comparator medians, with separate sweep axes."""
import argparse
import json
from pathlib import Path

import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "reports/hex-char-poly-carriers/measurements.json"
FAMILIES = {
    "dense-polynomial-charpoly": (["DenseInt", "DenseRat", "DenseMod"], 1, "Entry degree"),
    "multivariate-charpoly": (["MvInt", "MvRat"], 2, "Entry term count"),
    "rational-function-charpoly": (["RatFn"], 1, "Numerator/denominator degree"),
}


def plot_family(family):
    data = json.loads(DATA.read_text())
    carriers, fixed_parameter, parameter_label = FAMILIES[family]
    matplotlib.rcParams.update({"svg.hashsalt": "hex-char-poly", "svg.fonttype": "none"})
    figure, axes = plt.subplots(1, 2, figsize=(10, 4), layout="constrained")
    for color_index, carrier in enumerate(carriers):
        for external in (False, True):
            rows = []
            prefix = "Sympy" if external else ""
            for key, run in data.items():
                if not key.startswith(carrier + "-"):
                    continue
                n, k = map(int, key.split("-n")[1].split("k"))
                name = f"Hex.CharPolyBench.{prefix}{carrier}.n{n}k{k}"
                result = next(r for r in run["results"] if r["function"] == name)
                rows.append((n, k, result["median_nanos"] / 1000))
            for axis_index, axis in enumerate(axes):
                points = sorted((n if axis_index == 0 else k, time)
                                for n, k, time in rows
                                if (k == fixed_parameter if axis_index == 0 else n == 3))
                axis.plot([p[0] for p in points], [p[1] for p in points],
                          color=f"C{color_index}", linestyle="--" if external else "-",
                          marker="o", markersize=4,
                          label=f"{'SymPy' if external else 'Hex'} {carrier}")
    for axis in axes:
        axis.set_yscale("log")
        axis.set_ylabel("Median microseconds / call (log scale)")
        axis.grid(True, which="both", alpha=0.2)
    axes[0].set_xlabel("Matrix dimension")
    axes[0].set_title(f"Fixed entry parameter = {fixed_parameter}")
    axes[0].set_xticks([2, 3, 4])
    axes[1].set_xlabel(parameter_label)
    axes[1].set_title("Fixed matrix dimension = 3")
    axes[1].set_xticks([2, 4, 6] if family == "multivariate-charpoly" else [1, 2, 3])
    figure.legend(*axes[0].get_legend_handles_labels(), loc="outside lower center",
                  ncols=3, fontsize=8)
    figure.suptitle(f"{family}: Hex (with peak observation) and SymPy Bareiss", fontsize=11)
    return figure


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=FAMILIES, required=True)
    args = parser.parse_args()
    figure = plot_family(args.family)
    output = ROOT / f"reports/figures/hex-char-poly-comparator-{args.family}.svg"
    output.parent.mkdir(exist_ok=True)
    figure.savefig(output, metadata={"Date": None})
    output.write_text("\n".join(line.rstrip() for line in output.read_text().splitlines()) + "\n")
    plt.close(figure)
    print(output.relative_to(ROOT))


if __name__ == "__main__":
    main()
