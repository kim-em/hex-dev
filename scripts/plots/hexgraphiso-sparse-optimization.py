#!/usr/bin/env python3
"""Plot all paired sparse before/after measurements, without selecting samples."""
import argparse
import json
from pathlib import Path
import statistics


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--data", type=Path, required=True)
    p.add_argument("--out", type=Path, default=Path("reports/figures/hexgraphiso-sparse-optimization"))
    p.add_argument("--before-label", default="Initial sparse executable")
    p.add_argument("--after-label", default="After performance changes")
    args = p.parse_args()
    rows = [json.loads(line) for line in args.data.read_text().splitlines()]
    context = next(r for r in rows if r["kind"] == "context")
    names = list(dict.fromkeys(r["name"] for r in rows if r["kind"] == "sample"))
    samples = {(r["name"], r["block"], r["arm"]): r["result"]["ns_per_iteration"]
               for r in rows if r["kind"] == "sample"}
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    fig, ax = plt.subplots(figsize=(9, max(5.2, 1.2 + 0.55 * len(names))))
    labels = []
    for i, name in enumerate(names):
        a = [samples[name, block, "A"] / 1e6 for block in range(context["blocks"])]
        b = [samples[name, block, "B"] / 1e6 for block in range(context["blocks"])]
        ratio = statistics.median(y / x for x, y in zip(a, b))
        labels.append(f"{name}  ({1 / ratio:.2f}× faster)")
        for offset, values, color, label in [(-0.17, a, "#4c78a8", args.before_label),
                                             (0.17, b, "#d45087", args.after_label)]:
            ax.barh(i + offset, statistics.median(values), height=0.29, color=color,
                    alpha=0.85, label=label if i == 0 else None)
            ax.scatter(values, [i + offset] * len(values), color="black", s=9, zorder=3)
    ax.set_yticks(range(len(names)), labels)
    ax.invert_yaxis()
    ax.set_xscale("log")
    ax.set_xlabel("Complete sparse canonical result, milliseconds per call (log scale)")
    ax.set_title("Sparse nauty port: measured implementation improvements", pad=32)
    ax.grid(axis="x", alpha=0.2)
    ax.legend(loc="lower left", bbox_to_anchor=(0, 1.005), ncol=2, fontsize=8)
    fig.text(0.5, 0.015,
             f"{context['blocks']} adjacent AB/BA blocks; fixed iterations; every block shown as a dot; "
             f"{context['host']}, CPU {context['cpu']}.\n"
             "Bars show medians; speedups use paired ratios. Exact C conformance passes; sparse search proofs pending.",
             ha="center", fontsize=8)
    fig.tight_layout(rect=(0, 0.075, 1, 1))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    for suffix in [".svg", ".png"]:
        path = args.out.with_suffix(suffix)
        fig.savefig(path, dpi=160)
        if suffix == ".svg":
            path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n")
        print(path)


if __name__ == "__main__":
    main()
