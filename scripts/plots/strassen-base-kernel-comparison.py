#!/usr/bin/env python3
"""Plot the periodic Barrett Strassen base-kernel comparison.

Reads ``reports/bench-results/strassen-base-kernel-comparison.json`` (emitted by
``lake exe hexstrassen_compare``) and writes
``reports/figures/strassen-base-kernel-comparison.svg``. The left panel reports
the direct leaf-kernel comparison, including the cases that cross several
reduction windows. The right panel reports full ``mulStrassen`` with each
configuration at its shipped cutoff.

Run: ``python3 scripts/plots/strassen-base-kernel-comparison.py``
"""

from __future__ import annotations

import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "strassen-base-kernel-comparison"
import matplotlib.pyplot as plt

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "reports" / "bench-results" / "strassen-base-kernel-comparison.json"
FIGURES = ROOT / "reports" / "figures"
OUTPUT = FIGURES / "strassen-base-kernel-comparison.svg"


def shape_label(row: dict[str, object], *, reductions: bool) -> str:
    label = f"{row['n']}×{row['m']}×{row['k']}"
    if reductions:
        label += f"\nflushes={row['midstream_reductions']}"
    return label


def main() -> None:
    record = json.loads(DATA.read_text(encoding="utf-8"))
    if record.get("schema_version") != 2:
        raise ValueError("expected comparison schema_version 2")

    results = record["results"]
    moduli = list(dict.fromkeys(row["modulus"] for row in results))
    colors = {"tiny": "#1f77b4", "small": "#2ca02c", "upper": "#d62728"}

    fig, (leaf_ax, full_ax) = plt.subplots(1, 2, figsize=(11.5, 4.5))

    leaf_ratios: list[float] = []
    full_ratios: list[float] = []
    matched_ratios: list[float] = []

    for modulus in moduli:
        leaf = [r for r in results if r["kind"] == "leaf" and r["modulus"] == modulus]
        full = [r for r in results if r["kind"] == "full" and r["modulus"] == modulus]
        prime = leaf[0]["prime"]
        label = f"p={prime}"
        color = colors.get(modulus)

        lr = [r["default_ns"] / r["periodic_ns"] for r in leaf]
        fr = [r["default_ns"] / r["periodic_ns"] for r in full]
        leaf_ratios.extend(lr)
        full_ratios.extend(fr)
        matched_ratios.extend(
            r["default_ns"] / r["periodic_at_default_cutoff_ns"] for r in full
        )
        matched_ratios.extend(
            r["default_at_periodic_cutoff_ns"] / r["periodic_ns"] for r in full
        )

        leaf_ax.plot(range(len(leaf)), lr, marker="o", color=color, label=label)
        full_ax.plot(range(len(full)), fr, marker="s", color=color, label=label)

    first_leaf = [r for r in results if r["kind"] == "leaf" and r["modulus"] == moduli[0]]
    first_full = [r for r in results if r["kind"] == "full" and r["modulus"] == moduli[0]]
    leaf_ax.set_xticks(
        range(len(first_leaf)),
        [shape_label(r, reductions=True) for r in first_leaf],
        fontsize=8,
    )
    full_ax.set_xticks(
        range(len(first_full)),
        [shape_label(r, reductions=False) for r in first_full],
        fontsize=8,
    )

    for ax in (leaf_ax, full_ax):
        ax.axhline(1.0, color="#555555", linewidth=0.8, linestyle="--")
        ax.axhline(1.05, color="#888888", linewidth=0.7, linestyle=":")
        ax.set_ylabel("default / periodic  (>1 = periodic faster)")
        ax.set_xlabel("matrix shape n×m×k")
        ax.grid(True, linewidth=0.3, alpha=0.5)
        ax.legend(fontsize=8)

    leaf_ax.set_title("Direct baseMul leaf kernel", fontsize=11)
    full_ax.set_title("Full mulStrassen (shipped cutoffs)", fontsize=11)

    hi = max(leaf_ratios + full_ratios) * 1.08
    leaf_ax.set_ylim(0.95, hi)
    full_ax.set_ylim(0.95, hi)

    subtitle = (
        f"window={record['window_terms']} terms; leaf {min(leaf_ratios):.2f}–"
        f"{max(leaf_ratios):.2f}×, full {min(full_ratios):.2f}–"
        f"{max(full_ratios):.2f}×; matched-cutoff controls "
        f"{min(matched_ratios):.2f}–{max(matched_ratios):.2f}×. "
        "Dotted line is the 5% gate."
    )
    fig.text(0.5, 0.005, subtitle, ha="center", fontsize=8, color="#555555")
    fig.tight_layout(rect=(0, 0.06, 1, 1))

    OUTPUT.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(OUTPUT, format="svg", metadata={"Date": None})
    plt.close(fig)
    svg = OUTPUT.read_text(encoding="utf-8")
    OUTPUT.write_text(
        "\n".join(line.rstrip() for line in svg.splitlines()) + "\n",
        encoding="utf-8",
    )
    print(f"wrote {OUTPUT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
