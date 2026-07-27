#!/usr/bin/env python3
"""Plot the periodic Barrett Strassen base-kernel comparison.

Reads ``reports/bench-results/strassen-base-kernel-comparison.json`` (emitted by
``lake exe hexstrassen_compare``) and writes
``reports/figures/strassen-base-kernel-comparison.svg``. Absolute wall times and
speedups are shown separately for direct leaves and full ``mulStrassen``.

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
OUTPUT = ROOT / "reports" / "figures" / "strassen-base-kernel-comparison.svg"


def shape_label(row: dict[str, object], *, flushes: bool) -> str:
    label = f"{row['n']}×{row['m']}×{row['k']}"
    if flushes:
        label += f"\nflushes={row['window_flushes']}"
    return label


def main() -> None:
    record = json.loads(DATA.read_text(encoding="utf-8"))
    if record.get("schema_version") != 3:
        raise ValueError("expected comparison schema_version 3")

    results = record["results"]
    moduli = list(dict.fromkeys(r["modulus"] for r in results if r["kind"] == "leaf"))
    colors = {"tiny": "#1f77b4", "small": "#2ca02c", "upper": "#d62728"}
    fig, axes = plt.subplots(2, 2, figsize=(12.0, 8.0), sharex="col")
    leaf_time, full_time = axes[0]
    leaf_ratio, full_ratio = axes[1]

    leaf_ratios: list[float] = []
    full_ratios: list[float] = []
    matched_ratios: list[float] = []

    for modulus in moduli:
        leaf = [r for r in results if r["kind"] == "leaf" and r["modulus"] == modulus]
        full = [r for r in results if r["kind"] == "full" and r["modulus"] == modulus]
        prime = leaf[0]["prime"]
        color = colors[modulus]
        x_leaf = range(len(leaf))
        x_full = range(len(full))

        leaf_time.plot(x_leaf, [r["default_ns"] / 1e6 for r in leaf], color=color,
                       marker="o", label=f"default, p={prime}")
        leaf_time.plot(x_leaf, [r["periodic_ns"] / 1e6 for r in leaf], color=color,
                       marker="s", linestyle="--", label=f"periodic, p={prime}")
        full_time.plot(x_full, [r["default_ns"] / 1e6 for r in full], color=color,
                       marker="o", label=f"default, p={prime}")
        full_time.plot(x_full, [r["periodic_ns"] / 1e6 for r in full], color=color,
                       marker="s", linestyle="--", label=f"periodic, p={prime}")

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
        leaf_ratio.plot(x_leaf, lr, color=color, marker="o", label=f"p={prime}")
        full_ratio.plot(x_full, fr, color=color, marker="s", label=f"p={prime}")

    first_leaf = [r for r in results if r["kind"] == "leaf" and r["modulus"] == moduli[0]]
    first_full = [r for r in results if r["kind"] == "full" and r["modulus"] == moduli[0]]
    leaf_ratio.set_xticks(
        range(len(first_leaf)), [shape_label(r, flushes=True) for r in first_leaf], fontsize=8
    )
    full_ratio.set_xticks(
        range(len(first_full)), [shape_label(r, flushes=False) for r in first_full], fontsize=8
    )

    leaf_time.set_title("Direct baseMul leaf: absolute time", fontsize=11)
    full_time.set_title(
        f"Full mulStrassen: absolute time (cutoffs {record['default_cutoff']}/{record['periodic_cutoff']})",
        fontsize=11,
    )
    for ax in (leaf_time, full_time):
        ax.set_yscale("log")
        ax.set_ylabel("best wall time (ms, log)")
        ax.grid(True, which="both", linewidth=0.3, alpha=0.5)
        ax.legend(fontsize=7, ncol=2)

    for ax, title in ((leaf_ratio, "Direct leaf speedup"), (full_ratio, "Full shipped-config speedup")):
        ax.axhline(1.0, color="#555555", linewidth=0.8, linestyle="--")
        ax.axhline(1.05, color="#888888", linewidth=0.7, linestyle=":")
        ax.set_ylabel("default / periodic")
        ax.set_xlabel("matrix shape n×m×k")
        ax.set_title(title, fontsize=11)
        ax.grid(True, linewidth=0.3, alpha=0.5)
        ax.legend(fontsize=8)

    window_rows = [r for r in results if r["kind"] == "window"]
    window_tax: list[float] = []
    for shape in {(r["n"], r["m"], r["k"]) for r in window_rows}:
        rows = [r for r in window_rows if (r["n"], r["m"], r["k"]) == shape]
        selected = next(r for r in rows if r["window_terms"] == record["window_terms"])
        single = max(rows, key=lambda r: r["window_terms"])
        window_tax.append(selected["wall_ns"] / single["wall_ns"] - 1.0)

    subtitle = (
        f"window={record['window_terms']} terms; leaf {min(leaf_ratios):.2f}–"
        f"{max(leaf_ratios):.2f}×, full {min(full_ratios):.2f}–"
        f"{max(full_ratios):.2f}×; matched cutoffs {min(matched_ratios):.2f}–"
        f"{max(matched_ratios):.2f}×. Window tax vs effectively single flush: "
        f"{min(window_tax) * 100:.1f}–{max(window_tax) * 100:.1f}%."
    )
    fig.text(0.5, 0.005, subtitle, ha="center", fontsize=8, color="#555555")
    fig.tight_layout(rect=(0, 0.045, 1, 1))

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
