#!/usr/bin/env python3
"""Comparison plot: default-base vs delayed-reduction-base ``mulStrassen``.

Reads the committed local measurement
``reports/bench-results/strassen-base-kernel-comparison.json`` (emitted by the
``hexstrassen_compare`` driver, ``bench/HexStrassen/Compare.lean``) and writes
``reports/figures/strassen-base-kernel-comparison.svg``.

The two series are the same recursive ``mulStrassen`` differing only in the
pluggable base kernel on the prime field ``ZMod64 p``: ``strassenDefault`` (naive
``mulImpl``, one Barrett reduction per multiply-add) versus ``strassenBarrett``
(the delayed-reduction two-word accumulator, reducing once per window). A base
kernel fires only below the cutoff, so it moves the constant factor and the
crossover, **never the asymptotic slope** -- hence this is a per-dimension
constant-factor comparison (log-y runtime and the speedup ratio), not a scaling
slope. The committed measurement shows the delayed kernel beating the default
at every measured dimension, so it ships as the performance demonstration
config (SPEC honesty constraint (b) satisfied in the affirmative). Each config
carries its own measured cutoff, recorded in the JSON.

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


def main() -> None:
    record = json.loads(DATA.read_text(encoding="utf-8"))
    results = sorted(record["results"], key=lambda r: r["n"])
    dims = [r["n"] for r in results]
    default_ms = [r["default_ns"] / 1e6 for r in results]
    delayed_ms = [r["delayed_ns"] / 1e6 for r in results]
    ratios = [r["default_ns"] / r["delayed_ns"] for r in results]

    fig, (ax, axr) = plt.subplots(
        1, 2, figsize=(9.5, 4.0), gridspec_kw={"width_ratios": [3, 2]}
    )

    ax.plot(dims, default_ms, color="#1f77b4", marker="o",
            label="default base (naive mulImpl)")
    ax.plot(dims, delayed_ms, color="#d62728", marker="s",
            label="delayed-reduction base (strassenBarrett)")
    ax.set_yscale("log")
    ax.set_xlabel("matrix dimension n (n x n over ZMod64 p)")
    ax.set_ylabel("best wall time (ms, log)")
    ax.set_title("mulStrassen base-kernel comparison", fontsize=11)
    ax.grid(True, which="both", linewidth=0.3, alpha=0.5)
    ax.legend(fontsize=8, loc="upper left")

    axr.plot(dims, ratios, color="#d62728", marker="s")
    axr.axhline(1.0, color="#555555", linewidth=0.8, linestyle="--")
    axr.set_xlabel("matrix dimension n")
    axr.set_ylabel("default / delayed  (>1 = delayed faster)")
    axr.set_title("speedup factor", fontsize=11)
    axr.grid(True, which="both", linewidth=0.3, alpha=0.5)
    axr.set_ylim(bottom=0)

    hi = max(ratios)
    lo = min(ratios)
    if lo >= 1.0:
        verdict = f"delayed kernel is {lo:.1f}-{hi:.1f}x FASTER"
    elif hi <= 1.0:
        verdict = f"delayed kernel is {1 / hi:.1f}-{1 / lo:.1f}x SLOWER"
    else:
        verdict = f"delayed/default speedup ranges {lo:.1f}-{hi:.1f}x"
    subtitle = (
        f"prime p = {record['prime']}, cutoffs: default = "
        f"{record.get('default_cutoff', '?')}, barrett = "
        f"{record.get('barrett_cutoff', '?')}; "
        f"{verdict}. "
        "A base kernel moves constants/crossover, never the asymptotic slope."
    )
    fig.text(0.5, 0.005, subtitle, ha="center", fontsize=7, color="#555555")

    fig.tight_layout(rect=(0, 0.03, 1, 1))
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
