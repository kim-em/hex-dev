#!/usr/bin/env python3
"""Proof time against dimension for `det` and Mathlib's `eval_det`.

Reads the newest ``reports/bench-results/hex-bareiss-mathlib-tactic-size-*.json``
(``scripts/bench/det_tactic_size_sweep.py`` output) and writes
``reports/figures/hex-bareiss-mathlib-tactic-size.svg``: one panel per
family (dense 8-bit entries, singular of rank ``n - 1``, dense 64-bit
entries), the median whole-tactic proof time (solid) and its kernel share
(dashed) on a log axis against the dimension ``n``, one color per tactic.
A tactic's line ends at the last dimension it completed within the
sweep's cap; the first dimension it timed out at is marked on the cap.

``--check`` regenerates the figure to a temporary file and fails when the
committed figure differs, as CI runs it.

Run: ``python3 scripts/plots/hex-bareiss-mathlib-tactic-size.py``
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import matplotlib

matplotlib.rcParams.update(matplotlib.rcParamsDefault)
matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hex-bareiss-mathlib-tactic-size"
import matplotlib.pyplot as plt  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
DATA_GLOB = "hex-bareiss-mathlib-tactic-size-*.json"
FIGURE = ROOT / "reports" / "figures" / "hex-bareiss-mathlib-tactic-size.svg"
FAMILY_ORDER = ["dense", "singular", "large"]
STYLE = {
    "eval_det": {"color": "#eb6834", "label": "Mathlib `eval_det`"},
    "det": {"color": "#2a78d6", "label": "hex-bareiss `det`"},
}
SURFACE = "#fcfcfb"
INK = "#3a3a38"


def newest_record() -> Path:
    candidates = sorted((ROOT / "reports" / "bench-results").glob(DATA_GLOB),
                        key=lambda p: p.stat().st_mtime)
    if not candidates:
        raise SystemExit(f"no {DATA_GLOB} under reports/bench-results")
    return candidates[-1]


def render(record: dict, out: Path) -> None:
    cap = record["cap_s"]
    samples = record.get("samples_per_point", 1)
    fig, axes = plt.subplots(1, len(FAMILY_ORDER), figsize=(4.8 * len(FAMILY_ORDER), 4.6),
                             sharey=True, facecolor=SURFACE)
    fig.suptitle("Whole-tactic proof time (solid) and its kernel share (dashed) against dimension, "
                 f"{cap:g} s cap\n{record['host']} at {record['commit']}, median of {samples} runs",
                 fontsize=11, color=INK)
    for ax, family in zip(axes, FAMILY_ORDER):
        ax.set_facecolor(SURFACE)
        for tool, style in STYLE.items():
            pts = sorted((p for p in record["points"]
                          if p["family"] == family and p["tool"] == tool and p["status"] == "ok"),
                         key=lambda p: p["n"])
            stopped = sorted(p["n"] for p in record["points"]
                             if p["family"] == family and p["tool"] == tool and p["status"] != "ok")
            if pts:
                xs = [p["n"] for p in pts]
                ax.plot(xs, [p["proof_s"] for p in pts], color=style["color"], linewidth=2,
                        marker="o", markersize=6, label=f"{style['label']}, whole tactic")
                ax.plot(xs, [p["kernel_s"] for p in pts], color=style["color"], linewidth=2,
                        linestyle="--", marker="o", markersize=6, markerfacecolor=SURFACE,
                        label=f"{style['label']}, kernel share")
                ax.annotate(tool, (xs[-1], pts[-1]["proof_s"]), xytext=(6, -3),
                            textcoords="offset points", fontsize=9, color=INK)
            if stopped:
                ax.plot([stopped[0]], [cap], color=style["color"], marker="x", markersize=8,
                        linestyle="none")
                ax.annotate("cap", (stopped[0], cap), xytext=(0, 7), textcoords="offset points",
                            ha="center", fontsize=8, color="#6b6a63")
        ax.axhline(cap, color="#c3c2b7", linestyle=":", linewidth=1)
        ax.set_yscale("log")
        ax.set_title(f"n × n, {record['families'][family]}", fontsize=11, color=INK)
        ax.set_xlabel("n")
        ax.grid(True, which="major", color="#e6e5df", linewidth=0.8)
        for side in ("top", "right"):
            ax.spines[side].set_visible(False)
        for side in ("left", "bottom"):
            ax.spines[side].set_color("#c3c2b7")
    axes[0].set_ylabel("seconds")
    axes[-1].legend(loc="lower right", frameon=False, fontsize=8)
    fig.tight_layout(rect=(0, 0, 1, 0.9))
    out.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out, format="svg", metadata={"Date": None, "Creator": None})
    plt.close(fig)


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n", 1)[0])
    parser.add_argument("--record", type=Path, help="sweep JSON (default: newest)")
    parser.add_argument("--check", action="store_true", help="fail if the committed figure is stale")
    args = parser.parse_args(argv)
    record = json.loads((args.record or newest_record()).read_text())
    if args.check:
        import tempfile
        with tempfile.TemporaryDirectory() as tmp:
            candidate = Path(tmp) / FIGURE.name
            render(record, candidate)
            if not FIGURE.exists() or candidate.read_bytes() != FIGURE.read_bytes():
                print(f"{FIGURE.relative_to(ROOT)} is stale; rerun {Path(__file__).name}",
                      file=sys.stderr)
                return 1
        print(f"{FIGURE.relative_to(ROOT)} is current")
        return 0
    render(record, FIGURE)
    print(FIGURE.relative_to(ROOT))
    return 0


if __name__ == "__main__":
    sys.exit(main())
