#!/usr/bin/env python3
"""Proof time against dimension for `rank` and Mathlib's `eval_rank`.

Reads the newest ``reports/bench-results/hex-rank-mathlib-tactic-size-*.json``
(``scripts/bench/rank_tactic_size_sweep.py`` output) and writes
``reports/figures/hex-rank-mathlib-tactic-size.svg``: one panel per family
(full rank, rank ``n - 2``, rank ``n / 2``, rank ``2``), the median proof
time on a log axis against the dimension ``n`` on a log axis, one line per
tactic, with the sample range as error bars. Points that failed or timed
out are not drawn; a family's line ends at the last dimension that tactic
completed within the sweep's cap.

``--check`` regenerates the figure to a temporary file and fails when the
committed figure differs, as CI runs it.

Run: ``python3 scripts/plots/hex-rank-mathlib-tactic-size.py``
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

import matplotlib

matplotlib.rcParams.update(matplotlib.rcParamsDefault)
matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hex-rank-mathlib-tactic-size"
import matplotlib.pyplot as plt  # noqa: E402

ROOT = Path(__file__).resolve().parents[2]
DATA_GLOB = "hex-rank-mathlib-tactic-size-*.json"
FIGURE = ROOT / "reports" / "figures" / "hex-rank-mathlib-tactic-size.svg"
FAMILY_ORDER = ["full", "deficient", "half", "low"]
STYLE = {
    "eval_rank": {"color": "#d62728", "marker": "s", "label": "Mathlib `eval_rank`"},
    "rank": {"color": "#1f77b4", "marker": "o", "label": "hex-rank `rank`"},
}


def newest_record() -> Path:
    candidates = sorted((ROOT / "reports" / "bench-results").glob(DATA_GLOB),
                        key=lambda p: p.stat().st_mtime)
    if not candidates:
        raise SystemExit(f"no {DATA_GLOB} under reports/bench-results")
    return candidates[-1]


def render(record: dict, out: Path) -> None:
    fig, axes = plt.subplots(2, 2, figsize=(9, 7), sharex=False, sharey=True)
    samples = record.get("samples_per_point", 1)
    fig.suptitle("Proof time (literal elaboration, certificate, kernel check) against dimension\n"
                 f"{record['host']} at {record['commit']}, median of {samples} runs, range as bars",
                 fontsize=11)
    for ax, family in zip(axes.flat, FAMILY_ORDER):
        for tool, style in STYLE.items():
            pts = sorted((p for p in record["points"]
                          if p["family"] == family and p["tool"] == tool and p["status"] == "ok"),
                         key=lambda p: p["n"])
            if not pts:
                continue
            ys = [p["proof_s"] for p in pts]
            ax.errorbar([p["n"] for p in pts], ys,
                        yerr=[[y - p.get("proof_min_s", y) for p, y in zip(pts, ys)],
                              [p.get("proof_max_s", y) - y for p, y in zip(pts, ys)]],
                        marker=style["marker"], color=style["color"], label=style["label"],
                        capsize=2, linewidth=1.2)
        ax.axhline(10.0, color="0.6", linestyle=":", linewidth=1)
        ax.set_xscale("log", base=2)
        ax.set_yscale("log")
        ax.set_title(f"n × n, {record['families'][family]}")
        ax.set_xlabel("n")
        ax.grid(True, which="both", linewidth=0.3)
    for ax in axes[:, 0]:
        ax.set_ylabel("proof time (s)")
    axes[0, 0].legend(loc="upper left")
    fig.tight_layout(rect=(0, 0, 1, 0.94))
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
