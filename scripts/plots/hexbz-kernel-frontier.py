#!/usr/bin/env python3
"""Plot the kernel-evaluation frontier for `Hex.factor` from a kernel-factor record.

Reads a `scripts/bench/kernel_factor_sweep.py` record and draws, per family,
kernel `decide +kernel` wall time (log y, import baseline subtracted) against
polynomial degree. Solved instances are points on a rising curve; the first
censored (timeout / maxRecDepth / maxHeartbeats) degree per family is drawn as a
hollow marker at the timeout ceiling, so the "viability wall" is visible.

Output: `reports/figures/hexbz-kernel-factor-frontier.svg` (deterministic Agg).

Run: `python3 scripts/plots/hexbz-kernel-frontier.py --record <json>`.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hexbz-kernel-frontier"
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter

ROOT = Path(__file__).resolve().parents[2]
FIGURES = ROOT / "reports" / "figures"

# Stable per-family colour/marker.
STYLE = {
    "cyclotomic": ("#1f77b4", "o"),
    "cyclotomic-products": ("#17becf", "s"),
    "swinnerton-dyer": ("#d62728", "^"),
    "sd-products": ("#e377c2", "v"),
    "chebyshev": ("#2ca02c", "D"),
    "legendre": ("#9467bd", "P"),
    "laguerre": ("#8c564b", "X"),
    "wilkinson": ("#ff7f0e", "*"),
    "random-products": ("#bcbd22", "h"),
    "hoeij-zimmermann": ("#7f7f7f", "p"),
}
CENSORED = {"timeout", "maxRecDepth", "maxHeartbeats"}


def seconds_formatter(value, _pos):
    if value <= 0:
        return "0"
    if value >= 1:
        return f"{value:.0f}s"
    if value >= 1e-3:
        return f"{value * 1e3:.0f}ms"
    return f"{value * 1e6:.0f}us"


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--record", type=Path, required=True)
    p.add_argument("--output", type=Path, default=FIGURES / "hexbz-kernel-factor-frontier.svg")
    args = p.parse_args()

    report = json.loads(args.record.read_text())
    cfg = report["config"]
    timeout = cfg["timeout_seconds"]
    host = report["env"].get("hostname", "?")

    by_family = {}
    for r in report["results"]:
        by_family.setdefault(r["family"], []).append(r)

    fig, ax = plt.subplots(figsize=(7.6, 5.0))
    for family in sorted(by_family):
        color, marker = STYLE.get(family, ("#333333", "."))
        rows = sorted(by_family[family], key=lambda r: r["degree"])
        solved = [(r["degree"], (r["kernel_nanos"] or r["total_nanos"]) / 1e9)
                  for r in rows if r["status"] == "ok" and (r["kernel_nanos"] or r["total_nanos"])]
        if solved:
            xs = [d for d, _ in solved]
            ys = [t for _, t in solved]
            ax.plot(xs, ys, marker=marker, color=color, markersize=5, linewidth=1.2,
                    label=f"{family} (wall @ deg {_wall(rows)})")
        # First censored degree: hollow marker at the timeout ceiling.
        cens = [r["degree"] for r in rows if r["status"] in CENSORED]
        if cens:
            ax.plot([min(cens)], [timeout], marker=marker, color=color, markersize=8,
                    markerfacecolor="none", markeredgewidth=1.5, linestyle="none")

    ax.axhline(timeout, color="#999999", linewidth=0.8, linestyle="--")
    ax.text(ax.get_xlim()[1], timeout, f" {timeout:.0f}s timeout (censored)",
            va="bottom", ha="right", fontsize=7, color="#777777")
    ax.set_yscale("log")
    ax.yaxis.set_major_formatter(FuncFormatter(seconds_formatter))
    ax.set_xlabel("polynomial degree")
    ax.set_ylabel("kernel decide+kernel wall time (import baseline subtracted)")
    ax.set_title("Kernel evaluation frontier for Hex.factor")
    ax.grid(True, which="both", linewidth=0.3, alpha=0.5)
    ax.legend(fontsize=7, loc="lower right", ncol=2)
    fig.text(0.5, 0.005,
             f"host {host}; hollow marker = first censored degree; "
             f"import baseline {cfg['import_baseline_nanos']/1e9:.2f}s subtracted",
             ha="center", fontsize=7, color="#555555")
    fig.tight_layout()
    args.output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.output, format="svg", metadata={"Date": None})
    plt.close(fig)
    svg = args.output.read_text()
    args.output.write_text("\n".join(l.rstrip() for l in svg.splitlines()) + "\n")
    try:
        print(args.output.relative_to(ROOT))
    except ValueError:
        print(args.output)


def _wall(rows):
    """Highest degree solved before the family's first censored point."""
    ok = [r["degree"] for r in rows if r["status"] == "ok"]
    return max(ok) if ok else 0


if __name__ == "__main__":
    main()
