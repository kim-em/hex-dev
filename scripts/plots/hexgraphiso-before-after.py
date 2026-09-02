#!/usr/bin/env python3
"""Before/after comparison for the hex-graph-iso cactus sweeps.

Renders one figure overlaying two recorded sweeps (before faded and
dashed, after solid), one panel per plot: the canonical-labelling
cactus over the three compiled tiers, and the pair-decision cactus
including the tactic leg when both tactic snapshots exist. Prints a
markdown summary table (per-tier median ratio and worst instance) to
stdout, ready to paste into a pull-request comment.

Usage:

    python3 scripts/plots/hexgraphiso-before-after.py \
        --before reports/bench-results/hexgraphiso-cactus-<fpA>-<host>.jsonl \
        --after  reports/bench-results/hexgraphiso-cactus-<fpB>-<host>.jsonl \
        --out reports/figures/hexgraphiso-before-after-<fpA>-<fpB>.png

Pairs and tactic data are found by filename convention next to each
sweep (``-pairs-`` and ``hexgraphiso-tactic-``).
"""
from __future__ import annotations

import argparse
import json
import statistics
from pathlib import Path

TIERS = [
    ("nauty_ns", "nauty 2.9.3 (C)"),
    ("fast_ns", "hex fast tier"),
    ("checked_ns", "hex checked tier"),
]


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line]


def sibling(path: Path, kind: str) -> Path | None:
    name = path.name.replace("-cactus-", f"-{kind}-")
    if kind == "tactic":
        name = path.name.replace("hexgraphiso-cactus-", "hexgraphiso-tactic-")
        name = name.replace(".jsonl", ".json")
    candidate = path.with_name(name)
    return candidate if candidate.exists() else None


def cactus(ax, rows: list[dict], key: str, label: str, color, solid: bool):
    times = sorted(r[key] / 1e9 for r in rows if key in r)
    ax.plot(range(1, len(times) + 1), times,
            linestyle="-" if solid else "--",
            alpha=1.0 if solid else 0.45,
            marker="o", markersize=2.5, color=color,
            label=f"{label} ({'after' if solid else 'before'})")


def ratio_rows(before: list[dict], after: list[dict], key: str):
    b = {r["name"]: r[key] for r in before if key in r}
    a = {r["name"]: r[key] for r in after if key in r}
    shared = sorted(set(b) & set(a))
    ratios = [(a[n] / b[n], n) for n in shared if b[n] > 0]
    if not ratios:
        return None
    med = statistics.median(r for r, _ in ratios)
    worst = max(ratios)
    best = min(ratios)
    return med, best, worst


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--before", type=Path, required=True)
    parser.add_argument("--after", type=Path, required=True)
    parser.add_argument("--out", type=Path, required=True)
    args = parser.parse_args()

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt

    before = read_jsonl(args.before)
    after = read_jsonl(args.after)
    bpairs_p, apairs_p = sibling(args.before, "pairs"), sibling(args.after, "pairs")
    btac_p, atac_p = sibling(args.before, "tactic"), sibling(args.after, "tactic")

    have_pairs = bpairs_p and apairs_p
    fig, axes = plt.subplots(1, 2 if have_pairs else 1,
                             figsize=(13 if have_pairs else 7, 5), squeeze=False)
    ax = axes[0][0]
    colors = ["#555555", "#1f77b4", "#d62728"]
    for (key, label), color in zip(TIERS, colors):
        cactus(ax, before, key, label, color, solid=False)
        cactus(ax, after, key, label, color, solid=True)
    ax.set_yscale("log")
    ax.set_xlabel("instances solved")
    ax.set_ylabel("per-instance time (s)")
    ax.set_title(f"canonical labelling: {len(after)} instances")
    ax.grid(True, which="both", alpha=0.3)
    ax.legend(fontsize=7)

    lines = ["| layer | median after/before | best | worst |",
             "|---|---|---|---|"]
    for key, label in TIERS[1:]:
        r = ratio_rows(before, after, key)
        if r:
            med, best, worst = r
            lines.append(f"| canonical {label} | {med:.2f}x | "
                         f"{best[0]:.2f}x ({best[1]}) | "
                         f"{worst[0]:.2f}x ({worst[1]}) |")

    if have_pairs:
        bpairs, apairs = read_jsonl(bpairs_p), read_jsonl(apairs_p)
        ax2 = axes[0][1]
        for (key, label), color in zip(TIERS, colors):
            cactus(ax2, bpairs, key, label, color, solid=False)
            cactus(ax2, apairs, key, label, color, solid=True)
        if btac_p and atac_p:
            btac = json.loads(btac_p.read_text())
            atac = json.loads(atac_p.read_text())
            for cache, solid in ((btac, False), (atac, True)):
                times = sorted(v for v in cache.values() if v is not None)
                ax2.plot(range(1, len(times) + 1), times,
                         linestyle="-" if solid else "--",
                         alpha=1.0 if solid else 0.45, marker="o",
                         markersize=2.5, color="#2ca02c",
                         label=f"graph_iso tactic "
                               f"({'after' if solid else 'before'})")
            shared = [n for n in btac if n in atac
                      and btac[n] and atac[n]]
            if shared:
                ratios = sorted((atac[n] / btac[n], n) for n in shared)
                med = statistics.median(r for r, _ in ratios)
                lines.append(f"| graph_iso tactic | {med:.2f}x | "
                             f"{ratios[0][0]:.2f}x ({ratios[0][1]}) | "
                             f"{ratios[-1][0]:.2f}x ({ratios[-1][1]}) |")
        for key, label in TIERS[1:]:
            r = ratio_rows(bpairs, apairs, key)
            if r:
                med, best, worst = r
                lines.append(f"| pairs {label} | {med:.2f}x | "
                             f"{best[0]:.2f}x ({best[1]}) | "
                             f"{worst[0]:.2f}x ({worst[1]}) |")
        ax2.set_yscale("log")
        ax2.set_xlabel("instances solved")
        ax2.set_title("isomorphism pairs")
        ax2.grid(True, which="both", alpha=0.3)
        ax2.legend(fontsize=7)

    fig.tight_layout()
    args.out.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.out, dpi=140)
    print("\n".join(lines))
    print(f"\nfigure: {args.out}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
