#!/usr/bin/env python3
"""Animate the hex-graph-iso cactus plot across recorded sweeps.

Reads every committed sweep under ``reports/bench-results/``
(``hexgraphiso-cactus-<fp>-<host>.jsonl`` with its ``.meta.json``),
orders frames by the recorded date, draws the three-tier canonical
cactus with axes fixed across frames, and writes an animated GIF.
Sweeps without a meta file sort first by filename.

Usage:

    python3 scripts/plots/hexgraphiso-cactus-animation.py \
        --out reports/figures/hexgraphiso-cactus-animation.gif
"""
from __future__ import annotations

import argparse
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "reports" / "bench-results"

# ``checked_ns`` is the certificate replay, recorded while it was a
# separate tier from ``fast_ns``. Sweeps taken after the two became one
# omit it, and the frame then draws no such series.
TIERS = [
    ("nauty_ns", "nauty 2.9.3 (C)", "#555555"),
    ("fast_ns", "hex canonicalize", "#1f77b4"),
    ("checked_ns", "hex certificate replay (pre-collapse)", "#d62728"),
]


def read_jsonl(path: Path) -> list[dict]:
    return [json.loads(line) for line in path.read_text().splitlines() if line]


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--out", type=Path,
                        default=ROOT / "reports" / "figures" /
                        "hexgraphiso-cactus-animation.gif")
    parser.add_argument("--seconds-per-frame", type=float, default=1.6)
    args = parser.parse_args()

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    from matplotlib.animation import FuncAnimation, PillowWriter

    frames = []
    for path in RESULTS.glob("hexgraphiso-cactus-*.jsonl"):
        meta_path = path.with_name(path.name.replace(".jsonl", ".meta.json"))
        meta = json.loads(meta_path.read_text()) if meta_path.exists() else {}
        frames.append((meta.get("date", ""), meta, path))
    frames.sort()
    if not frames:
        print("no sweep data found")
        return 1

    sweeps = [(meta, read_jsonl(path)) for _, meta, path in frames]
    all_ns = [r[key] for _, rows in sweeps for r in rows
              for key, _, _ in TIERS if key in r]
    ymin, ymax = min(all_ns) / 1e9 / 2, max(all_ns) / 1e9 * 2
    xmax = max(len(rows) for _, rows in sweeps) + 1

    fig, ax = plt.subplots(figsize=(7.5, 5))

    def draw(i: int):
        ax.clear()
        meta, rows = sweeps[i]
        for key, label, color in TIERS:
            times = sorted(r[key] / 1e9 for r in rows if key in r)
            if not times:
                continue
            ax.plot(range(1, len(times) + 1), times, marker="o",
                    markersize=2.5, color=color, label=label)
        ax.set_yscale("log")
        ax.set_ylim(ymin, ymax)
        ax.set_xlim(0, xmax)
        ax.set_xlabel("instances solved")
        ax.set_ylabel("per-instance time (s)")
        stamp = meta.get("date", "?")[:10]
        label = meta.get("label", meta.get("describe", ""))
        ax.set_title(f"hex-graph-iso canonical labelling — {stamp} {label} "
                     f"({i + 1}/{len(sweeps)})")
        ax.grid(True, which="both", alpha=0.3)
        ax.legend(fontsize=8, loc="upper left")

    anim = FuncAnimation(fig, draw, frames=len(sweeps))
    args.out.parent.mkdir(parents=True, exist_ok=True)
    anim.save(args.out,
              writer=PillowWriter(fps=1.0 / args.seconds_per_frame))
    print(f"{args.out} ({len(sweeps)} frames)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
