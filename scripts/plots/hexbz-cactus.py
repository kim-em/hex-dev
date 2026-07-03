#!/usr/bin/env python3
"""Cactus (survival) and runtime-vs-degree plots for the cross-system factor sweep.

Reads a durable sweep JSON (``scripts/bench/factor_sweep.py`` output) and the
corpus JSONL, and emits, per family plus the combined mix-doctrine mixture:

* ``reports/figures/hexbz-cactus-<family>.svg`` and ``-combined.svg`` -- for each
  system, its solved instances sorted by median runtime, plotting cumulative time
  (log y) against N instances solved (x); a curve ends at that system's solved
  count.
* ``reports/figures/hexbz-runtime-degree-<family>.svg`` -- the per-family log-y
  runtime-vs-degree comparator plot, which falls out of the same data.

``reports/figures/`` is auto-published through the Verso manual's ``extraFiles``.
Charts regenerate deterministically from the committed JSON.

Run: ``python3 scripts/plots/hexbz-cactus.py [--sweep <json>]``.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hexbz-cactus"
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter

ROOT = Path(__file__).resolve().parents[2]
CORPUS_PATH = ROOT / "bench" / "corpus" / "hexbz-factor-corpus.jsonl"
FIGURES = ROOT / "reports" / "figures"

# Stable per-system styling so a system keeps its colour/marker across figures.
STYLE = {
    "hex-factor": ("#1f77b4", "o", "hex (factor)"),
    "hex-lattice": ("#2ca02c", "s", "hex (lattice / van Hoeij CLD)"),
    "hex-fast": ("#17becf", "D", "hex (fast)"),
    "hex-classical-nodecline": ("#d62728", "x", "hex (classical, no decline)"),
    "flint": ("#9467bd", "^", "FLINT"),
    "ntl": ("#8c564b", "v", "NTL"),
    "pari": ("#e377c2", "P", "PARI/GP"),
    "isabelle-bz": ("#ff7f0e", "*", "verified Isabelle BZ"),
    "isabelle-lll": ("#bcbd22", "h", "verified Isabelle LLL"),
}


def seconds_formatter(value, _pos):
    if value <= 0:
        return "0"
    if value >= 1:
        return f"{value:.0f}s" if value == int(value) else f"{value:.1f}s"
    if value >= 1e-3:
        return f"{value * 1e3:.0f}ms"
    return f"{value * 1e6:.0f}us"


def load_corpus():
    info = {}
    for line in CORPUS_PATH.read_text().splitlines():
        if not line.strip():
            continue
        rec = json.loads(line)
        info[rec["name"]] = {"family": rec["family"], "degree": rec["degree"],
                             "combined": rec.get("combined", False)}
    return info


def solved_series(results, system, names):
    """(sorted median seconds) for a system's ok records limited to `names`."""
    times = [r["median_nanos"] / 1e9 for r in results
             if r["system"] == system and r["name"] in names
             and r["status"] == "ok" and r["median_nanos"] is not None]
    return sorted(times)


def degree_series(results, system, names, corpus):
    pts = [(corpus[r["name"]]["degree"], r["median_nanos"] / 1e9) for r in results
           if r["system"] == system and r["name"] in names
           and r["status"] == "ok" and r["median_nanos"] is not None]
    return sorted(pts)


def _finalize(fig, ax, output, title, xlabel, ylabel, subtitle=None):
    ax.set_yscale("log")
    ax.yaxis.set_major_formatter(FuncFormatter(seconds_formatter))
    ax.set_xlabel(xlabel)
    ax.set_ylabel(ylabel)
    ax.set_title(title)
    ax.grid(True, which="both", linewidth=0.3, alpha=0.5)
    ax.legend(fontsize=8, loc="upper left")
    if subtitle:
        fig.text(0.5, 0.005, subtitle, ha="center", fontsize=7, color="#555555")
    fig.tight_layout()
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, format="svg", metadata={"Date": None})
    plt.close(fig)
    svg = output.read_text(encoding="utf-8")
    output.write_text("\n".join(line.rstrip() for line in svg.splitlines()) + "\n",
                      encoding="utf-8")


def plot_cactus(results, systems, names, output, title, subtitle):
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    drew = False
    for system in systems:
        times = solved_series(results, system, names)
        if not times:
            continue
        color, marker, label = STYLE.get(system, ("#333333", ".", system))
        xs = list(range(1, len(times) + 1))
        cumulative = []
        acc = 0.0
        for t in times:
            acc += t
            cumulative.append(acc)
        ax.plot(xs, cumulative, marker=marker, color=color, markersize=4,
                linewidth=1.2, label=f"{label} ({len(times)})")
        drew = True
    if not drew:
        plt.close(fig)
        return False
    _finalize(fig, ax, output, title, "instances solved (cumulative)",
              "cumulative median wall-clock", subtitle)
    return True


def plot_runtime_degree(results, systems, names, corpus, output, title, subtitle):
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    drew = False
    for system in systems:
        pts = degree_series(results, system, names, corpus)
        if not pts:
            continue
        color, marker, label = STYLE.get(system, ("#333333", ".", system))
        xs = [p[0] for p in pts]
        ys = [p[1] for p in pts]
        ax.plot(xs, ys, marker=marker, color=color, markersize=4, linewidth=1.0,
                linestyle="-", label=label)
        drew = True
    if not drew:
        plt.close(fig)
        return False
    _finalize(fig, ax, output, title, "polynomial degree", "median wall-clock", subtitle)
    return True


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--sweep", type=Path, required=True, help="sweep JSON from factor_sweep.py")
    p.add_argument("--outdir", type=Path, default=FIGURES)
    args = p.parse_args()

    report = json.loads(args.sweep.read_text())
    results = report["results"]
    corpus = load_corpus()
    systems = report["config"]["systems"]
    cutoff = report["config"]["cutoff_seconds"]
    host = report["env"].get("hostname", "?")
    subtitle = (f"cutoff {cutoff}s; host {host}; sweep "
                f"{args.sweep.name}; declines and timeouts count as unsolved")

    families = sorted({corpus[r["name"]]["family"] for r in results if r["name"] in corpus})
    written = []
    for family in families:
        names = {n for n, i in corpus.items() if i["family"] == family}
        cactus = args.outdir / f"hexbz-cactus-{family}.svg"
        if plot_cactus(results, systems, names, cactus,
                       f"Cactus plot -- {family}", subtitle):
            written.append(cactus)
        rvd = args.outdir / f"hexbz-runtime-degree-{family}.svg"
        if plot_runtime_degree(results, systems, names, corpus, rvd,
                               f"Runtime vs degree -- {family}", subtitle):
            written.append(rvd)

    combined_names = {n for n, i in corpus.items() if i["combined"]}
    combined = args.outdir / "hexbz-cactus-combined.svg"
    if plot_cactus(results, systems, combined_names, combined,
                   "Cactus plot -- combined mixture (balanced across families)", subtitle):
        written.append(combined)

    for path in written:
        try:
            print(path.relative_to(ROOT))
        except ValueError:
            print(path)
    print(f"{len(written)} figures written")


if __name__ == "__main__":
    raise SystemExit(main())
