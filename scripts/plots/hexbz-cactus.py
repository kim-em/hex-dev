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

Multiple records merge by **newest measurement per system** (guarded by a
matching corpus SHA-256), so the Lean entries can be re-run as they evolve
without re-running the expensive external comparators: record a fresh hex-only
sweep, then regenerate charts and each external curve is carried over from the
committed baseline it was last measured in.

Run (default: merge every committed record, newest per system):
``python3 scripts/plots/hexbz-cactus.py``
or pin explicit records: ``python3 scripts/plots/hexbz-cactus.py --sweep a.json b.json``.
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


BENCH_RESULTS = ROOT / "reports" / "bench-results"


def merge_reports(paths):
    """Merge several sweep records, taking the NEWEST measurement of each system.

    This is what lets the Lean entries be re-run cheaply without re-running the
    expensive external comparators: point the plotter at the fresh hex-only record
    plus the committed baseline, and each system's curve comes from whichever
    record measured it most recently. All records must cover the same corpus
    (matching `corpus_sha256`), since a system's solved-set is only comparable
    against the same instances.

    Returns (results, systems, provenance, cutoffs). `systems` is ordered by the
    canonical STYLE order for a stable legend; `provenance[system]` is
    (record filename, ISO timestamp, cutoff).
    """
    reports = [(pth, json.loads(pth.read_text())) for pth in paths]
    shas = {r["config"]["corpus_sha256"] for _, r in reports}
    if len(shas) > 1:
        raise SystemExit(
            "refusing to merge sweeps over different corpora (corpus_sha256 "
            "mismatch); re-run the external systems against the current corpus")
    chosen = {}  # system -> (ts, filename, iso, cutoff, results)
    for pth, rep in reports:
        ts = rep["env"].get("timestamp_unix_ms") or 0
        iso = rep["env"].get("timestamp_iso")
        cutoff = rep["config"]["cutoff_seconds"]
        for system in rep["config"]["systems"]:
            if system not in chosen or ts > chosen[system][0]:
                sysres = [r for r in rep["results"] if r["system"] == system]
                chosen[system] = (ts, pth.name, iso, cutoff, sysres)
    results, provenance, cutoffs = [], {}, set()
    for system, (_, fname, iso, cutoff, sysres) in chosen.items():
        results.extend(sysres)
        provenance[system] = (fname, iso, cutoff)
        cutoffs.add(cutoff)
    order = list(STYLE.keys())
    systems = sorted(chosen, key=lambda s: order.index(s) if s in order else len(order))
    return results, systems, provenance, cutoffs


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--sweep", type=Path, nargs="+", default=None,
                   help="one or more sweep JSONs; when several are given (or by "
                        "default, all committed records), the newest measurement "
                        "of each system wins")
    p.add_argument("--outdir", type=Path, default=FIGURES)
    args = p.parse_args()

    paths = args.sweep or sorted(BENCH_RESULTS.glob("hexbz-factor-sweep-*.json"))
    if not paths:
        raise SystemExit("no sweep records found")
    results, systems, provenance, cutoffs = merge_reports(paths)
    corpus = load_corpus()
    cutoff_str = (f"{next(iter(cutoffs))}s" if len(cutoffs) == 1
                  else "mixed " + "/".join(f"{c}s" for c in sorted(cutoffs)))
    if len(paths) == 1:
        src = paths[0].name
    else:
        src = f"newest-per-system across {len(paths)} records"
    subtitle = (f"cutoff {cutoff_str}; source {src}; "
                f"declines and timeouts count as unsolved")

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
    print("system provenance (newest measurement used):")
    for system in systems:
        fname, iso, cutoff = provenance[system]
        print(f"  {system:26s} {iso}  {cutoff}s  {fname}")


if __name__ == "__main__":
    raise SystemExit(main())
