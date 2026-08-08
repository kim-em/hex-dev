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
committed baseline it was last measured in. The default current-state charts
exclude retired standalone Hex diagnostic comparators; they can still be
plotted by naming their records explicitly with ``--sweep``. This does not
remove the live lattice fallback inside ``hex-factor``.

Run (default: merge committed records for the current corpus, newest per system):
``python3 scripts/plots/hexbz-cactus.py``
or pin explicit records: ``python3 scripts/plots/hexbz-cactus.py --sweep a.json b.json``.

Before/after mode: pass ``--baseline before.json`` alongside ``--sweep after.json``
to overlay each system's *before* curve as a dotted, hollow-marker line (labelled
"… — before") under its solid *after* curve. Both sides must cover the same corpus
(matching ``corpus_sha256``). This is the reproducible form of a one-off A/B — e.g.
record the same hex-only sweep on ``main`` and on a change branch, then::

    python3 scripts/plots/hexbz-cactus.py --sweep after.json --baseline before.json
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import sys
import tempfile

sys.path.insert(0, str(Path(__file__).resolve().parent))

from hexbz_sweep_data import (  # noqa: E402
    CURRENT_SYSTEMS,
    ROOT,
    default_sweep_paths,
    load_corpus,
    merge_reports,
)

import matplotlib

matplotlib.rcParams.update(matplotlib.rcParamsDefault)
matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hexbz-cactus"
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter

FIGURES = ROOT / "reports" / "figures"

# Stable per-system styling so a system keeps its colour/marker across figures.
STYLE = {
    "hex-factor": ("#1f77b4", "o", "hex (factor)"),
    "hex-lattice": ("#2ca02c", "s", "hex (lattice / van Hoeij CLD)"),
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


def _cumulative(times):
    xs = list(range(1, len(times) + 1))
    cumulative, acc = [], 0.0
    for t in times:
        acc += t
        cumulative.append(acc)
    return xs, cumulative


def plot_cactus(results, systems, names, output, title, subtitle, baseline_results=None):
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    drew = False
    for system in systems:
        color, marker, label = STYLE.get(system, ("#333333", ".", system))
        # before: dotted, hollow markers, drawn first so the solid after sits on top.
        if baseline_results is not None:
            btimes = solved_series(baseline_results, system, names)
            if btimes:
                bxs, bcum = _cumulative(btimes)
                ax.plot(bxs, bcum, marker=marker, color=color, markersize=3,
                        markerfacecolor="none", linewidth=1.0, linestyle=":",
                        alpha=0.85, label=f"{label} — before ({len(btimes)})")
                drew = True
        # after: solid.
        times = solved_series(results, system, names)
        if times:
            xs, cumulative = _cumulative(times)
            ax.plot(xs, cumulative, marker=marker, color=color, markersize=4,
                    linewidth=1.2, label=f"{label} ({len(times)})")
            drew = True
    if not drew:
        plt.close(fig)
        return False
    _finalize(fig, ax, output, title, "instances solved (cumulative)",
              "cumulative median wall-clock", subtitle)
    return True


def plot_runtime_degree(results, systems, names, corpus, output, title, subtitle,
                        baseline_results=None):
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    drew = False
    for system in systems:
        color, marker, label = STYLE.get(system, ("#333333", ".", system))
        if baseline_results is not None:
            bpts = degree_series(baseline_results, system, names, corpus)
            if bpts:
                ax.plot([p[0] for p in bpts], [p[1] for p in bpts], marker=marker,
                        color=color, markersize=3, markerfacecolor="none",
                        linewidth=0.9, linestyle=":", alpha=0.85,
                        label=f"{label} — before")
                drew = True
        pts = degree_series(results, system, names, corpus)
        if pts:
            ax.plot([p[0] for p in pts], [p[1] for p in pts], marker=marker,
                    color=color, markersize=4, linewidth=1.0, linestyle="-",
                    label=label)
            drew = True
    if not drew:
        plt.close(fig)
        return False
    _finalize(fig, ax, output, title, "polynomial degree", "median wall-clock", subtitle)
    return True


def main():
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--sweep", type=Path, nargs="+", default=None,
                   help="one or more sweep JSONs; when several are given (or by "
                        "default, all committed records for the current corpus), "
                        "the newest measurement of each system wins")
    p.add_argument("--baseline", type=Path, nargs="+", default=None,
                   help="one or more sweep JSONs measured BEFORE a change; each "
                        "system's before curve is overlaid as a dotted, hollow "
                        "line. Must cover the same corpus as --sweep.")
    p.add_argument("--outdir", type=Path, default=FIGURES)
    p.add_argument("--check", action="store_true",
                   help="regenerate the default figures in a temporary directory "
                        "and fail if any committed SVG differs")
    args = p.parse_args()

    check_directory = None
    if args.check:
        if args.sweep or args.baseline or args.outdir != FIGURES:
            p.error("--check validates only the default committed figure set")
        check_directory = tempfile.TemporaryDirectory(prefix="hexbz-plots-")
        args.outdir = Path(check_directory.name)

    if args.sweep:
        paths = args.sweep
        skipped = 0
    else:
        paths, skipped = default_sweep_paths()
    if not paths:
        note = f"; skipped {skipped} records for other or unknown corpora" if skipped else ""
        raise SystemExit(f"no sweep records found for the current corpus{note}")
    if skipped:
        print(f"skipped {skipped} historical sweep records with a different corpus hash")
    results, systems, provenance, cutoffs = merge_reports(paths)
    if args.sweep is None:
        systems = [system for system in systems if system in CURRENT_SYSTEMS]
        results = [result for result in results if result["system"] in CURRENT_SYSTEMS]
        provenance = {
            system: source for system, source in provenance.items()
            if system in CURRENT_SYSTEMS
        }

    baseline_results = None
    if args.baseline:
        baseline_results, _, base_prov, base_cutoffs = merge_reports(args.baseline)
        after_sha = {json.loads(p.read_text())["config"]["corpus_sha256"] for p in paths}
        before_sha = {json.loads(p.read_text())["config"]["corpus_sha256"] for p in args.baseline}
        if after_sha != before_sha:
            raise SystemExit(
                "refusing to overlay a baseline measured over a different corpus "
                "(corpus_sha256 mismatch between --sweep and --baseline)")
        cutoffs = cutoffs | base_cutoffs

    corpus = load_corpus()
    cutoff_str = (f"{next(iter(cutoffs))}s" if len(cutoffs) == 1
                  else "mixed " + "/".join(f"{c}s" for c in sorted(cutoffs)))
    if len(paths) == 1:
        src = paths[0].name
    else:
        src = f"newest-per-system across {len(paths)} records"
    if baseline_results is not None:
        src += "; before = dotted (" + "/".join(p.name for p in args.baseline) + ")"
    subtitle = (f"cutoff {cutoff_str}; source {src}; "
                f"declines and timeouts count as unsolved")

    families = sorted({corpus[r["name"]]["family"] for r in results if r["name"] in corpus})
    written = []
    for family in families:
        names = {n for n, i in corpus.items() if i["family"] == family}
        cactus = args.outdir / f"hexbz-cactus-{family}.svg"
        if plot_cactus(results, systems, names, cactus,
                       f"Cactus plot -- {family}", subtitle, baseline_results):
            written.append(cactus)
        rvd = args.outdir / f"hexbz-runtime-degree-{family}.svg"
        if plot_runtime_degree(results, systems, names, corpus, rvd,
                               f"Runtime vs degree -- {family}", subtitle, baseline_results):
            written.append(rvd)

    combined_names = {n for n, i in corpus.items() if i["combined"]}
    combined = args.outdir / "hexbz-cactus-combined.svg"
    if plot_cactus(results, systems, combined_names, combined,
                   "Cactus plot -- combined mixture (balanced across families)", subtitle,
                   baseline_results):
        written.append(combined)

    if args.check:
        generated = {path.name: path for path in written}
        committed_paths = list(FIGURES.glob("hexbz-cactus-*.svg")) + \
            list(FIGURES.glob("hexbz-runtime-degree-*.svg"))
        committed = {path.name: path for path in committed_paths}
        stale = sorted(
            name for name in generated.keys() & committed.keys()
            if generated[name].read_bytes() != committed[name].read_bytes())
        missing = sorted(generated.keys() - committed.keys())
        obsolete = sorted(committed.keys() - generated.keys())
        if stale or missing or obsolete:
            details = []
            if stale:
                details.append("stale: " + ", ".join(stale))
            if missing:
                details.append("missing: " + ", ".join(missing))
            if obsolete:
                details.append("obsolete: " + ", ".join(obsolete))
            raise SystemExit(
                "committed factorization figures are not current; run "
                "with matplotlib 3.11.1: `python3 "
                "scripts/plots/hexbz-cactus.py`: " + "; ".join(details))
        print(f"{len(written)} committed figures are current")
        check_directory.cleanup()
    else:
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
