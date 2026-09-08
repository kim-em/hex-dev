#!/usr/bin/env python3
"""Three-way canonical-labelling comparison: nauty, HexGraphIso, IsoGraph.

Local tooling, not merge CI. Times three implementations of canonical
labelling on **the same instances** — the deterministic families of
``bench/HexGraphIso/Cactus.lean``, materialized once and handed to each
side as the same adjacency matrix, so no side is measured on its own
generator's labelling:

* pinned nauty 2.9.3, timed by the standalone driver
  ``scripts/bench/ffi/nauty_corpus_bench.c`` rather than through the
  in-process FFI comparator: the Lean binding pushes the adjacency into
  a ``ByteArray`` a byte at a time and decodes the canonical upper
  triangle into a ``String``, both O(n^2) inside the timed region, and
  at these sizes that marshalling is a median 4x of what gets reported
  as nauty's time,
* ``Hex.GraphIso.canonicalize`` (compiled Lean, proved correct),
* ``IsoGraph.Canon.canonical`` from https://github.com/Timeroot/IsoGraph
  (compiled Lean, proved correct).

Compiled binaries only: no tactic, kernel-replay or ``native_decide``
tier appears here.

The two libraries' entry points do not return the same thing, so the
figures are drawn twice.  ``canonicalize`` returns the canonical graph
*and* its label, and pays a dense relabelling for the graph;
``canonical`` returns the packed certificate, the label and the
automorphisms it found.  The like-for-like pairing is the one that
matches those shapes: ``Nauty.runColored`` (packed rows plus label) on
the hex side, and on the IsoGraph side the search charged the
dense-to-native conversion that ``runColored`` pays through ``rowsOf``.

Input is one merged JSON line per instance, with ``nauty_ns`` and
``nauty_whole_ns`` (densenauty, without and with the dense-to-bitset
conversion), ``fast_ns`` (``canonicalize``), ``lit_ns``
(``runColored``), ``iso_ns`` and ``iso_whole_ns`` (``canonical``,
without and with the graph construction), and ``nauty_ffi_ns`` (the
in-process comparator, for the marshalling column of the table).

Usage:

    python3 scripts/plots/hexgraphiso-isograph-compare.py \\
        --data merged.jsonl --machine "chungus2 (AMD EPYC 9455)"
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent

# Categorical slots 1-3 of the reference palette, assigned by entity and
# never by rank: the C reference, then the two Lean implementations.
# Categorical slots of the reference palette, assigned by entity and never
# by rank. Slots 1-3 keep the colours the earlier three-series figures
# used for nauty, hex and IsoGraph; the two further nauty engines take
# slots 4 and 7. The draw order below is the one the palette validator
# was run on -- it checks *adjacent* pairs for a line chart, so reordering
# the legend needs a re-run.
NAUTY, HEX, ISO = "#2a78d6", "#eb6834", "#1baf7a"
SPARSE, TRACES = "#eda100", "#4a3aa7"

PUBLIC = [
    ("nauty 2.9.3 dense (C)", "nauty_ns", NAUTY, "o"),
    ("nauty 2.9.3 sparse (C)", "sparse_ns", SPARSE, "D"),
    ("Traces 2.9.3 (C)", "traces_ns", TRACES, "v"),
    ("HexGraphIso canonicalize", "fast_ns", HEX, "s"),
    ("IsoGraph canonical", "iso_ns", ISO, "^"),
]

# The three C engines on their own. Dense nauty is what HexGraphIso
# transcribes and therefore the like-for-like reference, but it is the
# wrong tool on a sparse graph and the other two are what the nauty and
# Traces literature points at for those classes.
ENGINES = [
    ("nauty 2.9.3 dense (C)", "nauty_ns", NAUTY, "o"),
    ("nauty 2.9.3 sparse (C)", "sparse_ns", SPARSE, "D"),
    ("Traces 2.9.3 (C)", "traces_ns", TRACES, "v"),
]

# The like-for-like trio, for the per-family breakdown: five series do not
# clear the palette's all-pairs floor, which is the pairlist a small
# multiple is read on, so that figure is faceted into this and ENGINES.
LIKE_FOR_LIKE = [
    ("nauty 2.9.3 dense (C)", "nauty_ns", NAUTY, "o"),
    ("HexGraphIso canonicalize", "fast_ns", HEX, "s"),
    ("IsoGraph canonical", "iso_ns", ISO, "^"),
]
LIKE = [
    ("nauty 2.9.3 dense + conversion", "nauty_whole_ns", NAUTY, "o"),
    ("HexGraphIso runColored", "lit_ns", HEX, "s"),
    ("IsoGraph canonical + graph build", "iso_whole_ns", ISO, "^"),
]


def _cactus(ax, rows: list[dict], series) -> None:
    for label, key, color, marker in series:
        # `None` is an instance that curve never solved: the sweep either
        # killed the process or the reported time was over budget. A cactus
        # plot's job is to show that, so it is dropped from the curve and
        # the legend reports the count.
        solved = sorted(r[key] / 1e9 for r in rows if r.get(key) is not None)
        ax.plot(range(1, len(solved) + 1), solved, marker=marker,
                markersize=4, linewidth=2, color=color,
                label=f"{label} ({len(solved)}/{len(rows)})")
    ax.set_yscale("log")
    ax.set_xlabel("instances canonicalized")
    ax.set_ylabel("per-instance time (s)")
    ax.grid(True, which="both", alpha=0.25, linewidth=0.6)
    ax.legend(loc="upper left", fontsize=9)


def _order(rows: list[dict]) -> list[str]:
    """Families easiest first, by median nauty time: the panels then read
    from the classes the literature calls easy to the ones it calls hard."""
    def key(f: str) -> float:
        times = [r["nauty_ns"] for r in rows
                 if r["family"] == f and r.get("nauty_ns") is not None]
        return statistics.median(times) if times else float("inf")
    return sorted({r["family"] for r in rows}, key=key)


def _families(axes, rows: list[dict], series) -> list[str]:
    families = _order(rows)
    for ax, family in zip(axes, families):
        group = sorted((r for r in rows if r["family"] == family),
                       key=lambda r: r["n"])
        for label, key, color, marker in series:
            pts = [(r["n"], r[key] / 1e9) for r in group
                   if r.get(key) is not None]
            ax.plot([x for x, _ in pts], [y for _, y in pts],
                    marker=marker, markersize=4, linewidth=2, color=color,
                    label=label)
            # a cross where the curve stops, so an unsolved family reads as
            # a wall rather than as a shorter line
            unsolved = [r["n"] for r in group if r.get(key) is None]
            if unsolved and pts:
                ax.plot([min(unsolved)], [max(y for _, y in pts)], marker="x",
                        markersize=7, markeredgewidth=2, color=color,
                        linestyle="none")
        ax.set_xscale("log")
        ax.set_yscale("log")
        # explicit decade-and-a-half ticks: the default log minor labels
        # collide on the families whose n spans less than a decade
        ax.set_xticks([10, 20, 50, 100, 200, 500, 1000])
        ax.xaxis.set_major_formatter(ScalarFormatter())
        ax.xaxis.set_minor_formatter(NullFormatter())
        ax.set_xlim(min(r["n"] for r in group) * 0.8,
                    max(r["n"] for r in group) * 1.25)
        ax.set_title(family, fontsize=10)
        ax.grid(True, which="both", alpha=0.25, linewidth=0.6)
        ax.tick_params(labelsize=8)
    for ax in axes[len(families):]:
        ax.set_visible(False)
    return families


def _table(rows: list[dict]) -> str:
    head = ("| family | n | nauty (median) | Hex `canonicalize` | "
            "IsoGraph `canonical` | IsoGraph / Hex | Hex `runColored` | "
            "IsoGraph + build | sparse | Traces | Hex nodes | "
            "IsoGraph nodes |")
    out = [head, "|---|---|---|---|---|---|---|---|---|---|---|---|"]

    def row(label: str, group: list[dict], span: str) -> str:
        med = statistics.median(r["nauty_ns"] for r in group
                                if r.get("nauty_ns") is not None) / 1e6

        def f(a: str, b: str) -> float:
            # a ratio only over the instances both columns solved
            both = [r[a] / r[b] for r in group
                    if r.get(a) is not None and r.get(b) is not None]
            return statistics.median(both) if both else float("nan")

        return (f"| {label} | {span} | {med:.3f} ms "
                f"| {f('fast_ns', 'nauty_ns'):.0f}× "
                f"| {f('iso_ns', 'nauty_ns'):.1f}× "
                f"| {f('iso_ns', 'fast_ns'):.2f}× "
                f"| {f('lit_ns', 'nauty_ns'):.0f}× "
                f"| {f('iso_whole_ns', 'nauty_whole_ns'):.1f}× "
                f"| {f('sparse_ns', 'nauty_ns'):.2f}× "
                f"| {f('traces_ns', 'nauty_ns'):.2f}× "
                f"| {f('nodes', 'nauty_nodes'):.2f}× "
                f"| {f('iso_nodes', 'nauty_nodes'):.2f}× |")

    for family in _order(rows):
        group = [r for r in rows if r["family"] == family]
        span = f"{min(r['n'] for r in group)}–{max(r['n'] for r in group)}"
        out.append(row(family, group, span))
    out.append(row(f"**all {len(rows)}**", rows,
                   f"{min(r['n'] for r in rows)}–{max(r['n'] for r in rows)}"))
    out.append("")
    out.append("Ratios are per-instance medians against standalone nauty "
               "2.9.3 on the same instance; the sixth column is the "
               "head-to-head. The last two are search-tree sizes against "
               "nauty's: `canonicalize` transcribes nauty's search and "
               "visits exactly its nodes on every instance, so its whole "
               "distance from nauty is per-node cost, while IsoGraph is a "
               "different search and its node count is what varies.")
    return "\n".join(out)


def _solved(rows: list[dict]) -> str:
    """How far each implementation got in each family before the sweep's
    per-instance budget cut it off."""
    cols = [("nauty dense", "nauty_ns"), ("nauty sparse", "sparse_ns"),
            ("Traces", "traces_ns"), ("Hex `canonicalize`", "fast_ns"),
            ("IsoGraph `canonical`", "iso_ns")]
    out = ["| family | instances | " +
           " | ".join(f"{c} largest n solved" for c, _ in cols) + " |",
           "|---|---|" + "---|" * len(cols)]
    for family in _order(rows):
        group = [r for r in rows if r["family"] == family]
        cells = []
        for _, key in cols:
            done = [r["n"] for r in group if r.get(key) is not None]
            missed = [r["n"] for r in group if r.get(key) is None]
            cell = str(max(done)) if done else "none"
            if missed:
                cell += f" (of {max(r['n'] for r in group)})"
            cells.append(cell)
        out.append(f"| {family} | {len(group)} | " + " | ".join(cells) + " |")
    out.append("")
    out.append("Largest instance each implementation canonicalized inside "
               "the sweep's per-instance budget; a parenthesised size is "
               "the largest the corpus offered, so the family was cut off "
               "there.")
    return "\n".join(out)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--data", type=Path, required=True)
    parser.add_argument("--out-dir", type=Path,
                        default=REPO_ROOT / "reports/figures")
    parser.add_argument("--machine", default="")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    global ScalarFormatter, NullFormatter
    from matplotlib.ticker import ScalarFormatter, NullFormatter

    rows = [json.loads(line) for line in args.data.read_text().splitlines()
            if line]
    caption = ("best of several reps after warm-up, over two passes, one "
               "process per instance per implementation; the identical "
               "adjacency matrix is handed to every one;\ncompiled binaries "
               "only, no tactic or kernel replay; a curve stops where its "
               "implementation first exceeded the per-instance budget")
    if args.machine:
        caption += f"; {args.machine}"

    written = []
    for stem, series, title in [
            ("hexgraphiso-isograph-cactus", PUBLIC,
             "canonical labelling: cactus over "
             f"{len(rows)} family instances"),
            ("hexgraphiso-isograph-cactus-likeforlike", LIKE,
             "canonical labelling, matched result shapes: cactus over "
             f"{len(rows)} family instances")]:
        fig, ax = plt.subplots(figsize=(8, 5.5))
        _cactus(ax, rows, series)
        ax.set_title(title, fontsize=11)
        fig.text(0.5, 0.012, caption, ha="center", fontsize=6.5,
                 style="italic", wrap=True)
        path = args.out_dir / f"{stem}.svg"
        fig.tight_layout(rect=(0, 0.06, 1, 1))
        fig.savefig(path)
        plt.close(fig)
        written.append(path)

    def family_figure(series, stem: str, title: str):
        families = _order(rows)
        cols = 4 if len(families) > 12 else 3
        nrows = (len(families) + cols - 1) // cols
        fig, axs = plt.subplots(nrows, cols, figsize=(3.6 * cols, 2.9 * nrows),
                                sharey=True)
        axes = list(axs.flat)
        _families(axes, rows, series)
        for ax in axes[::cols]:
            ax.set_ylabel("time (s)")
        for ax in axes[-cols:]:
            ax.set_xlabel("n (vertices)")
        handles, labels = axes[0].get_legend_handles_labels()
        fig.legend(handles, labels, loc="lower center",
                   bbox_to_anchor=(0.5, 0.048), ncol=len(series), fontsize=9,
                   frameon=False)
        fig.suptitle(title, fontsize=12)
        fig.text(0.5, 0.006, caption, ha="center", fontsize=6.5,
                 style="italic")
        path = args.out_dir / f"{stem}.svg"
        fig.tight_layout(rect=(0, 0.10, 1, 0.97))
        fig.savefig(path)
        plt.close(fig)
        written.append(path)

    family_figure(LIKE_FOR_LIKE, "hexgraphiso-isograph-families",
                  "canonical labelling by family, against vertex count")
    family_figure(ENGINES, "hexgraphiso-nauty-engines",
                  "the three nauty 2.9.3 engines by family, "
                  "against vertex count")

    table = _table(rows) + "\n\n" + _solved(rows)
    table_path = args.out_dir / "hexgraphiso-isograph-table.md"
    table_path.write_text(table + "\n")
    written.append(table_path)

    for path in written:
        print(path)
    print()
    print(table)
    return 0


if __name__ == "__main__":
    sys.exit(main())
