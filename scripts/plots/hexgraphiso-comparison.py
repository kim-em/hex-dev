#!/usr/bin/env python3
"""Six-way canonical-labelling plots from retained per-instance measurements.

C dense nauty, sparse nauty and Traces use the pinned 2.9.3 engines. Hex
has separate dense and sparse implementations; IsoGraph is the sixth
comparator. The sparse Hex executable is conformance tested, with search
correctness and totality proved. Historical five-way samples remain unchanged in a separate
archive; the merged file adds only the new sparse measurements.

The main figures time native canonical entry points, excluding input
construction. A supplementary figure shows search and input-conversion
measurements with their different scopes explicitly named. Native sparse
construction and output costs are tabulated separately.
"""
from __future__ import annotations

import argparse
import json
import statistics
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent.parent
sys.path.insert(0, str(REPO_ROOT))
from scripts.bench.graphiso_archive import normalize  # noqa: E402

# Colours identify implementations; distinct markers and dashed sparse-Hex
# lines provide secondary encoding when six colours are hard to distinguish.
# Draw the dashed series above solid lines so near-coincident curves remain
# visible through the gaps instead of hiding the dashed curve completely.
NAUTY, SPARSE, TRACES = "#2a78d6", "#eda100", "#008300"
HEX, HEX_SPARSE, ISO = "#4a3aa7", "#d43b66", "#1baf7a"

PUBLIC = [
    ("nauty 2.9.3 dense (C)", "nauty_ns", NAUTY, "o"),
    ("nauty 2.9.3 sparse (C)", "sparse_ns", SPARSE, "D"),
    ("Traces 2.9.3 (C)", "traces_ns", TRACES, "v"),
    ("Hex dense", "fast_ns", HEX, "s"),
    ("Hex sparse", "hex_sparse_ns", HEX_SPARSE, "P"),
    ("IsoGraph", "iso_ns", ISO, "^"),
]


LIKE = [
    ("C dense + matrix conversion", "nauty_whole_ns", NAUTY, "o"),
    ("C sparse + matrix conversion", "sparse_whole_ns", SPARSE, "D"),
    ("Traces + matrix conversion", "traces_whole_ns", TRACES, "v"),
    ("Hex dense runColored", "search_ns", HEX, "s"),
    ("Hex sparse runColored", "hex_sparse_search_ns", HEX_SPARSE, "P"),
    ("IsoGraph + matrix conversion", "iso_whole_ns", ISO, "^"),
]


def _cactus(ax, rows: list[dict], series) -> None:
    for label, key, color, marker in series:
        # `None` is an instance that curve never solved: the sweep either
        # killed the process or the reported time was over budget. A cactus
        # plot's job is to show that, so it is dropped from the curve and
        # the legend reports the count.
        solved = sorted(r[key] / 1e9 for r in rows if r.get(key) is not None)
        ax.plot(range(1, len(solved) + 1), solved, marker=marker,
                markersize=4, linewidth=2, color=color, linestyle="--" if key.startswith("hex_sparse") else "-",
                zorder=3 if key.startswith("hex_sparse") else 2,
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
                    marker=marker, markersize=4, linewidth=2, color=color, linestyle="--" if key.startswith("hex_sparse") else "-",
                    zorder=3 if key.startswith("hex_sparse") else 2,
                    label=label)
            # a cross where the curve stops, so an unsolved family reads as
            # a wall rather than as a shorter line
            unsolved = [r["n"] for r in group if r.get(key) is None]
            if unsolved and pts:
                ax.plot([min(unsolved)], [max(y for _, y in pts)], marker="x",
                        markersize=7, markeredgewidth=2, color=color,
                        zorder=3 if key.startswith("hex_sparse") else 2,
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


def _save(fig, out_dir, stem: str) -> list:
    """Write both an SVG and a PNG.

    The SVG is what the manual publishes and what scales; the PNG is what
    you can paste into a Zulip thread or an issue, and rendering it here
    rather than by hand is what keeps the two from drifting apart."""
    paths = [out_dir / f"{stem}.svg", out_dir / f"{stem}.png"]
    for path in paths:
        fig.savefig(path, dpi=110 if path.suffix == ".png" else None)
        if path.suffix == ".svg":
            path.write_text("\n".join(line.rstrip() for line in path.read_text().splitlines()) + "\n")
    return paths


def _table(rows: list[dict], hex_refresh: bool = False, sparse_refresh: bool = False,
           sparse_refresh_below: int | None = None) -> str:
    out = ["| family | n | C dense ms | C sparse ms | Traces ms | Hex dense / C dense | Hex sparse / C sparse | Hex sparse / Hex dense | IsoGraph / Hex sparse |",
           "|---|---|---|---|---|---|---|---|---|"]
    def median(group, key):
        xs = [r[key] / 1e6 for r in group if r.get(key) is not None]
        return f"{statistics.median(xs):.3f}" if xs else "—"
    def ratio(group, a, b):
        xs = [r[a] / r[b] for r in group if r.get(a) is not None and r.get(b) is not None]
        return f"{statistics.median(xs):.2f}×" if xs else "—"
    for family in _order(rows) + ["all"]:
        group = rows if family == "all" else [r for r in rows if r['family'] == family]
        cells = [family, f"{min(r['n'] for r in group)}–{max(r['n'] for r in group)}"]
        cells += [median(group, key) for key in ['nauty_ns', 'sparse_ns', 'traces_ns']]
        cells += [ratio(group, a, b) for a, b in [('fast_ns', 'nauty_ns'),
                  ('hex_sparse_ns', 'sparse_ns'), ('hex_sparse_ns', 'fast_ns'),
                  ('iso_ns', 'hex_sparse_ns')]]
        out.append("| " + " | ".join(cells) + " |")
    out += ["", "Ratios are medians of per-instance ratios on the intersection of solved cases. "
            "C and IsoGraph samples are historical; " +
            (f"Hex sparse below {sparse_refresh_below} vertices was refreshed; larger cases and Hex dense "
             "are retained from the preceding comparison on the same shared host. " if sparse_refresh_below is not None else
             "both Hex series were refreshed on the same shared host. " if hex_refresh else
             "Hex dense samples are also historical; Hex sparse was refreshed on the same shared host. " if sparse_refresh else
             "Hex sparse samples were added on the same shared host. ") +
            "These observations are not an adjacent before/after experiment.", "",
            "| family | native sparse build ms | sparse runColored ms | checked canonicalization ms | relabel alone ms |",
            "|---|---|---|---|---|"]
    for family in _order(rows):
        group = [r for r in rows if r['family'] == family]
        out.append("| " + " | ".join([family] + [median(group, key) for key in
            ['hex_sparse_build_ns', 'hex_sparse_search_ns', 'hex_sparse_ns', 'hex_sparse_output_ns']]) + " |")
    out += ["", "Each cost column uses its own solved subset. Build and relabel are measured independently; "
            "their medians must not be subtracted from the canonicalization median."]
    if sparse_refresh_below is not None:
        out += ["", "Only sparse canonicalization and output below the stated order were remeasured; "
                "native construction and search samples are retained from the preceding comparison."]
    return "\n".join(out)


def _solved(rows: list[dict]) -> str:
    """How far each implementation got in each family before the sweep's
    per-instance budget cut it off."""
    cols = [("nauty dense", "nauty_ns"), ("nauty sparse", "sparse_ns"),
            ("Traces", "traces_ns"), ("Hex dense", "fast_ns"),
            ("Hex sparse", "hex_sparse_ns"),
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
    parser.add_argument("--sparse-passes", type=int, choices=[1, 2], default=2,
                        help="completed sparse measurement passes; one marks a preliminary figure")
    parser.add_argument("--hex-refresh", action="store_true",
                        help="both Hex variants were remeasured after the performance changes")
    parser.add_argument("--sparse-refresh", action="store_true",
                        help="Hex sparse was remeasured; the other five series were retained")
    parser.add_argument("--sparse-refresh-below", type=int,
                        help="Hex sparse canonicalization and output were remeasured below this order; "
                             "other measurements were retained")
    args = parser.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)

    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.pyplot as plt
    global ScalarFormatter, NullFormatter
    from matplotlib.ticker import ScalarFormatter, NullFormatter

    rows = [normalize(json.loads(line)) for line in args.data.read_text().splitlines()
            if line]
    pass_caption = ("two passes" if args.sparse_passes == 2 else
                    "preliminary Hex series: one completed pass; comparators: two passes"
                    if args.hex_refresh else
                    "preliminary Hex sparse: one completed pass; historical series: two passes")
    series_caption = (f"five historical series; Hex sparse remeasured below {args.sparse_refresh_below} vertices, larger instances retained"
                      if args.sparse_refresh_below is not None else
                      "four historical comparator series plus refreshed Hex dense and Hex sparse measurements"
                      if args.hex_refresh else
                      "five historical series plus refreshed Hex sparse measurements" if args.sparse_refresh else
                      "five historical series plus new Hex sparse measurements")
    caption = (f"best of repetitions after warm-up, {pass_caption}; identical labelled graphs, native input construction excluded; "
               "five-second per-call budget with family give-up;\n"
               f"{series_caption} on the same shared host; "
               "Hex sparse passes C conformance; search correctness and totality proved")
    if args.machine:
        caption += f"; {args.machine}"

    written = []
    for stem, series, title in [
            ("hexgraphiso-comparison-cactus", PUBLIC,
             "canonical labelling: cactus over "
             f"{len(rows)} family instances")]:
        fig, ax = plt.subplots(figsize=(8, 5.5))
        _cactus(ax, rows, series)
        ax.set_title(title, fontsize=11)
        fig.text(0.5, 0.012, caption, ha="center", fontsize=6.5,
                 style="italic", wrap=True)
        fig.tight_layout(rect=(0, 0.06, 1, 1))
        written.extend(_save(fig, args.out_dir, stem))
        plt.close(fig)

    def family_figure(series, stem: str, title: str, figure_caption=caption):
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
                   bbox_to_anchor=(0.5, 0.048), ncol=3, fontsize=9,
                   frameon=False)
        fig.suptitle(title, fontsize=12)
        fig.text(0.5, 0.006, figure_caption, ha="center", fontsize=6.5,
                 style="italic")
        fig.tight_layout(rect=(0, 0.10, 1, 0.97))
        written.extend(_save(fig, args.out_dir, stem))
        plt.close(fig)

    family_figure(PUBLIC, "hexgraphiso-comparison-families",
                  "canonical labelling by family, against vertex count")

    search_caption = caption.replace("native input construction excluded",
        "C and IsoGraph include matrix-to-native conversion; Hex sparse starts from CSR")
    if args.sparse_refresh_below is not None:
        search_caption = search_caption.replace(series_caption,
            "all search and conversion measurements retained from the preceding comparison")
    family_figure(LIKE, "hexgraphiso-comparison-search-families",
                  "search and conversion costs (input representations differ; see report)", search_caption)

    table = _table(rows, args.hex_refresh, args.sparse_refresh, args.sparse_refresh_below) + "\n\n" + _solved(rows)
    table_path = args.out_dir / "hexgraphiso-comparison-table.md"
    table_path.write_text(table + "\n")
    written.append(table_path)

    for path in written:
        print(path)
    print()
    print(table)
    return 0


if __name__ == "__main__":
    sys.exit(main())
