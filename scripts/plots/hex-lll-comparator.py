#!/usr/bin/env python3
"""Generate the HexLLL comparator-runtime plot from committed bench exports."""

from __future__ import annotations

import argparse
import json
import re
from dataclasses import dataclass
from pathlib import Path

import matplotlib

matplotlib.use("Agg")
matplotlib.rcParams["svg.hashsalt"] = "hex-lll-comparator"
import matplotlib.pyplot as plt
from matplotlib.ticker import FuncFormatter


ROOT = Path(__file__).resolve().parents[2]
# Post-warmupFirstIter, post-perf-fix exports. Each family file has all
# comparators measured in one run so the ratios are internally consistent
# within each source family. Pre-#6642 exports recorded
# the fpLLL comparator under the `runFpylllFirstShortVector*` function
# names (process-call fpylll subprocess); the regex accepts either.
DEFAULT_RANDOM_CONSOLIDATED = (
    ROOT / "reports/bench-results/hex-lll-random-bounded-schur.json"
)
DEFAULT_HARSH_CONSOLIDATED = (
    ROOT / "reports/bench-results/hex-lll-harsh-cubic-extended-schur.json"
)
DEFAULT_ISABELLE_BOTTOM = (
    ROOT / "reports/bench-results/hex-lll-isabelle-bottom-e211854d1435.json"
)
# The Lean-certified and Isabelle-certified series come from separate
# committed carica runs: the Lean-certified ladder tracks the current
# checker, while the Isabelle-certified ladder is the full Lean+Isabelle
# schedule (the Lean-certified export carries no Isabelle rows). Within
# each series the rungs share a host and commit; the cross-series ratio
# carries the cross-run caveat recorded in reports/hex-lll-scaling.md.
DEFAULT_CERTIFIED = ROOT / "reports/bench-results/hex-lll-certified-443bf8fb.json"
DEFAULT_ISABELLE_CERTIFIED = (
    ROOT / "reports/bench-results/hex-lll-certified-carica.json"
)
DEFAULT_ISABELLE_CERTIFIED_RANDOM = DEFAULT_ISABELLE_CERTIFIED
DEFAULT_ISABELLE_CERTIFIED_HARSH = DEFAULT_ISABELLE_CERTIFIED
DEFAULT_RANDOM_OUTPUT = ROOT / "reports/figures/hex-lll-comparator-random-bounded.svg"
DEFAULT_HARSH_OUTPUT = ROOT / "reports/figures/hex-lll-comparator-harsh-cubic.svg"

LEAN_RANDOM = re.compile(r"runFirstShortVectorRandomBoundedNormSq([0-9]+)$")
ISABELLE_RANDOM = re.compile(r"runIsabelleRandomBoundedNormSq([0-9]+)$")
FPLLL_RANDOM = re.compile(
    r"run(?:FpLLL|Fpylll)FirstShortVectorRandomBounded([0-9]+)Checksum$"
)
CERTIFIED_RANDOM = re.compile(
    r"runCertifiedFirstShortVectorRandomBounded([0-9]+)Checksum$"
)
ISABELLE_CERTIFIED_RANDOM = re.compile(
    r"runIsabelleCertifiedRandomBoundedNormSq([0-9]+)$"
)
LEAN_HARSH = re.compile(r"runFirstShortVectorHarshCubicNormSq([0-9]+)$")
ISABELLE_HARSH = re.compile(r"runIsabelleHarshCubicNormSq([0-9]+)$")
FPLLL_HARSH = re.compile(
    r"run(?:FpLLL|Fpylll)FirstShortVectorHarshCubic([0-9]+)Checksum$"
)
CERTIFIED_HARSH = re.compile(
    r"runCertifiedFirstShortVectorHarshCubic([0-9]+)Checksum$"
)
ISABELLE_CERTIFIED_HARSH = re.compile(
    r"runIsabelleCertifiedHarshCubicNormSq([0-9]+)$"
)


@dataclass(frozen=True)
class Series:
    label: str
    xs: list[int]
    ys: list[float]


@dataclass(frozen=True)
class FamilyConfig:
    lean_pattern: re.Pattern[str]
    isabelle_pattern: re.Pattern[str]
    fpll_pattern: re.Pattern[str]
    certified_pattern: re.Pattern[str]
    isabelle_certified_pattern: re.Pattern[str]
    fpll_path: Path
    certified_path: Path
    isabelle_certified_path: Path
    output: Path
    title: str
    xlabel: str
    # If set, read Lean and Isabelle from this single file instead of
    # the densified file + the standalone Isabelle export.
    consolidated_path: Path | None = None
    bottom_consistency: bool = False
    # On harsh-cubic the certified paths run slightly slower than their
    # native counterparts (fpLLL's advantage is too small to offset the
    # checker), so the certified curves are omitted from that figure.
    include_certified: bool = True


FAMILIES = {
    "random-bounded": FamilyConfig(
        lean_pattern=LEAN_RANDOM,
        isabelle_pattern=ISABELLE_RANDOM,
        fpll_pattern=FPLLL_RANDOM,
        certified_pattern=CERTIFIED_RANDOM,
        isabelle_certified_pattern=ISABELLE_CERTIFIED_RANDOM,
        fpll_path=DEFAULT_RANDOM_CONSOLIDATED,
        certified_path=DEFAULT_CERTIFIED,
        isabelle_certified_path=DEFAULT_ISABELLE_CERTIFIED_RANDOM,
        output=DEFAULT_RANDOM_OUTPUT,
        title="HexLLL random-bounded comparator runtime",
        xlabel="random-bounded dimension n",
        consolidated_path=DEFAULT_RANDOM_CONSOLIDATED,
        bottom_consistency=True,
    ),
    "harsh-cubic": FamilyConfig(
        lean_pattern=LEAN_HARSH,
        isabelle_pattern=ISABELLE_HARSH,
        fpll_pattern=FPLLL_HARSH,
        certified_pattern=CERTIFIED_HARSH,
        isabelle_certified_pattern=ISABELLE_CERTIFIED_HARSH,
        fpll_path=DEFAULT_HARSH_CONSOLIDATED,
        certified_path=DEFAULT_CERTIFIED,
        isabelle_certified_path=DEFAULT_ISABELLE_CERTIFIED_HARSH,
        output=DEFAULT_HARSH_OUTPUT,
        title="HexLLL harsh-cubic comparator runtime",
        xlabel="harsh-cubic dimension n",
        consolidated_path=DEFAULT_HARSH_CONSOLIDATED,
        include_certified=False,
    ),
}


# Marker style keyed by series label, so a curve keeps the same marker
# whether or not the certified curves are present in a given figure.
STYLE_BY_LABEL = {
    "Lean native": {"marker": "o", "linewidth": 2.0},
    "Isabelle native": {"marker": "s", "linewidth": 2.0},
    "Lean certified": {"marker": "D", "linewidth": 2.0, "markersize": 6.5},
    "Isabelle certified": {"marker": "^", "linewidth": 2.0, "markersize": 7.0},
    "fpLLL via fplll-ffi": {"marker": "v", "linewidth": 2.0, "markersize": 7.0},
}


def load_results(path: Path) -> list[dict]:
    with path.open(encoding="utf-8") as handle:
        data = json.load(handle)
    return data["results"]


def median_ms(result: dict) -> float:
    return result["median_nanos"] / 1_000_000.0


def collect_series(results: list[dict], pattern: re.Pattern[str], label: str) -> Series:
    values: dict[int, float] = {}
    for result in results:
        match = pattern.search(result["function"])
        if match:
            values[int(match.group(1))] = median_ms(result)
    if not values:
        raise ValueError(f"no results found for {label}")
    xs = sorted(values)
    return Series(label=label, xs=xs, ys=[values[x] for x in xs])


def assert_bottom_consistent(bottom_results: list[dict], isabelle: Series) -> None:
    """Load the historical bottom-rung export named in the issue body.

    The report's ratio table uses the later densified run for the Isabelle curve.
    This check keeps the older committed export visible without mixing host runs
    in one plotted curve.
    """
    bottom = collect_series(bottom_results, ISABELLE_RANDOM, "Isabelle bottom")
    if bottom.xs != [30]:
        raise ValueError(f"expected one Isabelle bottom rung at n=30, got {bottom.xs}")
    if 30 not in isabelle.xs:
        raise ValueError("densified Isabelle data is missing n=30")


def seconds_formatter(value: float, _position: int) -> str:
    if value < 1.0:
        return f"{value * 1000:g} ms"
    return f"{value:g} s"


def plot(series: list[Series], output: Path, title: str, xlabel: str) -> None:
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    for item in series:
        ax.plot(
            item.xs,
            [y / 1000.0 for y in item.ys],
            label=item.label,
            **STYLE_BY_LABEL[item.label],
        )

    ax.set_title(title)
    ax.set_xlabel(xlabel)
    ax.set_ylabel("median wall time per call")
    ax.set_yscale("log")
    ax.yaxis.set_major_formatter(FuncFormatter(seconds_formatter))
    ax.set_xticks(sorted({x for item in series for x in item.xs}))
    ax.grid(True, which="both", axis="y", alpha=0.25)
    ax.grid(True, which="major", axis="x", alpha=0.15)
    ax.legend(frameon=False)
    fig.tight_layout()
    output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(output, format="svg", metadata={"Date": None})
    svg = output.read_text(encoding="utf-8")
    output.write_text(
        "\n".join(line.rstrip() for line in svg.splitlines()) + "\n",
        encoding="utf-8",
    )


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Generate a HexLLL comparator-runtime plot."
    )
    parser.add_argument(
        "--family",
        choices=sorted(FAMILIES),
        required=True,
        help="Input family to plot.",
    )
    parser.add_argument(
        "--consolidated",
        type=Path,
        default=None,
        help="Override the family-specific consolidated bench export.",
    )
    parser.add_argument(
        "--isabelle-bottom", type=Path, default=DEFAULT_ISABELLE_BOTTOM
    )
    parser.add_argument(
        "--certified",
        type=Path,
        default=None,
        help="Override the committed Lean-certified bench export.",
    )
    parser.add_argument(
        "--isabelle-certified",
        type=Path,
        default=None,
        help="Override the committed Isabelle-certified bench export.",
    )
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    config = FAMILIES[args.family]
    cons_path = args.consolidated or config.consolidated_path
    output = args.output or config.output

    cons = load_results(cons_path)
    lean = collect_series(cons, config.lean_pattern, "Lean native")
    isabelle = collect_series(cons, config.isabelle_pattern, "Isabelle native")
    fpll = collect_series(cons, config.fpll_pattern, "fpLLL via fplll-ffi")

    # Legend follows plot order; order the series slowest-to-fastest at large
    # n (Isabelle native, Lean native, Isabelle certified, Lean certified,
    # fpLLL) so the legend reads top-to-bottom like the stacked curves.
    series = [isabelle, lean]
    if config.include_certified:
        certified_results = load_results(args.certified or config.certified_path)
        certified = collect_series(
            certified_results, config.certified_pattern, "Lean certified"
        )
        isabelle_certified_results = load_results(
            args.isabelle_certified or config.isabelle_certified_path
        )
        isabelle_certified = collect_series(
            isabelle_certified_results,
            config.isabelle_certified_pattern,
            "Isabelle certified",
        )
        series += [isabelle_certified, certified]
    series.append(fpll)

    if config.bottom_consistency:
        isabelle_bottom_results = load_results(args.isabelle_bottom)
        assert_bottom_consistent(isabelle_bottom_results, isabelle)

    plot(series, output, config.title, config.xlabel)


if __name__ == "__main__":
    main()
