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
DEFAULT_DENSIFIED = ROOT / "reports/bench-results/hex-lll-setentry-modify-densified.json"
# Post-warmupFirstIter exports; supersede the pre-fix files whose
# subprocess-driver startup dominated small-n medians.
DEFAULT_FPYLLL_RANDOM = (
    ROOT / "reports/bench-results/hex-lll-fpylll-random-bounded-warmupfix.json"
)
DEFAULT_FPYLLL_HARSH = (
    ROOT / "reports/bench-results/hex-lll-harsh-cubic-extended-warmupfix.json"
)
DEFAULT_HARSH_LEAN_ISABELLE = (
    ROOT / "reports/bench-results/hex-lll-setentry-modify-harsh-cubic.json"
)
DEFAULT_ISABELLE = (
    ROOT / "reports/bench-results/hex-lll-isabelle-warmupfix.json"
)
DEFAULT_ISABELLE_BOTTOM = (
    ROOT / "reports/bench-results/hex-lll-isabelle-bottom-e211854d1435.json"
)
DEFAULT_RANDOM_OUTPUT = ROOT / "reports/figures/hex-lll-comparator-random-bounded.svg"
DEFAULT_HARSH_OUTPUT = ROOT / "reports/figures/hex-lll-comparator-harsh-cubic.svg"

LEAN_RANDOM = re.compile(r"runFirstShortVectorRandomBoundedNormSq([0-9]+)$")
ISABELLE_RANDOM = re.compile(r"runIsabelleRandomBoundedNormSq([0-9]+)$")
FPYLLL_RANDOM = re.compile(r"runFpylllFirstShortVectorRandomBounded([0-9]+)Checksum$")
LEAN_HARSH = re.compile(r"runFirstShortVectorHarshCubicNormSq([0-9]+)$")
ISABELLE_HARSH = re.compile(r"runIsabelleHarshCubicNormSq([0-9]+)$")
FPYLLL_HARSH = re.compile(r"runFpylllFirstShortVectorHarshCubic([0-9]+)Checksum$")


@dataclass(frozen=True)
class Series:
    label: str
    xs: list[int]
    ys: list[float]


@dataclass(frozen=True)
class FamilyConfig:
    lean_pattern: re.Pattern[str]
    isabelle_pattern: re.Pattern[str]
    fpylll_pattern: re.Pattern[str]
    fpylll_path: Path
    output: Path
    title: str
    xlabel: str
    # If set, read Lean and Isabelle from this single file instead of
    # the densified file + the standalone Isabelle export.
    consolidated_path: Path | None = None
    bottom_consistency: bool = False


FAMILIES = {
    "random-bounded": FamilyConfig(
        lean_pattern=LEAN_RANDOM,
        isabelle_pattern=ISABELLE_RANDOM,
        fpylll_pattern=FPYLLL_RANDOM,
        fpylll_path=DEFAULT_FPYLLL_RANDOM,
        output=DEFAULT_RANDOM_OUTPUT,
        title="HexLLL random-bounded comparator runtime",
        xlabel="random-bounded dimension n",
        bottom_consistency=True,
    ),
    "harsh-cubic": FamilyConfig(
        lean_pattern=LEAN_HARSH,
        isabelle_pattern=ISABELLE_HARSH,
        fpylll_pattern=FPYLLL_HARSH,
        fpylll_path=DEFAULT_FPYLLL_HARSH,
        output=DEFAULT_HARSH_OUTPUT,
        title="HexLLL harsh-cubic comparator runtime",
        xlabel="harsh-cubic dimension n",
        consolidated_path=DEFAULT_HARSH_LEAN_ISABELLE,
    ),
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
    styles = [
        {"marker": "o", "linewidth": 2.0},
        {"marker": "s", "linewidth": 2.0},
        {"marker": "^", "linewidth": 2.0, "markersize": 7.0},
    ]
    for item, style in zip(series, styles, strict=True):
        ax.plot(item.xs, [y / 1000.0 for y in item.ys], label=item.label, **style)

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
    parser.add_argument("--densified", type=Path, default=DEFAULT_DENSIFIED)
    parser.add_argument(
        "--fpylll",
        type=Path,
        default=None,
        help="Override the family-specific fpylll export.",
    )
    parser.add_argument(
        "--isabelle",
        type=Path,
        default=DEFAULT_ISABELLE,
        help="Isabelle export to use; defaults to the post-warmupFirstIter run.",
    )
    parser.add_argument(
        "--isabelle-bottom", type=Path, default=DEFAULT_ISABELLE_BOTTOM
    )
    parser.add_argument("--output", type=Path, default=None)
    args = parser.parse_args()
    config = FAMILIES[args.family]
    fpylll_path = args.fpylll or config.fpylll_path
    output = args.output or config.output

    fpylll_results = load_results(fpylll_path)
    if config.consolidated_path is not None:
        cons = load_results(config.consolidated_path)
        lean = collect_series(cons, config.lean_pattern, "Lean")
        isabelle = collect_series(cons, config.isabelle_pattern,
                                  "verified Isabelle LLL")
    else:
        densified_results = load_results(args.densified)
        isabelle_results = load_results(args.isabelle)
        lean = collect_series(densified_results, config.lean_pattern, "Lean")
        isabelle = collect_series(isabelle_results, config.isabelle_pattern,
                                  "verified Isabelle LLL")
    fpylll = collect_series(
        fpylll_results, config.fpylll_pattern, "fpLLL via fpylll"
    )
    if config.bottom_consistency:
        isabelle_bottom_results = load_results(args.isabelle_bottom)
        assert_bottom_consistent(isabelle_bottom_results, isabelle)

    plot([lean, isabelle, fpylll], output, config.title, config.xlabel)


if __name__ == "__main__":
    main()
