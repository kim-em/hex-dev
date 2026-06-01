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
DEFAULT_DENSIFIED = ROOT / "reports/bench-results/hex-lll-densified-fa57a699.json"
DEFAULT_FPYLLL = ROOT / "reports/bench-results/hex-lll-fpylll-ed9da7537e96.json"
DEFAULT_ISABELLE_BOTTOM = (
    ROOT / "reports/bench-results/hex-lll-isabelle-bottom-e211854d1435.json"
)
DEFAULT_OUTPUT = ROOT / "reports/figures/hex-lll-comparator.svg"

LEAN_RANDOM = re.compile(r"runFirstShortVectorRandomBoundedNormSq([0-9]+)$")
ISABELLE_RANDOM = re.compile(r"runIsabelleRandomBoundedNormSq([0-9]+)$")
FPYLLL_RANDOM = re.compile(r"runFpylllFirstShortVectorRandomBounded([0-9]+)Checksum$")


@dataclass(frozen=True)
class Series:
    label: str
    xs: list[int]
    ys: list[float]


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
        raise ValueError(f"no random-bounded results found for {label}")
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


def plot(series: list[Series], output: Path) -> None:
    fig, ax = plt.subplots(figsize=(7.2, 4.8))
    styles = [
        {"marker": "o", "linewidth": 2.0},
        {"marker": "s", "linewidth": 2.0},
        {"marker": "^", "linewidth": 0.0, "markersize": 7.0},
    ]
    for item, style in zip(series, styles, strict=True):
        ax.plot(item.xs, [y / 1000.0 for y in item.ys], label=item.label, **style)

    ax.set_title("HexLLL random-bounded comparator runtime")
    ax.set_xlabel("random-bounded dimension n")
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
        description="Generate reports/figures/hex-lll-comparator.svg."
    )
    parser.add_argument("--densified", type=Path, default=DEFAULT_DENSIFIED)
    parser.add_argument("--fpylll", type=Path, default=DEFAULT_FPYLLL)
    parser.add_argument(
        "--isabelle-bottom", type=Path, default=DEFAULT_ISABELLE_BOTTOM
    )
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    densified_results = load_results(args.densified)
    fpylll_results = load_results(args.fpylll)
    isabelle_bottom_results = load_results(args.isabelle_bottom)

    lean = collect_series(densified_results, LEAN_RANDOM, "Lean")
    isabelle = collect_series(
        densified_results, ISABELLE_RANDOM, "verified Isabelle LLL"
    )
    fpylll = collect_series(fpylll_results, FPYLLL_RANDOM, "fpLLL via fpylll")
    assert_bottom_consistent(isabelle_bottom_results, isabelle)

    plot([lean, isabelle, fpylll], args.output)


if __name__ == "__main__":
    main()
