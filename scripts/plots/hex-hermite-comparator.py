#!/usr/bin/env python3
"""Render HexHermite Lean/FLINT/PARI fixed-comparator runtime plots."""

from __future__ import annotations

import argparse
import json
import math
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_INPUT = (
    REPO_ROOT
    / "reports"
    / "bench-results"
    / "hex-hermite-phase4-comparators.json"
)

FAMILIES: dict[str, str] = {
    "random-dense-hermite": "Dense",
    "rank-deficient-hermite": "Deficient",
    "tall-hermite": "Tall",
    "unimodular-conjugate": "Conjugate",
}
PARAMETERS = [16, 24, 32, 40, 48]
TOOLS = (
    ("Lean", "Hex", "#2864dc"),
    ("FLINT", "Flint", "#d62728"),
    ("PARI", "Pari", "#2ca02c"),
)


def _results(document: dict[str, Any]) -> dict[str, dict[str, Any]]:
    return {row["function"].rsplit(".", 1)[-1]: row for row in document["results"]}


def _load_family(
    document: dict[str, Any], family: str
) -> tuple[list[int], dict[str, list[float]]]:
    prefix = FAMILIES[family]
    rows = _results(document)
    overhead = {
        "FLINT": rows["runFlintOverhead"]["median_nanos"],
        "PARI": rows["runPariOverhead"]["median_nanos"],
    }
    series: dict[str, list[float]] = {label: [] for label, _, _ in TOOLS}
    eligible: list[int] = []
    for parameter in PARAMETERS:
        selected = {
            label: rows[f"run{stem}{prefix}{parameter}"]
            for label, stem, _ in TOOLS
        }
        observed = {row["observed_hash"] for row in selected.values()}
        if len(observed) != 1 or not all(row["hashes_agree"] for row in selected.values()):
            raise SystemExit(f"{family} n={parameter}: comparator hashes disagree")
        if any(
            selected[tool]["median_nanos"] < 2 * overhead[tool]
            for tool in ("FLINT", "PARI")
        ):
            continue
        if any(row["median_nanos"] > 10_000_000_000 for row in selected.values()):
            continue
        eligible.append(parameter)
        for tool, _, _ in TOOLS:
            series[tool].append(selected[tool]["median_nanos"] / 1_000_000)
    if len(eligible) < 2:
        raise SystemExit(f"{family}: fewer than two eligible comparator rungs")
    return eligible, series


def _render(family: str, parameters: list[int], series: dict[str, list[float]]) -> str:
    width, height = 760, 460
    left, right, top, bottom = 86, 28, 48, 72
    plot_w, plot_h = width - left - right, height - top - bottom
    values = [value for tool, _, _ in TOOLS for value in series[tool]]
    log_min = math.floor(math.log10(min(values)))
    log_max = math.ceil(math.log10(max(values)))
    if log_min == log_max:
        log_max += 1

    def x_at(index: int) -> float:
        return left + plot_w * index / max(1, len(parameters) - 1)

    def y_at(value: float) -> float:
        fraction = (math.log10(value) - log_min) / (log_max - log_min)
        return top + plot_h * (1 - fraction)

    out = [
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        '<rect width="100%" height="100%" fill="white"/>',
        f'<text x="{width / 2}" y="25" text-anchor="middle" font-family="sans-serif" font-size="17">HexHermite comparator runtimes: {family}</text>',
    ]
    for exponent in range(log_min, log_max + 1):
        value = 10.0**exponent
        y = y_at(value)
        out.append(f'<line x1="{left}" y1="{y:.2f}" x2="{left + plot_w}" y2="{y:.2f}" stroke="#dddddd"/>')
        out.append(f'<text x="{left - 10}" y="{y + 4:.2f}" text-anchor="end" font-family="sans-serif" font-size="12">10^{exponent} ms</text>')
    out.append(f'<line x1="{left}" y1="{top}" x2="{left}" y2="{top + plot_h}" stroke="#222"/>')
    out.append(f'<line x1="{left}" y1="{top + plot_h}" x2="{left + plot_w}" y2="{top + plot_h}" stroke="#222"/>')
    for index, parameter in enumerate(parameters):
        x = x_at(index)
        out.append(f'<line x1="{x:.2f}" y1="{top + plot_h}" x2="{x:.2f}" y2="{top + plot_h + 5}" stroke="#222"/>')
        out.append(f'<text x="{x:.2f}" y="{top + plot_h + 22}" text-anchor="middle" font-family="sans-serif" font-size="12">{parameter}</text>')
    out.append(f'<text x="{left + plot_w / 2}" y="{height - 18}" text-anchor="middle" font-family="sans-serif" font-size="13">matrix dimension n</text>')
    out.append(f'<text x="18" y="{top + plot_h / 2}" text-anchor="middle" transform="rotate(-90 18 {top + plot_h / 2})" font-family="sans-serif" font-size="13">median wall time per call (log scale)</text>')
    for tool, _, color in TOOLS:
        points = " ".join(
            f"{x_at(index):.2f},{y_at(value):.2f}"
            for index, value in enumerate(series[tool])
        )
        out.append(f'<polyline points="{points}" fill="none" stroke="{color}" stroke-width="2.5"/>')
        for index, value in enumerate(series[tool]):
            out.append(f'<circle cx="{x_at(index):.2f}" cy="{y_at(value):.2f}" r="3.5" fill="{color}"/>')
    for index, (tool, _, color) in enumerate(TOOLS):
        x = left + 12 + index * 112
        out.append(f'<line x1="{x}" y1="{top + 14}" x2="{x + 24}" y2="{top + 14}" stroke="{color}" stroke-width="3"/>')
        out.append(f'<text x="{x + 31}" y="{top + 18}" font-family="sans-serif" font-size="12">{tool}</text>')
    out.append("</svg>")
    return "\n".join(out) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", choices=sorted(FAMILIES), required=True)
    parser.add_argument("--input", type=Path, default=DEFAULT_INPUT)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    output = args.output or (
        REPO_ROOT / "reports" / "figures" / f"hex-hermite-comparator-{args.family}.svg"
    )
    document = json.loads(args.input.read_text())
    parameters, series = _load_family(document, args.family)
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(_render(args.family, parameters, series))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
