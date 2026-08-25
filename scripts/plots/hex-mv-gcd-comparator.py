#!/usr/bin/env python3
"""Generate HexMvGcd comparator plots from the committed fixed export."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from html import escape
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
EXPORT = (
    ROOT
    / "reports/bench-results/hex-mv-gcd-comparators-9f668741-chungus2.json"
)
PREFIX = "Hex.MvGcdBench.ComparatorCases.run"


@dataclass(frozen=True)
class Family:
    title: str
    endpoints: tuple[tuple[str, str], tuple[str, str]]


FAMILIES = {
    "coprime-pairs": Family(
        "Coprime pairs",
        (("dense, 2 variables", "CoprimeDense2"),
         ("sparse, 8 variables", "CoprimeSparse8")),
    ),
    "dense-gcds": Family(
        "Dense GCDs (degree 5)",
        (("3 variables", "Dense3d5"), ("4 variables", "Dense4d5")),
    ),
    "sparse-stress": Family(
        "Sparse stress (5 variables)",
        (("degree 4", "Sparse5d4"), ("degree 16", "Sparse5d16")),
    ),
    "swell": Family(
        "Coefficient swell",
        (("degree 3", "Swell3"), ("degree 5", "Swell5")),
    ),
    "rational": Family(
        "Rational GCDs (degree 5)",
        (("3 variables", "Rational3d5"),
         ("4 variables", "Rational4d5")),
    ),
    "squarefree": Family(
        "Squarefree decomposition",
        (("2 variables, m=1", "Squarefree2m1"),
         ("4 variables, m=7", "Squarefree4m7")),
    ),
    "cofactor-heavy": Family(
        "Cofactor-heavy exact division",
        (("degree 16", "Cofactor16"), ("degree 64", "Cofactor64")),
    ),
}

ARMS = (
    ("Hex", "Lean", "#2468b4", "circle"),
    ("FLINT 3.6.0", "Flint", "#d95f02", "square"),
    ("Singular 4.4.1", "Singular", "#249148", "triangle"),
)


def medians() -> dict[str, float]:
    data = json.loads(EXPORT.read_text(encoding="utf-8"))
    return {
        result["function"]: float(result["median_nanos"]) / 1_000_000_000
        for result in data["results"]
    }


def render_svg(family: Family, values: dict[str, float]) -> str:
    width, height = 900, 560
    left, right, top, bottom = 108, 30, 62, 92
    plot_width = width - left - right
    plot_height = height - top - bottom
    x_positions = (left + plot_width * 0.25, left + plot_width * 0.75)

    series: list[tuple[str, str, str, list[float]]] = []
    for label, target_prefix, color, marker in ARMS:
        ys = [
            values[PREFIX + target_prefix + target_suffix]
            for _, target_suffix in family.endpoints
        ]
        series.append((label, color, marker, ys))

    all_y = [value for _, _, _, ys in series for value in ys]
    ymin_power = math.floor(math.log10(min(all_y)))
    ymax_power = math.ceil(math.log10(max(all_y)))
    if ymin_power == ymax_power:
        ymax_power += 1
    ymin, ymax = 10.0**ymin_power, 10.0**ymax_power

    def y_position(value: float) -> float:
        span = math.log10(ymax) - math.log10(ymin)
        return top + (math.log10(ymax) - math.log10(value)) / span * plot_height

    lines = [
        '<svg xmlns="http://www.w3.org/2000/svg" '
        f'width="{width}" height="{height}" viewBox="0 0 {width} {height}">',
        "<style>",
        "text { font-family: sans-serif; fill: #202124; }",
        ".grid { stroke: #cfd4da; stroke-width: 1; opacity: 0.65; }",
        ".axis { stroke: #202124; stroke-width: 1.4; }",
        ".series { fill: none; stroke-width: 2.5; }",
        "</style>",
        f'<text x="{width / 2}" y="30" text-anchor="middle" '
        f'font-size="19" font-weight="600">HexMvGcd comparators — '
        f'{escape(family.title)} (chungus2)</text>',
        f'<rect x="{left}" y="{top}" width="{plot_width}" '
        f'height="{plot_height}" fill="#ffffff"/>',
    ]

    for power in range(ymin_power, ymax_power + 1):
        tick = 10.0**power
        y = y_position(tick)
        lines.extend(
            [
                f'<line class="grid" x1="{left}" y1="{y:.2f}" '
                f'x2="{left + plot_width}" y2="{y:.2f}"/>',
                f'<text x="{left - 12}" y="{y + 4:.2f}" '
                f'text-anchor="end" font-size="12">10^{power}</text>',
            ]
        )

    for x, (label, _) in zip(x_positions, family.endpoints, strict=True):
        lines.extend(
            [
                f'<line class="grid" x1="{x:.2f}" y1="{top}" '
                f'x2="{x:.2f}" y2="{top + plot_height}"/>',
                f'<text x="{x:.2f}" y="{top + plot_height + 25}" '
                f'text-anchor="middle" font-size="12">{escape(label)}</text>',
            ]
        )

    lines.extend(
        [
            f'<line class="axis" x1="{left}" y1="{top + plot_height}" '
            f'x2="{left + plot_width}" y2="{top + plot_height}"/>',
            f'<line class="axis" x1="{left}" y1="{top}" '
            f'x2="{left}" y2="{top + plot_height}"/>',
            f'<text x="{left + plot_width / 2}" y="{height - 25}" '
            'text-anchor="middle" font-size="14">matched endpoint</text>',
            f'<text x="25" y="{top + plot_height / 2}" '
            'text-anchor="middle" font-size="14" '
            f'transform="rotate(-90 25 {top + plot_height / 2})">'
            "wall time per call (s)</text>",
        ]
    )

    for index, (label, color, marker, ys) in enumerate(series):
        points = " ".join(
            f"{x:.2f},{y_position(y):.2f}"
            for x, y in zip(x_positions, ys, strict=True)
        )
        lines.append(
            f'<polyline class="series" stroke="{color}" points="{points}"/>'
        )
        for x, value in zip(x_positions, ys, strict=True):
            y = y_position(value)
            if marker == "circle":
                shape = f'<circle cx="{x:.2f}" cy="{y:.2f}" r="4" fill="{color}"/>'
            elif marker == "square":
                shape = (
                    f'<rect x="{x - 4:.2f}" y="{y - 4:.2f}" width="8" '
                    f'height="8" fill="{color}"/>'
                )
            else:
                shape = (
                    f'<polygon points="{x:.2f},{y - 5:.2f} '
                    f'{x - 5:.2f},{y + 4:.2f} {x + 5:.2f},{y + 4:.2f}" '
                    f'fill="{color}"/>'
                )
            lines.append(shape)
        legend_x = left + 18
        legend_y = top + 20 + index * 24
        lines.extend(
            [
                f'<line x1="{legend_x}" y1="{legend_y}" '
                f'x2="{legend_x + 28}" y2="{legend_y}" '
                f'stroke="{color}" stroke-width="2.5"/>',
                f'<text x="{legend_x + 38}" y="{legend_y + 4}" '
                f'font-size="12">{escape(label)}</text>',
            ]
        )

    lines.append("</svg>")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--family", required=True, choices=sorted(FAMILIES))
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    output = args.out or (
        ROOT / "reports/figures" / f"hex-mv-gcd-comparator-{args.family}.svg"
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        render_svg(FAMILIES[args.family], medians()), encoding="utf-8"
    )
    print(f"wrote {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
