#!/usr/bin/env python3
"""Generate HexMvPoly native-comparator plots from committed exports."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from html import escape
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
HEX_EXPORT = (
    ROOT / "reports/bench-results/hex-mv-poly-native-163e100c-chungus2.json"
)
COMPPOLY_EXPORT = (
    ROOT / "reports/bench-results/hex-mv-poly-comppoly-a7430482-chungus2.json"
)
SORTED_EXPORT = (
    ROOT
    / "reports/bench-results/hex-mv-poly-sorted-proxy-a7430482-chungus2.json"
)


@dataclass(frozen=True)
class Family:
    hex_target: str
    comppoly_target: str
    sorted_target: str
    title: str


FAMILIES = {
    "sparse-addition": Family(
        "Hex.MvPolyBench.runSparseAdditionLex",
        "CompPoly.MvPolyBench.runSparseAddition",
        "MvSparsePolyProxy.MvPolyBench.runSparseAddition",
        "Sparse addition",
    ),
    "sparse-multiplication": Family(
        "Hex.MvPolyBench.runSparseMultiplicationLow",
        "CompPoly.MvPolyBench.runSparseMultiplication",
        "MvSparsePolyProxy.MvPolyBench.runSparseMultiplication",
        "Low-collision sparse multiplication",
    ),
    "cancellation-arithmetic": Family(
        "Hex.MvPolyBench.runCancellationInt",
        "CompPoly.MvPolyBench.runCancellationArithmetic",
        "MvSparsePolyProxy.MvPolyBench.runCancellationArithmetic",
        "Cancellation-heavy integer arithmetic",
    ),
    "structural-collisions": Family(
        "Hex.MvPolyBench.runRenameCollisions",
        "CompPoly.MvPolyBench.runStructuralCollisions",
        "MvSparsePolyProxy.MvPolyBench.runStructuralCollisions",
        "Collision-heavy rename",
    ),
    "sum-of-squares-arithmetic": Family(
        "Hex.MvPolyBench.runSumOfSquaresArithmetic",
        "CompPoly.MvPolyBench.runSumOfSquaresArithmetic",
        "MvSparsePolyProxy.MvPolyBench.runSumOfSquaresArithmetic",
        "Sum-of-squares arithmetic",
    ),
}


def load_series(path: Path, target: str) -> tuple[list[int], list[float]]:
    data = json.loads(path.read_text(encoding="utf-8"))
    matches = [
        result for result in data["results"] if result["function"] == target
    ]
    if len(matches) != 1:
        raise RuntimeError(f"{path}: expected one result for {target}")
    summaries = matches[0]["trial_summaries"]
    xs = [int(row["param"]) for row in summaries]
    ys = [float(row["median_per_call_nanos"]) / 1_000_000_000 for row in summaries]
    if len(xs) < 2:
        raise RuntimeError(f"{path}: {target} has fewer than two data points")
    return xs, ys


def render_svg(
    title: str,
    series: tuple[tuple[str, str, tuple[list[int], list[float]]], ...],
) -> str:
    width, height = 900, 560
    left, right, top, bottom = 90, 30, 62, 78
    plot_width = width - left - right
    plot_height = height - top - bottom
    all_x = [x for _, _, (xs, _) in series for x in xs]
    all_y = [y for _, _, (_, ys) in series for y in ys]
    xmin, xmax = min(all_x), max(all_x)
    ymin_power = math.floor(math.log10(min(all_y)))
    ymax_power = math.ceil(math.log10(max(all_y)))
    ymin = 10.0 ** ymin_power
    ymax = 10.0 ** ymax_power

    def x_position(value: int) -> float:
        span = math.log2(xmax) - math.log2(xmin)
        return left + (math.log2(value) - math.log2(xmin)) / span * plot_width

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
        f'font-size="19" font-weight="600">{escape(title)}</text>',
        f'<rect x="{left}" y="{top}" width="{plot_width}" '
        f'height="{plot_height}" fill="#ffffff"/>',
    ]

    x_ticks: list[int] = []
    power = math.ceil(math.log2(xmin))
    while 2**power <= xmax:
        x_ticks.append(2**power)
        power += 1
    for tick in x_ticks:
        x = x_position(tick)
        lines.extend(
            [
                f'<line class="grid" x1="{x:.2f}" y1="{top}" '
                f'x2="{x:.2f}" y2="{top + plot_height}"/>',
                f'<text x="{x:.2f}" y="{top + plot_height + 24}" '
                f'text-anchor="middle" font-size="12">{tick}</text>',
            ]
        )
    for power in range(ymin_power, ymax_power + 1):
        tick = 10.0**power
        y = y_position(tick)
        label = f"10^{power}"
        lines.extend(
            [
                f'<line class="grid" x1="{left}" y1="{y:.2f}" '
                f'x2="{left + plot_width}" y2="{y:.2f}"/>',
                f'<text x="{left - 12}" y="{y + 4:.2f}" '
                f'text-anchor="end" font-size="12">{label}</text>',
            ]
        )

    lines.extend(
        [
            f'<line class="axis" x1="{left}" y1="{top + plot_height}" '
            f'x2="{left + plot_width}" y2="{top + plot_height}"/>',
            f'<line class="axis" x1="{left}" y1="{top}" '
            f'x2="{left}" y2="{top + plot_height}"/>',
            f'<text x="{left + plot_width / 2}" y="{height - 22}" '
            'text-anchor="middle" font-size="14">source terms n</text>',
            f'<text x="22" y="{top + plot_height / 2}" '
            'text-anchor="middle" font-size="14" '
            f'transform="rotate(-90 22 {top + plot_height / 2})">'
            "wall time per call (s)</text>",
        ]
    )

    palette = ("#2468b4", "#d95f02", "#249148")
    for index, (label, marker, (xs, ys)) in enumerate(series):
        color = palette[index]
        points = " ".join(
            f"{x_position(x):.2f},{y_position(y):.2f}"
            for x, y in zip(xs, ys, strict=True)
        )
        lines.append(
            f'<polyline class="series" stroke="{color}" points="{points}"/>'
        )
        for x_value, y_value in zip(xs, ys, strict=True):
            x, y = x_position(x_value), y_position(y_value)
            if marker == "circle":
                shape = (
                    f'<circle cx="{x:.2f}" cy="{y:.2f}" r="4" '
                    f'fill="{color}"/>'
                )
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

    family = FAMILIES[args.family]
    series = (
        (
            "Hex ExtTreeMap",
            "circle",
            load_series(HEX_EXPORT, family.hex_target),
        ),
        (
            "CompPoly CMvPolynomial",
            "square",
            load_series(COMPPOLY_EXPORT, family.comppoly_target),
        ),
        (
            "sorted-list MvSparsePoly proxy",
            "triangle",
            load_series(SORTED_EXPORT, family.sorted_target),
        ),
    )

    output = args.out or (
        ROOT / "reports/figures" / f"hex-mv-poly-comparator-{args.family}.svg"
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        render_svg(
            f"HexMvPoly comparators — {family.title} (chungus2)",
            series,
        ),
        encoding="utf-8",
    )
    print(f"wrote {output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
