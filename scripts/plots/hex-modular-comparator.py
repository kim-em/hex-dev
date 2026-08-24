#!/usr/bin/env python3
"""Generate scoped HexModular comparator plots from committed exports."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
from html import escape
import json
import math
from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "reports/bench-results"


@dataclass(frozen=True)
class Family:
    title: str
    params: tuple[int, ...]
    lean_prefix: str | None
    lean_parametric: str | None
    comparator_prefix: str
    comparator_label: str


FAMILIES = {
    "incremental-crt": Family(
        "Incremental scalar CRT",
        (4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192),
        "Hex.ModularBench.Comparator.runLeanScalar",
        None,
        "Hex.ModularBench.Comparator.runFlintScalar",
        "python-flint fmpz CRT",
    ),
    "vector-crt": Family(
        "Fixed-depth vector CRT",
        (1, 4, 16, 64, 256, 1024, 2048, 4096),
        "Hex.ModularBench.Comparator.runLeanVector",
        None,
        "Hex.ModularBench.Comparator.runFlintVector",
        "python-flint fmpz CRT",
    ),
    "rational-reconstruction": Family(
        "Truncated Euclidean reconstruction",
        (
            64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384,
            32768, 65536, 100000, 131072, 196608, 262144,
        ),
        "Hex.ModularBench.Comparator.runLeanGcd",
        None,
        "Hex.ModularBench.Comparator.runGmpy2Gcd",
        "gmpy2.gcdext",
    ),
    "failure-cost": Family(
        "Failed rational reconstruction",
        (
            64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384,
            32768, 65536, 100000, 131072, 196608, 262144,
        ),
        None,
        "Hex.ModularBench.runRatReconFailure",
        "Hex.ModularBench.Comparator.runGmpy2Gcd",
        "gmpy2.gcdext",
    ),
}


def singleton_export(pattern: str) -> Path:
    matches = sorted(RESULTS.glob(pattern))
    if len(matches) != 1:
        raise RuntimeError(
            f"expected exactly one {pattern!r} export, found {len(matches)}"
        )
    return matches[0]


def read_export(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def result_by_name(data: dict, name: str) -> dict:
    matches = [row for row in data["results"] if row["function"] == name]
    if len(matches) != 1:
        raise RuntimeError(f"expected one result for {name}, found {len(matches)}")
    return matches[0]


def fixed_series(data: dict, prefix: str, params: tuple[int, ...]) -> dict[int, float]:
    series: dict[int, float] = {}
    for param in params:
        row = result_by_name(data, f"{prefix}{param}")
        if row.get("median_nanos") is None:
            raise RuntimeError(f"{prefix}{param} has no successful fixed median")
        if not row.get("hashes_agree", False):
            raise RuntimeError(f"{prefix}{param} has disagreeing repeat hashes")
        series[param] = float(row["median_nanos"]) / 1_000_000_000
    return series


def parametric_series(data: dict, name: str) -> dict[int, float]:
    row = result_by_name(data, name)
    return {
        int(summary["param"]):
            float(summary["median_per_call_nanos"]) / 1_000_000_000
        for summary in row["trial_summaries"]
    }


def select_ticks(values: list[int], limit: int = 7) -> list[int]:
    if len(values) <= limit:
        return values
    indices = {
        round(index * (len(values) - 1) / (limit - 1))
        for index in range(limit)
    }
    return [values[index] for index in sorted(indices)]


def render_svg(
    family: Family,
    params: list[int],
    lean: list[float],
    comparator: list[float],
    overhead: float,
) -> str:
    width, height = 900, 560
    left, right, top, bottom = 92, 28, 76, 76
    plot_width = width - left - right
    plot_height = height - top - bottom
    ymin_power = math.floor(math.log10(min(lean + comparator)))
    ymax_power = math.ceil(math.log10(max(lean + comparator)))
    ymin, ymax = 10.0 ** ymin_power, 10.0 ** ymax_power
    xmin, xmax = min(params), max(params)

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
        f'<text x="{width / 2}" y="28" text-anchor="middle" '
        f'font-size="19" font-weight="600">{escape(family.title)}</text>',
        f'<text x="{width / 2}" y="50" text-anchor="middle" font-size="12">'
        f'eligible range; persistent-call overhead {overhead * 1e6:.1f} µs</text>',
        f'<rect x="{left}" y="{top}" width="{plot_width}" '
        f'height="{plot_height}" fill="#ffffff"/>',
    ]

    for tick in select_ticks(params):
        x = x_position(tick)
        lines.extend(
            [
                f'<line class="grid" x1="{x:.2f}" y1="{top}" '
                f'x2="{x:.2f}" y2="{top + plot_height}"/>',
                f'<text x="{x:.2f}" y="{top + plot_height + 23}" '
                f'text-anchor="middle" font-size="11">{tick}</text>',
            ]
        )
    for power in range(ymin_power, ymax_power + 1):
        tick = 10.0 ** power
        y = y_position(tick)
        lines.extend(
            [
                f'<line class="grid" x1="{left}" y1="{y:.2f}" '
                f'x2="{left + plot_width}" y2="{y:.2f}"/>',
                f'<text x="{left - 12}" y="{y + 4:.2f}" '
                f'text-anchor="end" font-size="12">10^{power}</text>',
            ]
        )

    lines.extend(
        [
            f'<line class="axis" x1="{left}" y1="{top + plot_height}" '
            f'x2="{left + plot_width}" y2="{top + plot_height}"/>',
            f'<line class="axis" x1="{left}" y1="{top}" '
            f'x2="{left}" y2="{top + plot_height}"/>',
            f'<text x="{left + plot_width / 2}" y="{height - 20}" '
            'text-anchor="middle" font-size="14">benchmark parameter</text>',
            f'<text x="22" y="{top + plot_height / 2}" '
            'text-anchor="middle" font-size="14" '
            f'transform="rotate(-90 22 {top + plot_height / 2})">'
            "wall time per call (s)</text>",
        ]
    )

    for index, (label, values, color, square) in enumerate(
        (
            ("HexModular", lean, "#2468b4", False),
            (family.comparator_label, comparator, "#d95f02", True),
        )
    ):
        points = " ".join(
            f"{x_position(param):.2f},{y_position(value):.2f}"
            for param, value in zip(params, values, strict=True)
        )
        lines.append(
            f'<polyline class="series" stroke="{color}" points="{points}"/>'
        )
        for param, value in zip(params, values, strict=True):
            x, y = x_position(param), y_position(value)
            if square:
                lines.append(
                    f'<rect x="{x - 4:.2f}" y="{y - 4:.2f}" width="8" '
                    f'height="8" fill="{color}"/>'
                )
            else:
                lines.append(
                    f'<circle cx="{x:.2f}" cy="{y:.2f}" r="4" fill="{color}"/>'
                )
        legend_x, legend_y = left + 18, top + 20 + index * 24
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
    parser.add_argument("--native-export", type=Path)
    parser.add_argument("--comparator-export", type=Path)
    parser.add_argument("--out", type=Path)
    args = parser.parse_args()

    native_path = args.native_export or singleton_export("hex-modular-native-*.json")
    comparator_path = (
        args.comparator_export
        or singleton_export("hex-modular-comparators-*.json")
    )
    native = read_export(native_path)
    fixed = read_export(comparator_path)
    family = FAMILIES[args.family]
    if family.lean_prefix is not None:
        lean = fixed_series(fixed, family.lean_prefix, family.params)
    else:
        assert family.lean_parametric is not None
        lean = parametric_series(native, family.lean_parametric)
    comparator = fixed_series(fixed, family.comparator_prefix, family.params)
    overhead_row = result_by_name(
        fixed, "Hex.ModularBench.Comparator.runComparatorOverhead"
    )
    overhead = float(overhead_row["median_nanos"]) / 1_000_000_000

    eligible = [
        param for param in family.params
        if param in lean
        and comparator[param] >= 2.0 * overhead
        and lean[param] <= 10.0
        and comparator[param] <= 10.0
    ]
    if len(eligible) < 2:
        raise RuntimeError(
            f"{args.family} has only {len(eligible)} comparator-eligible rung(s)"
        )
    lean_values = [lean[param] for param in eligible]
    comparator_values = [comparator[param] for param in eligible]
    output = args.out or (
        ROOT / "reports/figures" / f"hex-modular-comparator-{args.family}.svg"
    )
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        render_svg(family, eligible, lean_values, comparator_values, overhead),
        encoding="utf-8",
    )
    print(
        f"wrote {output} from {native_path.name} and {comparator_path.name} "
        f"({len(eligible)} eligible rungs)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
