#!/usr/bin/env python3
"""Per-node cost exponents of hex and nauty from a recorded cactus sweep.

``canonicalize`` runs nauty's search tree node for node (conformance pins
the node counts), so the hex/nauty ratio is a per-node constant factor and
the only question about the implementation's asymptotics is how that
factor moves with ``n``. This script reads one sweep
(``reports/bench-results/hexgraphiso-cactus-<fp>-<host>.jsonl``), divides
each instance's wallclock by its visited-node count (Kneser and Johnson
node counts grow with ``n``, so raw wallclock would conflate tree size
with per-node work), fits ``log(cost) = a + e·log(n)`` per family for hex
and for nauty by least squares, and prints the exponents with the ratio
``X = hex/nauty`` in the ``n ≤ 64`` and ``n > 64`` slices.

``--check MARGIN`` exits non-zero when, on any family with at least
``--min-sizes`` sizes, the hex exponent exceeds nauty's by more than
``MARGIN``: the required check that keeps an elementwise loop from
creeping back into the packed-word search. Families with fewer sizes are
reported but not checked.

The fit needs no numpy: it is the closed-form two-parameter least-squares
solution on the logarithms.
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
RESULTS = ROOT / "reports" / "bench-results"

SPLIT = 64


def fit_exponent(points: list[tuple[float, float]]) -> tuple[float, float]:
    """Least-squares slope and intercept of ``log y`` against ``log x``."""
    xs = [math.log(x) for x, _ in points]
    ys = [math.log(y) for _, y in points]
    k = len(xs)
    mx = sum(xs) / k
    my = sum(ys) / k
    sxx = sum((x - mx) ** 2 for x in xs)
    if sxx == 0:
        return float("nan"), my
    slope = sum((x - mx) * (y - my) for x, y in zip(xs, ys)) / sxx
    return slope, my - slope * mx


def geometric_mean(values: list[float]) -> float:
    if not values:
        return float("nan")
    return math.exp(sum(math.log(v) for v in values) / len(values))


def load_sweep(path: Path) -> dict[str, list[dict]]:
    families: dict[str, list[dict]] = defaultdict(list)
    with path.open() as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            if "fast_ns" not in record or "nauty_ns" not in record:
                continue
            families[record["family"]].append(record)
    for rows in families.values():
        rows.sort(key=lambda r: r["n"])
    return families


def latest_sweep() -> Path:
    metas = sorted(RESULTS.glob("hexgraphiso-cactus-*.meta.json"),
                   key=lambda p: json.loads(p.read_text())["date"])
    if not metas:
        sys.exit("no recorded sweep under reports/bench-results/")
    name = metas[-1].name.replace(".meta.json", ".jsonl")
    return metas[-1].with_name(name)


def analyse(families: dict[str, list[dict]]) -> list[dict]:
    table = []
    for family, rows in sorted(families.items()):
        hex_pts = [(r["n"], r["fast_ns"] / r["nodes"]) for r in rows]
        nauty_pts = [(r["n"], r["nauty_ns"] / r["nodes"]) for r in rows]
        sizes = sorted({r["n"] for r in rows})
        hex_e, _ = fit_exponent(hex_pts) if len(sizes) >= 2 else (float("nan"), 0)
        nauty_e, _ = fit_exponent(nauty_pts) if len(sizes) >= 2 else (float("nan"), 0)
        ratios_lo = [r["fast_ns"] / r["nauty_ns"] for r in rows if r["n"] <= SPLIT]
        ratios_hi = [r["fast_ns"] / r["nauty_ns"] for r in rows if r["n"] > SPLIT]
        table.append({
            "family": family,
            "sizes": len(sizes),
            "n_min": sizes[0],
            "n_max": sizes[-1],
            "hex_exp": hex_e,
            "nauty_exp": nauty_e,
            "x_lo": geometric_mean(ratios_lo),
            "x_hi": geometric_mean(ratios_hi),
        })
    return table


def overall(families: dict[str, list[dict]]) -> tuple[float, float]:
    rows = [r for rs in families.values() for r in rs]
    lo = [r["fast_ns"] / r["nauty_ns"] for r in rows if r["n"] <= SPLIT]
    hi = [r["fast_ns"] / r["nauty_ns"] for r in rows if r["n"] > SPLIT]
    return geometric_mean(lo), geometric_mean(hi)


def fmt(x: float) -> str:
    return "-" if math.isnan(x) else f"{x:.2f}"


def render(sweep: Path, table: list[dict], x_lo: float, x_hi: float) -> str:
    out = [f"per-node cost fit from {sweep.name}",
           "",
           "| family | sizes | n range | hex n^e | nauty n^e | diff | X (n ≤ 64) | X (n > 64) |",
           "|---|---|---|---|---|---|---|---|"]
    for row in table:
        diff = row["hex_exp"] - row["nauty_exp"]
        out.append(
            f"| {row['family']} | {row['sizes']} | {row['n_min']}–{row['n_max']} "
            f"| {fmt(row['hex_exp'])} | {fmt(row['nauty_exp'])} | {fmt(diff)} "
            f"| {fmt(row['x_lo'])} | {fmt(row['x_hi'])} |")
    out.append("")
    out.append(f"overall X (geometric mean): n ≤ 64: {fmt(x_lo)}, n > 64: {fmt(x_hi)}")
    return "\n".join(out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("--sweep", type=Path,
                        help="sweep jsonl (default: the most recently recorded)")
    parser.add_argument("--check", type=float, metavar="MARGIN",
                        help="fail if any checked family's hex exponent exceeds "
                             "nauty's by more than MARGIN")
    parser.add_argument("--min-sizes", type=int, default=5,
                        help="families with fewer distinct sizes are not checked")
    parser.add_argument("--out", type=Path,
                        help="also write the table to this file")
    args = parser.parse_args()

    sweep = args.sweep or latest_sweep()
    families = load_sweep(sweep)
    table = analyse(families)
    x_lo, x_hi = overall(families)
    text = render(sweep, table, x_lo, x_hi)
    print(text)
    if args.out:
        args.out.write_text(text + "\n")

    if args.check is None:
        return 0
    failures = []
    for row in table:
        if row["sizes"] < args.min_sizes:
            continue
        if row["hex_exp"] - row["nauty_exp"] > args.check:
            failures.append(
                f"{row['family']}: hex n^{row['hex_exp']:.2f} exceeds nauty "
                f"n^{row['nauty_exp']:.2f} by more than {args.check}")
    if failures:
        print("\nper-node exponent check failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1
    print(f"\nper-node exponent check passed (margin {args.check})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
