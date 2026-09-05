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
``MARGIN``: the required check that keeps the per-node factor from
growing with ``n``. Families with fewer sizes are reported but not
checked, and the check fails if no family qualifies. It is a growth
check, not a constant-factor check: a slowdown that is uniform in ``n``
is the per-library bench's business.

Without ``--sweep`` the script reads the sweep recorded for the current
source fingerprint (the one ``check_graphiso_sweep_freshness.py``
requires to exist), so CI never fits a sweep of some other source state.

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
sys.path.insert(0, str(ROOT))

from scripts.bench import sweep_freshness as freshness  # noqa: E402

RESULTS = freshness.RESULTS

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
    """The timed records of one sweep by family, each sorted by ``n``.

    Every record must carry positive ``fast_ns``, ``nauty_ns`` and
    ``nodes``, and no family may record the same ``n`` twice: a duplicate
    would reweight the fit, and a zero would break the logarithm.
    """
    families: dict[str, list[dict]] = defaultdict(list)
    seen: set[tuple[str, int]] = set()
    with path.open() as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            if "fast_ns" not in record or "nauty_ns" not in record:
                continue
            for field in ("fast_ns", "nauty_ns", "nodes"):
                if not isinstance(record.get(field), int) or record[field] <= 0:
                    sys.exit(f"{path.name}: {record.get('name')}: "
                             f"{field} must be a positive integer")
            key = (record["family"], record["n"])
            if key in seen:
                sys.exit(f"{path.name}: family {key[0]} records n = {key[1]} twice")
            seen.add(key)
            families[record["family"]].append(record)
    if not families:
        sys.exit(f"{path.name}: no timed records")
    for rows in families.values():
        rows.sort(key=lambda r: r["n"])
    return families


def current_sweep() -> Path:
    """The sweep covering the current source.

    A sweep recorded at the current fingerprint wins. Otherwise the same
    verdict as `check_graphiso_sweep_freshness.py` applies: when the
    source differs from the newest recorded sweep only in paths the
    freshness check exempts (a `.lean` file whose comments alone changed),
    that sweep still measures this source and the fit reads it.
    """
    from scripts.bench import check_graphiso_sweep_freshness as check
    found, errors = check.observations()
    verdict = freshness.assess(freshness.GRAPHISO, found,
                               allow=freshness.lean_comment_only)
    covering = verdict.matched or (verdict.baseline if verdict.fresh else None)
    if errors or covering is None:
        sys.exit(f"no recorded sweep covers the current source "
                 f"(fingerprint {verdict.fingerprint}); regenerate with "
                 f"scripts/bench/graphiso_cactus_sweep.sh")
    return RESULTS / covering.label


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
                        help="sweep jsonl (default: the one recorded for the "
                             "current source fingerprint)")
    parser.add_argument("--check", type=float, metavar="MARGIN",
                        help="fail if any checked family's hex exponent exceeds "
                             "nauty's by more than MARGIN")
    parser.add_argument("--min-sizes", type=int, default=5,
                        help="families with fewer distinct sizes are not checked")
    parser.add_argument("--out", type=Path,
                        help="also write the table to this file")
    args = parser.parse_args()

    sweep = args.sweep or current_sweep()
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
    checked = 0
    for row in table:
        if row["sizes"] < args.min_sizes:
            continue
        checked += 1
        if row["hex_exp"] - row["nauty_exp"] > args.check:
            failures.append(
                f"{row['family']}: hex n^{row['hex_exp']:.2f} exceeds nauty "
                f"n^{row['nauty_exp']:.2f} by more than {args.check}")
    if checked == 0:
        failures.append(f"no family has {args.min_sizes} sizes; nothing was checked")
    if failures:
        print("\nper-node exponent check failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1
    print(f"\nper-node exponent check passed (margin {args.check})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
