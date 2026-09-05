#!/usr/bin/env python3
"""Compare the two canonical searches from one ``hexgraphiso_cactus engine`` run.

The ``engine`` mode of the cactus driver times the literal port and the
second search on the same materialized instance and records both node
counts, one JSON line per instance::

    {"family": ..., "name": ..., "n": ..., "lit_ns": ..., "eng_ns": ...,
     "nauty_ns": ..., "nodes": ..., "eng_nodes": ...}

This script reads such a run and prints, per family, the geometric mean
of ``eng_ns/lit_ns`` and of ``eng_ns/nauty_ns``, and the per-node cost
exponents of both searches. The exponents come from
``graphiso_pernode_fit.fit_exponent``, on ``lit_ns/nodes`` and on
``eng_ns/eng_nodes`` against ``n``, so a constant-factor difference and a
difference that grows with ``n`` are reported apart.

Two searches with the same traversal visit the same nodes, so a record
whose ``eng_nodes`` differs from its ``nodes`` fails the run whatever the
timings say.

``--check`` additionally requires each family's geometric-mean
``eng_ns/lit_ns`` to be at most ``--max-mean``, every instance's ratio to
be at most ``--max-instance``, and each family's engine exponent to
exceed the literal exponent by at most ``--max-exponent``.
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

from scripts.bench.graphiso_pernode_fit import (  # noqa: E402
    fit_exponent,
    geometric_mean,
)

FIELDS = ("lit_ns", "eng_ns", "nauty_ns", "nodes", "eng_nodes")


def load(path: Path) -> dict[str, list[dict]]:
    """The timed records of one engine run by family, each sorted by ``n``."""
    families: dict[str, list[dict]] = defaultdict(list)
    with path.open() as fh:
        for line in fh:
            line = line.strip()
            if not line:
                continue
            record = json.loads(line)
            if "eng_ns" not in record:
                continue
            for field in FIELDS:
                if not isinstance(record.get(field), int) or record[field] <= 0:
                    sys.exit(f"{path.name}: {record.get('name')}: "
                             f"{field} must be a positive integer")
            families[record["family"]].append(record)
    if not families:
        sys.exit(f"{path.name}: no engine records")
    for rows in families.values():
        rows.sort(key=lambda r: r["n"])
    return families


def node_disagreements(families: dict[str, list[dict]]) -> list[str]:
    return [f"{r['name']}: nodes {r['nodes']} but eng_nodes {r['eng_nodes']}"
            for rows in families.values() for r in rows
            if r["nodes"] != r["eng_nodes"]]


def analyse(families: dict[str, list[dict]]) -> list[dict]:
    table = []
    for family, rows in sorted(families.items()):
        sizes = sorted({r["n"] for r in rows})
        lit_pts = [(r["n"], r["lit_ns"] / r["nodes"]) for r in rows]
        eng_pts = [(r["n"], r["eng_ns"] / r["eng_nodes"]) for r in rows]
        nan = (float("nan"), 0)
        lit_e, _ = fit_exponent(lit_pts) if len(sizes) >= 2 else nan
        eng_e, _ = fit_exponent(eng_pts) if len(sizes) >= 2 else nan
        ratios = [r["eng_ns"] / r["lit_ns"] for r in rows]
        table.append({
            "family": family,
            "sizes": len(sizes),
            "n_min": sizes[0],
            "n_max": sizes[-1],
            "lit_exp": lit_e,
            "eng_exp": eng_e,
            "over_lit": geometric_mean(ratios),
            "over_nauty": geometric_mean(
                [r["eng_ns"] / r["nauty_ns"] for r in rows]),
            "worst": max(ratios),
            "worst_name": max(rows, key=lambda r: r["eng_ns"] / r["lit_ns"])["name"],
        })
    return table


def fmt(x: float) -> str:
    return "-" if math.isnan(x) else f"{x:.2f}"


def render(sweep: Path, table: list[dict], families: dict[str, list[dict]]) -> str:
    rows = [r for rs in families.values() for r in rs]
    out = [f"engine comparison from {sweep.name}",
           "",
           "| family | sizes | n range | eng/lit | eng/nauty | lit n^e "
           "| eng n^e | diff | worst instance |",
           "|---|---|---|---|---|---|---|---|---|"]
    for row in table:
        diff = row["eng_exp"] - row["lit_exp"]
        out.append(
            f"| {row['family']} | {row['sizes']} | {row['n_min']}–{row['n_max']} "
            f"| {fmt(row['over_lit'])} | {fmt(row['over_nauty'])} "
            f"| {fmt(row['lit_exp'])} | {fmt(row['eng_exp'])} | {fmt(diff)} "
            f"| {row['worst_name']} {fmt(row['worst'])} |")
    out.append("")
    out.append("overall (geometric mean): eng/lit "
               f"{fmt(geometric_mean([r['eng_ns'] / r['lit_ns'] for r in rows]))}"
               ", eng/nauty "
               f"{fmt(geometric_mean([r['eng_ns'] / r['nauty_ns'] for r in rows]))}")
    return "\n".join(out)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__.split("\n\n")[0])
    parser.add_argument("sweep", type=Path,
                        help="jsonl written by `hexgraphiso_cactus engine`")
    parser.add_argument("--check", action="store_true",
                        help="fail on a family or instance outside the bounds")
    parser.add_argument("--max-mean", type=float, default=1.00,
                        help="largest accepted per-family geometric mean eng/lit")
    parser.add_argument("--max-instance", type=float, default=1.05,
                        help="largest accepted single-instance eng/lit")
    parser.add_argument("--max-exponent", type=float, default=0.02,
                        help="largest accepted engine minus literal exponent")
    parser.add_argument("--out", type=Path, help="also write the table here")
    args = parser.parse_args()

    families = load(args.sweep)
    table = analyse(families)
    text = render(args.sweep, table, families)
    print(text)
    if args.out:
        args.out.write_text(text + "\n")

    failures = node_disagreements(families)
    if args.check:
        for row in table:
            if row["over_lit"] > args.max_mean:
                failures.append(
                    f"{row['family']}: geometric mean eng/lit "
                    f"{row['over_lit']:.2f} exceeds {args.max_mean}")
            if row["worst"] > args.max_instance:
                failures.append(
                    f"{row['worst_name']}: eng/lit {row['worst']:.2f} exceeds "
                    f"{args.max_instance}")
            diff = row["eng_exp"] - row["lit_exp"]
            if diff > args.max_exponent:
                failures.append(
                    f"{row['family']}: engine exponent exceeds the literal "
                    f"port's by {diff:.2f}, more than {args.max_exponent}")
    if failures:
        print("\nengine comparison failed:")
        for failure in failures:
            print(f"  - {failure}")
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
