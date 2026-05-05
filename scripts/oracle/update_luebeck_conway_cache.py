#!/usr/bin/env python3
"""Regenerate the committed Lübeck Conway cache subset.

The source file uses GAP-style assignment syntax whose right-hand side
is Python-literal compatible for the entry list.  This script keeps only
the small project slice used by CI: ``p in {2,3,5,7,11,13}`` and
``n in {1..6}``.
"""
from __future__ import annotations

import argparse
import ast
import json
import urllib.request
from pathlib import Path
from typing import Any


DEFAULT_SOURCE = (
    "http://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/CPimport.txt"
)
DEFAULT_PRIMES = [2, 3, 5, 7, 11, 13]
DEFAULT_DEGREES = [1, 2, 3, 4, 5, 6]
DEFAULT_OUTPUT = Path(__file__).with_name("luebeck_conway_cache.json")


def _load_source(url: str) -> list[Any]:
    raw = urllib.request.urlopen(url, timeout=60).read().decode("latin1")
    start = raw.index("[")
    end = raw.rindex("]")
    return ast.literal_eval(raw[start : end + 1])


def build_cache(source: str, primes: list[int], degrees: list[int]) -> dict[str, Any]:
    wanted = {(p, n) for p in primes for n in degrees}
    entries_by_key: dict[tuple[int, int], list[int]] = {}
    for item in _load_source(source):
        if not (
            isinstance(item, list)
            and len(item) == 3
            and isinstance(item[0], int)
            and isinstance(item[1], int)
            and isinstance(item[2], list)
        ):
            continue
        p, n, coeffs = item
        if (p, n) not in wanted:
            continue
        if not all(isinstance(c, int) for c in coeffs):
            raise ValueError(f"non-integer coefficient in entry {(p, n)}: {coeffs}")
        if len(coeffs) != n + 1 or coeffs[-1] != 1:
            raise ValueError(f"bad monic coefficient shape for entry {(p, n)}: {coeffs}")
        entries_by_key[(p, n)] = coeffs

    missing = sorted(wanted - entries_by_key.keys())
    if missing:
        raise ValueError(f"source is missing requested entries: {missing}")

    return {
        "coefficient_order": "ascending",
        "degrees": degrees,
        "entries": [
            {"p": p, "n": n, "coeffs": entries_by_key[(p, n)]}
            for p in primes
            for n in degrees
        ],
        "primes": primes,
        "source": source,
    }


def format_cache(cache: dict[str, Any]) -> str:
    lines = [
        "{",
        '  "coefficient_order": "ascending",',
        f'  "degrees": {json.dumps(cache["degrees"])},',
        '  "entries": [',
    ]
    entries = cache["entries"]
    for idx, entry in enumerate(entries):
        suffix = "," if idx + 1 < len(entries) else ""
        lines.append(
            "    "
            + json.dumps(entry, separators=(", ", ": "))
            + suffix
        )
    lines.extend(
        [
            "  ],",
            f'  "primes": {json.dumps(cache["primes"])},',
            f'  "source": {json.dumps(cache["source"])}',
            "}",
            "",
        ]
    )
    return "\n".join(lines)


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", default=DEFAULT_SOURCE)
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    cache = build_cache(args.source, DEFAULT_PRIMES, DEFAULT_DEGREES)
    args.output.write_text(format_cache(cache))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
