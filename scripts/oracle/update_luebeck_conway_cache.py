#!/usr/bin/env python3
"""Regenerate the committed Lübeck Conway cache subset.

The source file uses GAP-style assignment syntax whose right-hand side
is Python-literal compatible for the entry list.  This script keeps a
per-prime slice of it, described by ``SLICE`` below (``prime -> maximum
degree``, all *available* degrees ``n`` with ``1 <= n <= max`` kept, so
gaps in Lübeck's tables are tolerated).

The slice serves two consumers:

* the ``conway_luebeck.py`` conformance oracle, which only needs the CI
  core ``p in {2,3,5,7,11,13}``, ``n in {1..6}``; and
* the ``conway`` factorization corpus family
  (``scripts/bench/gen_factor_corpus.py``), which lifts every cached
  entry to a monic integer polynomial.  The slice therefore sweeps both
  the degree axis (small primes to high degree) and the coefficient
  height axis (high primes at low degree).

Editing ``SLICE`` and re-running this script (network required, reads
Lübeck's table) is the single source of truth for both; regenerate the
corpus afterwards with ``scripts/bench/gen_factor_corpus.py``.
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

# prime -> maximum degree kept (all available n in 1..max are included).
# Small primes sweep the degree axis at low coefficient height; high primes
# sweep the height axis at low degree (a Conway polynomial mod p has height
# up to p - 1). The CI core p in {2,3,5,7,11,13}, n in {1..6} is a subset.
SLICE: dict[int, int] = {
    2: 40,
    3: 40,
    5: 40,
    7: 40,
    11: 8,
    13: 8,
    97: 8,
    521: 8,
    65537: 8,
}

DEFAULT_OUTPUT = Path(__file__).with_name("luebeck_conway_cache.json")


def _load_source(url: str) -> list[Any]:
    raw = urllib.request.urlopen(url, timeout=60).read().decode("latin1")
    start = raw.index("[")
    end = raw.rindex("]")
    return ast.literal_eval(raw[start : end + 1])


def build_cache(source: str, slice_spec: dict[int, int]) -> dict[str, Any]:
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
        if p not in slice_spec or n > slice_spec[p]:
            continue
        if not all(isinstance(c, int) for c in coeffs):
            raise ValueError(f"non-integer coefficient in entry {(p, n)}: {coeffs}")
        if len(coeffs) != n + 1 or coeffs[-1] != 1:
            raise ValueError(f"bad monic coefficient shape for entry {(p, n)}: {coeffs}")
        entries_by_key[(p, n)] = coeffs

    # Every prime in the slice must contribute at least its degree-1 entry;
    # a totally-absent prime is a typo in SLICE, not a Lübeck gap.
    missing_primes = sorted(p for p in slice_spec if not any(k[0] == p for k in entries_by_key))
    if missing_primes:
        raise ValueError(f"source has no entries for primes {missing_primes}")

    keys = sorted(entries_by_key)
    primes = sorted(slice_spec)
    degrees = sorted({n for _, n in keys})
    return {
        "coefficient_order": "ascending",
        "degrees": degrees,
        "entries": [
            {"p": p, "n": n, "coeffs": entries_by_key[(p, n)]} for p, n in keys
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

    cache = build_cache(args.source, SLICE)
    args.output.write_text(format_cache(cache))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
