#!/usr/bin/env python3
"""Table-source Conway polynomial adapter for `hex-conway`.

This helper loads the standalone Python ``conway-polynomials`` package
and exposes Conway table lookup by ``(p, n)``.  Coefficients are returned
in the project/Luebeck convention ``[a0, a1, ..., 1]`` for
``a0 + a1*x + ... + x^n``.

This is intentionally only a table-source check: it validates Hex's
Lean/cache wiring against another packaged Conway table interface.  It
does not independently recompute Conway polynomial minimality,
primitivity, or compatibility.

Usage::

    python3 scripts/oracle/conway_polynomials_table.py 2 3
    python3 scripts/oracle/conway_polynomials_table.py --smoke

Install dependency::

    python3 -m pip install conway-polynomials
"""
from __future__ import annotations

import argparse
import json
import sys
from collections.abc import Mapping, Sequence
from typing import Any


SMOKE_CASES: dict[tuple[int, int], list[int]] = {
    (2, 1): [1, 1],
    (2, 3): [1, 1, 0, 1],
    (3, 2): [2, 2, 1],
}


class ConwayTableError(RuntimeError):
    """Raised when the runtime table package is missing or unusable."""


def _load_database() -> Mapping[int, Mapping[int, Sequence[int]]]:
    try:
        import conway_polynomials  # type: ignore[import-not-found]
    except ModuleNotFoundError as exc:
        raise ConwayTableError(
            "missing dependency: install the Python package "
            "`conway-polynomials` with `python3 -m pip install "
            "conway-polynomials`"
        ) from exc

    try:
        database = conway_polynomials.database()
    except Exception as exc:  # pragma: no cover - depends on external package
        raise ConwayTableError(
            f"failed to load conway-polynomials database: {exc}"
        ) from exc

    if not isinstance(database, Mapping):
        raise ConwayTableError(
            "conway-polynomials database() returned "
            f"{type(database).__name__}, expected mapping"
        )
    return database


def _lookup_in_database(
    database: Mapping[int, Mapping[int, Sequence[int]]], p: int, n: int
) -> list[int]:
    if p <= 0 or n <= 0:
        raise ConwayTableError(f"p and n must be positive, got p={p}, n={n}")

    try:
        coeffs = database[p][n]
    except KeyError as exc:
        raise ConwayTableError(f"no Conway table entry for p={p}, n={n}") from exc

    if not isinstance(coeffs, Sequence):
        raise ConwayTableError(
            f"entry for p={p}, n={n} is {type(coeffs).__name__}, "
            "expected coefficient sequence"
        )
    out: list[int] = []
    for coeff in coeffs:
        if not isinstance(coeff, int):
            raise ConwayTableError(
                f"entry for p={p}, n={n} contains non-integer coefficient "
                f"{coeff!r}"
            )
        out.append(coeff)
    if len(out) != n + 1:
        raise ConwayTableError(
            f"entry for p={p}, n={n} has {len(out)} coefficients, expected {n + 1}"
        )
    if out[-1] != 1:
        raise ConwayTableError(
            f"entry for p={p}, n={n} is not monic in ascending convention: {out}"
        )
    return out


def lookup(p: int, n: int) -> list[int]:
    """Return ``C(p, n)`` as ascending integer coefficients."""
    return _lookup_in_database(_load_database(), p, n)


def smoke() -> int:
    try:
        database = _load_database()
    except ConwayTableError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        print(
            "conway_polynomials_table.py: checked 0 case(s), 1 failure(s)",
            file=sys.stderr,
        )
        return 1

    failures = 0
    checked = 0
    for (p, n), expected in SMOKE_CASES.items():
        try:
            actual = _lookup_in_database(database, p, n)
        except ConwayTableError as exc:
            print(f"FAIL ({p}, {n}): {exc}", file=sys.stderr)
            failures += 1
            continue
        if actual != expected:
            print(
                f"FAIL ({p}, {n}): expected {expected}, got {actual}",
                file=sys.stderr,
            )
            failures += 1
            continue
        checked += 1
    print(
        f"conway_polynomials_table.py: checked {checked} case(s), "
        f"{failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: Sequence[str] | None = None) -> int:
    parser = argparse.ArgumentParser(
        description="Lookup Conway polynomial table entries via conway-polynomials."
    )
    parser.add_argument("p", nargs="?", type=int, help="prime characteristic")
    parser.add_argument("n", nargs="?", type=int, help="extension degree")
    parser.add_argument(
        "--smoke",
        action="store_true",
        help="check the known Luebeck cases (2,1), (2,3), and (3,2)",
    )
    parser.add_argument(
        "--pretty",
        action="store_true",
        help="pretty-print JSON lookup output",
    )
    args = parser.parse_args(argv)

    if args.smoke:
        if args.p is not None or args.n is not None:
            parser.error("--smoke does not accept p/n positional arguments")
        return smoke()

    if args.p is None or args.n is None:
        parser.error("provide p and n, or pass --smoke")

    try:
        coeffs = lookup(args.p, args.n)
    except ConwayTableError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2

    payload: dict[str, Any] = {"p": args.p, "n": args.n, "coeffs": coeffs}
    print(json.dumps(payload, indent=2 if args.pretty else None, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
