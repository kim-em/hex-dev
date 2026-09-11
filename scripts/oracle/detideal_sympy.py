#!/usr/bin/env python3
"""SymPy oracle driver for ``hex-determinantal-ideal``.

Reads the JSONL stream emitted by ``lake exe
hexdeterminantalideal_emit_fixtures`` and recomputes, with ``sympy.Matrix``,
the enumerated ``r x r`` minors of each committed matrix, the generators of
the determinantal ideal ``I_r(A)``, the rank of the specialisation at a
point, and the decision of the rank-drop locus there.

The row and column selections come from ``itertools.combinations`` sorted by
reversed tuple, which is the colexicographic order ``selectedColumnTuples``
produces (``selectedColumnTuples 2 4`` is ``01, 02, 12, 03, 13, 23``); a
lexicographic enumeration disagrees on the ``2 x 4`` case. Rows are the outer
loop and columns the inner one. The two boundary conventions need no special
case: ``combinations(range(n), 0)`` is the single empty tuple for every ``n``,
so ``r = 0`` gives exactly one minor, the determinant ``1`` of the ``0 x 0``
matrix, on every shape; and ``combinations(range(n), r)`` is empty once
``r > n``, so ``r > min(rows, cols)`` gives no minors at all.

The term encoding, generator naming and monomial orders are shared with
``mvpoly_sympy.py``.

The oracle is ``if_available`` for local development. Release CI installs
SymPy and preflights its import before invoking this script, so it remains a
a required check there.
"""
from __future__ import annotations

import argparse
import itertools
import json
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexDeterminantalIdeal" / "detideal.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)
from scripts.oracle.mvpoly_sympy import (  # noqa: E402
    _generators,
    _record_from_expr,
)


def _entry(terms: list[Any], generators: tuple[Any, ...]):
    """One matrix entry, from its ``(exponents, coefficient)`` term list."""
    from sympy import Integer

    expression = Integer(0)
    for exponents, coefficient in terms:
        term = Integer(coefficient)
        for generator, exponent in zip(generators, exponents):
            term *= generator**exponent
        expression += term
    return expression


def _matrix(record: dict[str, Any]):
    from sympy import Matrix

    generators = _generators(record["arity"])
    flat = [
        _entry(terms, generators) for row in record["entries"] for terms in row
    ]
    return Matrix(record["rows"], record["cols"], flat), generators


def _selections(n: int, r: int) -> list[tuple[int, ...]]:
    """The strictly increasing ``r``-tuples below ``n``, colexicographically."""
    return sorted(itertools.combinations(range(n), r), key=lambda t: t[::-1])


def _minor_expressions(record: dict[str, Any]) -> tuple[list[Any], tuple[Any, ...]]:
    """The expanded ``r x r`` minors, rows outer and columns inner."""
    from sympy import expand

    matrix, generators = _matrix(record)
    r = record["r"]
    minors = [
        expand(matrix.extract(list(rows), list(cols)).det())
        for rows in _selections(record["rows"], r)
        for cols in _selections(record["cols"], r)
    ]
    return minors, generators


def _terms(expression: Any, record: dict[str, Any], generators: tuple[Any, ...]):
    return _record_from_expr(
        expression,
        record["arity"],
        record["order"],
        generators=generators,
    )["terms"]


def _minors(record: dict[str, Any]) -> list[Any]:
    expressions, generators = _minor_expressions(record)
    return [_terms(expression, record, generators) for expression in expressions]


def _det_ideal_gens(record: dict[str, Any]) -> list[Any]:
    """The nonzero minors with duplicates removed, in a canonical order."""
    unique: list[Any] = []
    for terms in _minors(record):
        if terms and terms not in unique:
            unique.append(terms)
    return sorted(unique)


def _point_map(record: dict[str, Any], op: str, generators: tuple[Any, ...]):
    """The integer point named by a ``rankAt/`` or ``inLocus/`` op.

    Points are integer tuples (the emit driver reads them as integers of the
    field); anything else is a malformed stream, not a value to coerce.
    """
    point = json.loads(op.split("/", 1)[1])
    if not isinstance(point, list) or not all(
        isinstance(coordinate, int) and not isinstance(coordinate, bool)
        for coordinate in point
    ):
        raise OracleMismatch(f"{op!r}: point must be a JSON list of integers")
    return dict(zip(generators, point, strict=True))


def _rank_at(record: dict[str, Any], op: str) -> list[int]:
    from sympy import Matrix, Rational

    matrix, generators = _matrix(record)
    assignments = _point_map(record, op, generators)
    specialised = matrix.subs(assignments) if assignments else matrix
    entries = [Rational(entry) for entry in specialised]
    return [int(Matrix(record["rows"], record["cols"], entries).rank())]


def _in_locus(record: dict[str, Any], op: str) -> bool:
    expressions, generators = _minor_expressions(record)
    assignments = _point_map(record, op, generators)
    return all(
        (expression.subs(assignments) if assignments else expression) == 0
        for expression in expressions
    )


def _sympy_version() -> str:
    import sympy

    return sympy.__version__


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    cases, results = split_fixtures_results(read_fixtures(source))
    failures = 0
    checked = 0
    version = _sympy_version()

    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        lean_value = result["value"]
        try:
            input_record = cases[(lib, case_id)]
            if op == "minors":
                oracle_value = _minors(input_record)
            elif op == "detIdealGens":
                lean_value = sorted(lean_value)
                oracle_value = _det_ideal_gens(input_record)
            elif op.startswith("rankAt/"):
                oracle_value = _rank_at(input_record, op)
            elif op.startswith("inLocus/"):
                oracle_value = _in_locus(input_record, op)
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r}; extend "
                    "detideal_sympy.py"
                )

            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{op}",
                kind=op,
                input_record=input_record,
                oracle_name="SymPy",
                oracle_version=version,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except (OracleMismatch, KeyError, TypeError, ValueError) as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)

    print(
        f"detideal_sympy.py: checked {checked} case(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group()
    src.add_argument("input", nargs="?", help="JSONL fixture path (default: stdin)")
    src.add_argument(
        "--check",
        action="store_true",
        help=f"read the committed sample at {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
        help="directory for JSON failure records",
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)

    try:
        import sympy  # noqa: F401
    except ImportError:
        print("SKIP: SymPy not installed", file=sys.stderr)
        return 0

    source = str(DEFAULT_FIXTURE) if args.check else args.input
    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
