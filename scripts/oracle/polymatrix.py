#!/usr/bin/env python3
"""SymPy Smith-normal-form oracle for ``HexPolySmith`` polymatrices.

SymPy is the primary oracle because its PID implementation accepts rectangular
matrices over ``GF(p)[x]`` and ``QQ[x]``. PARI's polynomial ``matsnf`` is
square-only, and FLINT exposes no polynomial-matrix Smith routine.
"""
from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexPolySmith" / "smith.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _sympy_version() -> str:
    import sympy

    return sympy.__version__


def _entry_expr(entry: Any, field: dict[str, Any], x: Any) -> Any:
    import sympy as sp

    if "p" in field:
        return sum(sp.Integer(c) * x**i for i, c in enumerate(entry))
    return sum(
        sp.Rational(num, den) * x**i
        for i, (num, den) in enumerate(zip(entry["num"], entry["den"]))
    )


def _matrix(record: dict[str, Any]) -> tuple[Any, Any, int | None]:
    import sympy as sp

    x = sp.Symbol("x")
    rows, cols = record["rows"], record["cols"]
    field = record["field"]
    modulus = field.get("p")
    if rows == 0 or cols == 0:
        matrix = sp.zeros(rows, cols)
    else:
        matrix = sp.Matrix(
            [
                [_entry_expr(entry, field, x) for entry in row]
                for row in record["entries"]
            ]
        )
    domain = (sp.GF(modulus) if modulus is not None else sp.QQ).poly_ring(x)
    if not domain.is_PID:
        raise OracleMismatch(f"SymPy does not recognize {domain} as a PID")
    return matrix, domain, modulus


def _poly(expr: Any, modulus: int | None) -> Any:
    import sympy as sp

    x = sp.Symbol("x")
    return sp.Poly(expr, x, modulus=modulus) if modulus is not None else sp.Poly(
        expr, x, domain=sp.QQ
    )


def _normalise(poly: Any) -> Any:
    return poly if poly.is_zero else poly.monic()


def _chain_order(polys: list[Any]) -> list[Any]:
    """Put a known divisibility chain in increasing-divisibility order."""
    remaining = list(polys)
    ordered: list[Any] = []
    while remaining:
        for i, candidate in enumerate(remaining):
            if all(other.rem(candidate).is_zero for other in remaining):
                ordered.append(remaining.pop(i))
                break
        else:
            raise OracleMismatch(
                "SymPy returned diagonal entries that do not form a divisibility chain"
            )
    return ordered


def _value(poly: Any, modulus: int | None) -> Any:
    if poly.is_zero:
        return [] if modulus is not None else {"num": [], "den": []}
    coeffs = [poly.nth(i) for i in range(poly.degree() + 1)]
    if modulus is not None:
        return [int(c) % modulus for c in coeffs]
    return {
        "num": [int(c.p) for c in coeffs],
        "den": [int(c.q) for c in coeffs],
    }


def _smith(record: dict[str, Any]) -> list[Any]:
    from sympy.matrices.normalforms import smith_normal_form

    matrix, domain, modulus = _matrix(record)
    if min(record["rows"], record["cols"]) == 0:
        return []
    diagonal = smith_normal_form(matrix, domain=domain)
    factors = [
        _normalise(_poly(diagonal[i, i], modulus))
        for i in range(min(diagonal.rows, diagonal.cols))
        if diagonal[i, i] != 0
    ]
    return [_value(poly, modulus) for poly in _chain_order(factors)]


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    cases, results = split_fixtures_results(read_fixtures(source))
    version = _sympy_version()
    failures = 0
    checked = 0
    for result in results:
        lib, case_id, op = result["lib"], result["case"], result["op"]
        try:
            if op != "smith":
                raise OracleMismatch(f"unsupported operation {op!r}")
            input_record = cases[(lib, case_id)]
            oracle_value = _smith(input_record)
            assert_equal(
                result["value"],
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{op}",
                kind=op,
                input_record=input_record,
                oracle_name="SymPy smith_normal_form",
                oracle_version=version,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except Exception as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({op}): {exc}", file=sys.stderr)
    print(
        f"polymatrix.py: checked {checked} case(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    src = parser.add_mutually_exclusive_group()
    src.add_argument("input", nargs="?", help="JSONL input (default: stdin)")
    src.add_argument(
        "--check",
        action="store_true",
        help=f"read {DEFAULT_FIXTURE.relative_to(REPO_ROOT)}",
    )
    parser.add_argument(
        "--failure-dir",
        default=os.environ.get("HEX_FAILURE_DIR", str(DEFAULT_FAILURE_DIR)),
    )
    parser.add_argument("--profile", default="ci")
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)
    source = str(DEFAULT_FIXTURE) if args.check else args.input
    try:
        import sympy  # noqa: F401
    except ImportError:
        print("SKIP: SymPy not installed", file=sys.stderr)
        return 0
    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
