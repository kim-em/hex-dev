#!/usr/bin/env python3
"""SymPy oracle for ``HexMvGcd`` gcd and squarefree fixtures."""
from __future__ import annotations

import argparse
import math
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexMvGcd" / "mvgcd.jsonl"
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


def _generators(arity: int):
    import sympy as sp

    return sp.symbols(f"x0:{arity}") if arity else ()


def _expression(terms: list[Any], generators: tuple[Any, ...]):
    import sympy as sp

    result = sp.Integer(0)
    for exponents, coefficient in terms:
        term = sp.Integer(coefficient)
        for generator, exponent in zip(generators, exponents):
            term *= generator**exponent
        result += term
    return result


def _poly(record: dict[str, Any], terms: list[Any]):
    import sympy as sp

    arity = int(record["arity"])
    generators = _generators(arity)
    expression = _expression(terms, generators)
    if arity == 0:
        return int(expression)
    if record["domain"] == "zmod":
        return sp.Poly(expression, *generators, modulus=int(record["mod"]))
    return sp.Poly(expression, *generators, domain=sp.ZZ)


def _terms(poly, arity: int, order: str) -> list[Any]:
    from sympy.polys.orderings import monomial_key

    if arity == 0:
        return [] if poly == 0 else [[[], int(poly)]]
    if poly.is_zero:
        return []
    return [
        [list(monomial), int(coefficient)]
        for monomial, coefficient in reversed(poly.terms(order=monomial_key(order)))
        if coefficient != 0
    ]


def _mvgcd(record: dict[str, Any]) -> dict[str, Any]:
    arity = int(record["arity"])
    order = record["order"]
    left = _poly(record, record["left"])
    right = _poly(record, record["right"])
    if arity == 0:
        common = math.gcd(left, right)
        if common == 0:
            left_cofactor, right_cofactor = 1, 1
        else:
            left_cofactor, right_cofactor = left // common, right // common
    else:
        common = left.gcd(right)
        if common.is_zero:
            left_cofactor = right_cofactor = left.one
        else:
            left_cofactor = left.exquo(common)
            right_cofactor = right.exquo(common)
    return {
        "gcd": _terms(common, arity, order),
        "left": _terms(left_cofactor, arity, order),
        "right": _terms(right_cofactor, arity, order),
    }


def _mvsqf(record: dict[str, Any]) -> dict[str, Any]:
    arity = int(record["arity"])
    order = record["order"]
    polynomial = _poly(record, record["terms"])
    if arity == 0:
        return {"content": polynomial, "factors": []}
    content, factors = polynomial.sqf_list()
    return {
        "content": int(content),
        "factors": [
            {
                "factor": _terms(factor, arity, order),
                "multiplicity": int(multiplicity),
            }
            for factor, multiplicity in sorted(factors, key=lambda pair: pair[1])
        ],
    }


def _mvsquarefree(record: dict[str, Any]) -> bool:
    arity = int(record["arity"])
    polynomial = _poly(record, record["terms"])
    if arity == 0:
        return polynomial != 0
    if polynomial.is_zero:
        return False
    common = polynomial
    for generator in polynomial.gens:
        common = common.gcd(polynomial.diff(generator))
    return common.total_degree() == 0


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
        lib = result["lib"]
        case_id = result["case"]
        operation = result["op"]
        input_record = cases[(lib, case_id)]
        try:
            if operation == "mvgcd":
                oracle_value: Any = _mvgcd(input_record)
            elif operation == "mvsqf":
                oracle_value = _mvsqf(input_record)
            elif operation == "mvsquarefree":
                oracle_value = _mvsquarefree(input_record)
            else:
                raise OracleMismatch(f"unsupported operation {operation!r}")
            assert_equal(
                result["value"],
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{operation}",
                kind=operation,
                input_record=input_record,
                oracle_name="SymPy",
                oracle_version=version,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except (KeyError, TypeError, ValueError, OracleMismatch) as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({operation}): {exc}", file=sys.stderr)
    print(
        f"mvgcd_sympy.py: checked {checked} case(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("input", nargs="?", help="JSONL input (default: stdin)")
    source.add_argument(
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
    input_path = str(DEFAULT_FIXTURE) if args.check else args.input
    try:
        import sympy  # noqa: F401
    except ImportError:
        print("SKIP: SymPy not installed", file=sys.stderr)
        return 0
    return check(
        input_path,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
