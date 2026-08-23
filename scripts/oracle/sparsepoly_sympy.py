#!/usr/bin/env python3
"""SymPy oracle driver for ``hex-sparse-poly``.

Reads the JSONL stream emitted by ``lake exe hexsparsepoly_emit_fixtures``
and recomputes arithmetic, powering, evaluation, the derivative, and the
substitutions with the *sparse* polynomial elements of
``sympy.polys.rings``, which store a dictionary keyed on the exponent and
handle an exponent of ``10^6`` without materialising a coefficient
vector. ``python-flint``'s ``fmpz_poly`` is dense and is therefore not
the oracle for the high-exponent cases.

Every expected value is rebuilt from the original serialized terms of the
fixture record, never from Lean's output. Domains: ``ZZ`` for ``int``
records, ``QQ`` for ``rat``, ``GF(p)`` for ``zmod`` (normalised to the
standard representative in ``[0, p)``).

The oracle is ``if_available`` for local development. Release CI installs
SymPy and preflights its import before invoking this script, so it
remains a hard gate there.
"""
from __future__ import annotations

import argparse
import os
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexSparsePoly" / "sparsepoly.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _domain(record: dict[str, Any]):
    from sympy import GF, QQ, ZZ

    name = record["domain"]
    if name == "int":
        return ZZ
    if name == "rat":
        return QQ
    return GF(record["mod"], symmetric=False)


def _ring(record: dict[str, Any]):
    from sympy.polys.rings import ring

    return ring("x", _domain(record))


def _element(R, record: dict[str, Any]):
    """Rebuild the sparse ring element from the original fixture terms."""
    dom = R.domain
    poly = R.zero
    for exponent, numerator, denominator in record["terms"]:
        if record["domain"] == "rat":
            coefficient = dom.convert(Fraction(numerator, denominator))
        else:
            coefficient = dom.convert(numerator)
        poly += coefficient * R.gens[0] ** exponent
    return poly


def _wire_coefficient(record: dict[str, Any], coefficient) -> list[int]:
    if record["domain"] == "rat":
        # `int(...)` because with python-flint installed SymPy's QQ ground
        # type is flint's `fmpq`, whose numerator/denominator are `fmpz`,
        # not `numbers.Rational`, and `Fraction` rejects those.
        rational = Fraction(int(coefficient.numerator),
                            int(coefficient.denominator))
        return [rational.numerator, rational.denominator]
    if record["domain"] == "zmod":
        return [int(coefficient) % record["mod"], 1]
    return [int(coefficient), 1]


def _wire_terms(record: dict[str, Any], poly) -> list[list[int]]:
    terms = []
    for (exponent,), coefficient in sorted(poly.terms()):
        num, den = _wire_coefficient(record, coefficient)
        if num == 0:
            continue
        terms.append([exponent, num, den])
    return terms


def _scalar(record: dict[str, Any], value) -> list[list[int]]:
    """A scalar result serialised the way the emit driver does: one
    `[0, num, den]` entry, kept even when the value is zero."""
    num, den = _wire_coefficient(record, value)
    return [[0, num, den]]


def _parse_scalar(record: dict[str, Any], text: str):
    dom = _domain(record)
    if record["domain"] == "rat":
        return dom.convert(Fraction(text))
    return dom.convert(int(text))


def _expected(op: str, inputs: dict[str, dict[str, Any]],
              case_id: str) -> tuple[dict[str, Any], Any]:
    """Recompute `op` for `case_id`, returning the record whose domain
    labels the output together with the oracle value."""
    def rec(suffix: str) -> dict[str, Any]:
        return inputs[case_id + suffix]

    if op in {"add", "sub", "mul"}:
        left_record = rec("/left")
        R, _x = _ring(left_record)
        left = _element(R, left_record)
        right = _element(R, rec("/right"))
        if op == "add":
            return left_record, left + right
        if op == "sub":
            return left_record, left - right
        return left_record, left * right

    if op == "compose":
        left_record = rec("/left")
        R, x = _ring(left_record)
        left = _element(R, left_record)
        right = _element(R, rec("/right"))
        return left_record, left.compose(x, right)

    record = rec("")
    R, x = _ring(record)
    poly = _element(R, record)

    if op == "neg":
        return record, -poly
    if op == "derivative":
        return record, poly.diff(x)
    if op.startswith("pow/"):
        return record, poly ** int(op.split("/", 1)[1])
    if op.startswith("substPow/"):
        return record, poly.compose(x, x ** int(op.split("/", 1)[1]))
    if op.startswith("substScale/"):
        scale = _parse_scalar(record, op.split("/", 1)[1])
        return record, poly.compose(x, scale * x)
    if op.startswith("eval/"):
        point = _parse_scalar(record, op.split("/", 1)[1])
        return record, ("scalar", poly(point))
    raise ValueError(f"unknown op: {op}")


def check(source: str | None, *, failure_dir: Path, profile: str,
          seed: int) -> int:
    import sympy

    version = getattr(sympy, "__version__", "unknown")
    cases, results = split_fixtures_results(read_fixtures(source))
    inputs = {case: record for (_lib, case), record in cases.items()}

    checked = 0
    failures = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        op = result["op"]
        lean_value = result["value"]
        try:
            record, oracle = _expected(op, inputs, case_id)
            if isinstance(oracle, tuple) and oracle[0] == "scalar":
                oracle_value = _scalar(record, oracle[1])
            else:
                oracle_value = _wire_terms(record, oracle)
            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{op}",
                kind=op,
                input_record=record,
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
        f"sparsepoly_sympy.py: checked {checked} case(s), "
        f"{failures} failure(s)",
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
