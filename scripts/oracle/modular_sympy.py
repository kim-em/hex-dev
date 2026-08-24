#!/usr/bin/env python3
"""Independent SymPy/``fractions.Fraction`` oracle for ``HexModular``.

The CRT leg uses SymPy's batched Chinese-remainder implementation after an
independent pairwise-coprimality check. Rational reconstruction follows the
SPEC's truncated Euclidean recurrence in Python and exhaustively enumerates
all bounded rationals on small uniqueness-regime fixtures. No oracle result is
derived from Lean's emitted answer.
"""
from __future__ import annotations

import argparse
import math
import os
import sys
from fractions import Fraction
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexModular" / "modular.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _symmod(a: int, m: int) -> int:
    if m == 0:
        return a
    residue = a % m
    return residue - m if m < 2 * residue else residue


def _crt(record: dict[str, Any]) -> list[int] | None:
    from sympy.ntheory.modular import crt

    residues = [int(value) for value in record["residues"]]
    moduli = [int(value) for value in record["moduli"]]
    if len(residues) != len(moduli):
        raise OracleMismatch("CRT residue and modulus lists have different lengths")
    product = 1
    for modulus in moduli:
        if modulus <= 1 or math.gcd(product, modulus) != 1:
            return None
        product *= modulus
    answer = crt(moduli, residues, check=True)
    if answer is None:
        raise OracleMismatch("SymPy rejected a pairwise-coprime CRT fixture")
    value, oracle_product = map(int, answer)
    if oracle_product != product:
        raise OracleMismatch(
            f"SymPy CRT modulus {oracle_product} differs from product {product}"
        )
    return [_symmod(value, product), product]


def _euclid_until(m: int, a: int, bound: int) -> tuple[int, int]:
    modulus = abs(m)
    if modulus == 0:
        return (0, 0)
    old_r, r = modulus, abs(a % modulus)
    old_t, t = 0, 1
    while True:
        if r <= bound:
            return (r, t)
        if r == 0:
            return (0, t)
        quotient = old_r // r
        old_r, r = r, old_r % r
        old_t, t = t, old_t - quotient * t


def _reconstruct(record: dict[str, Any]) -> list[int] | None:
    a = int(record["a"])
    m = int(record["m"])
    p = int(record["p"])
    q = int(record["q"])
    if m == 0:
        return None
    remainder, coefficient = _euclid_until(m, a, p)
    if coefficient == 0:
        return None
    candidate = Fraction(remainder, coefficient)
    valid = (
        (candidate.denominator * a - candidate.numerator) % m == 0
        and abs(candidate.numerator) <= p
        and candidate.denominator <= q
    )
    return [candidate.numerator, candidate.denominator] if valid else None


def _check_unique_regime(record: dict[str, Any], expected: list[int] | None) -> None:
    a = int(record["a"])
    m = int(record["m"])
    p = int(record["p"])
    q = int(record["q"])
    if m <= 0 or p < 0 or q <= 0 or 2 * p * q >= m or m > 5000:
        return
    solutions = {
        Fraction(numerator, denominator)
        for denominator in range(1, q + 1)
        for numerator in range(-p, p + 1)
        if (denominator * a - numerator) % m == 0
    }
    expected_fraction = (
        None if expected is None else Fraction(expected[0], expected[1])
    )
    if expected_fraction is None and solutions:
        raise OracleMismatch(
            f"reference reconstruction missed bounded solution(s) {solutions}"
        )
    if expected_fraction is not None and solutions != {expected_fraction}:
        raise OracleMismatch(
            f"bounded solution set {solutions} differs from {expected_fraction}"
        )


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    import sympy

    cases, results = split_fixtures_results(read_fixtures(source))
    failures = 0
    checked = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        operation = result["op"]
        lean_value = result["value"]
        input_record = cases[(lib, case_id)]
        try:
            if operation == "symmod":
                if input_record["kind"] != "symmod":
                    raise OracleMismatch("symmod result has the wrong fixture kind")
                oracle_value: Any = _symmod(
                    int(input_record["a"]), int(input_record["m"])
                )
            elif operation == "crt":
                if input_record["kind"] != "crt":
                    raise OracleMismatch("CRT result has the wrong fixture kind")
                oracle_value = _crt(input_record)
            elif operation == "ratrecon":
                if input_record["kind"] != "ratrecon":
                    raise OracleMismatch(
                        "rational-reconstruction result has the wrong fixture kind"
                    )
                oracle_value = _reconstruct(input_record)
                _check_unique_regime(input_record, oracle_value)
            else:
                raise OracleMismatch(f"unsupported operation {operation!r}")
            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{operation}",
                kind=operation,
                input_record=input_record,
                oracle_name="SymPy+fractions.Fraction",
                oracle_version=sympy.__version__,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except (KeyError, TypeError, ValueError, OracleMismatch) as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({operation}): {exc}", file=sys.stderr)
    print(
        f"modular_sympy.py: checked {checked} result(s), {failures} failure(s)",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("input", nargs="?", help="JSONL fixture path (default: stdin)")
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
    input_path: str | None = str(DEFAULT_FIXTURE) if args.check else args.input
    return check(
        input_path,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
