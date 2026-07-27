#!/usr/bin/env python3
"""Independent FLINT/PARI oracle for ``HexNumberField``.

The JSONL stream is emitted by ``lake exe hexnumberfield_emit_fixtures``.
For lazy arithmetic, PARI forms the eliminant from the original operand
polynomials and FLINT independently primitive-normalizes, factors, and removes
multiplicity. For exactification, FLINT factors the original enclosing
polynomial and PARI root approximations select the unique factor meeting the
original dyadic isolation box. No Lean-produced result is used as an oracle
input. Root-set fixtures are checked independently against FLINT's certified
Arb root balls, including multiplicities.
"""
from __future__ import annotations

import argparse
import math
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT
    / "conformance-fixtures"
    / "HexNumberField"
    / "number_field.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _coeffs(record: dict[str, Any]) -> list[int]:
    if record["kind"] != "poly":
        raise OracleMismatch(f"expected poly record, got {record['kind']!r}")
    return [int(c) for c in record["coeffs"]]


def _trim(coefficients) -> list[int]:
    result = [int(c) for c in coefficients]
    while result and result[-1] == 0:
        result.pop()
    return result


def _pari_coeffs(pari, polynomial) -> list[int]:
    return _trim(pari.Vecrev(polynomial))


def _flint_core(fmpz_poly, coefficients: list[int]) -> list[int]:
    """Primitive positive-leading product of all distinct FLINT factors."""
    polynomial = fmpz_poly(coefficients)
    if polynomial == 0:
        return []
    _content, factors = polynomial.factor()
    core = fmpz_poly([1])
    for factor, _multiplicity in factors:
        core *= factor
    result = _trim(core.coeffs())
    if result and result[-1] < 0:
        result = [-coefficient for coefficient in result]
    return result


def _remove_x(coefficients: list[int]) -> list[int]:
    """Remove the largest power of x, matching product-eliminant semantics."""
    first_nonzero = 0
    while (
        first_nonzero < len(coefficients)
        and coefficients[first_nonzero] == 0
    ):
        first_nonzero += 1
    return coefficients[first_nonzero:]


def _lazy_raw(pari, left: list[int], right: list[int], operation: str):
    x = pari("x")
    y = pari("y")
    z = pari("z")
    p = pari.Polrev(left, "y")
    q = pari.Polrev(right, "z")
    if operation == "add":
        transformed = pari.subst(q, z, x - y)
    elif operation == "sub":
        transformed = pari.subst(q, z, y - x)
    elif operation == "mul":
        degree = len(right) - 1
        transformed = pari(0)
        for exponent, coefficient in enumerate(right):
            transformed += coefficient * x**exponent * y ** (degree - exponent)
    else:
        raise OracleMismatch(f"unsupported binary operation {operation!r}")
    return pari.polresultant(p, transformed, y)


def _inverse_raw(pari, coefficients: list[int]):
    x = pari("x")
    y = pari("y")
    polynomial = pari.Polrev(coefficients, "y")
    return pari.polresultant(polynomial, y * x - 1, y)


def _box(record: dict[str, Any]) -> tuple[complex, float]:
    if record["kind"] != "matrix":
        raise OracleMismatch(f"expected matrix box, got {record['kind']!r}")
    rows = record["rows"]
    if len(rows) != 3 or len(rows[0]) != 2 or len(rows[1]) != 2:
        raise OracleMismatch("malformed dyadic box fixture")
    numerators = [int(rows[0][0]), int(rows[1][0])]
    precision = int(rows[2][0])
    if any(abs(numerator) > 2**53 for numerator in numerators) or precision > 48:
        raise OracleMismatch("dyadic box exceeds the exact-double oracle profile")
    real = numerators[0] / int(rows[0][1])
    imaginary = numerators[1] / int(rows[1][1])
    half_width = 2.0 ** (-precision)
    return complex(real, imaginary), math.sqrt(2.0) * half_width


def _exact_factor(pari, fmpz_poly, coefficients: list[int], box_record):
    _content, factors = fmpz_poly(coefficients).factor()
    center, radius = _box(box_record)
    matches: list[list[int]] = []
    for factor, _multiplicity in factors:
        factor_coefficients = _trim(factor.coeffs())
        roots = pari.polroots(pari.Polrev(factor_coefficients, "x"))
        if any(abs(complex(root) - center) <= radius for root in roots):
            matches.append(factor_coefficients)
    if len(matches) != 1:
        raise OracleMismatch(
            f"isolation box met {len(matches)} FLINT irreducible factors"
        )
    result = matches[0]
    if result[-1] < 0:
        result = [-coefficient for coefficient in result]
    return result


def _version(module, pari) -> str:
    flint_version = getattr(module, "__version__", "unknown")
    try:
        pari_version = str(pari("Str(version())"))
    except Exception:
        pari_version = "unknown"
    return f"python-flint/{flint_version}+PARI/{pari_version}"


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    import cypari2  # type: ignore[import-not-found]
    import flint  # type: ignore[import-not-found]
    from flint import fmpz_poly  # type: ignore[import-not-found]
    from scripts.oracle.roots_flint import _check_case as check_roots_case

    pari = cypari2.Pari()
    cases, results = split_fixtures_results(read_fixtures(source))
    oracle_version = _version(flint, pari)
    checked = 0
    failures = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        operation = result["op"]
        try:
            if operation == "roots":
                input_record = cases[(lib, f"{case_id}/input")]
                coefficients = _coeffs(input_record)
                check_roots_case(
                    lib=lib,
                    case_id=case_id,
                    coeffs=coefficients,
                    lean_value=result["value"],
                    failure_dir=failure_dir,
                    profile=profile,
                    seed=seed,
                    oracle_version=oracle_version,
                )
                checked += 1
                continue
            lean_value = [int(c) for c in result["value"]]
            if operation in {"add", "sub", "mul"}:
                left_record = cases[(lib, f"{case_id}/left")]
                right_record = cases[(lib, f"{case_id}/right")]
                left = _coeffs(left_record)
                right = _coeffs(right_record)
                raw = _lazy_raw(pari, left, right, operation)
                raw_coefficients = _pari_coeffs(pari, raw)
                if operation == "mul":
                    raw_coefficients = _remove_x(raw_coefficients)
                expected = _flint_core(fmpz_poly, raw_coefficients)
                input_record = {"left": left_record, "right": right_record}
            elif operation == "inv":
                input_record = cases[(lib, f"{case_id}/input")]
                coefficients = _coeffs(input_record)
                raw = _inverse_raw(pari, coefficients)
                expected = _flint_core(fmpz_poly, _pari_coeffs(pari, raw))
            elif operation == "exact":
                input_record = {
                    "polynomial": cases[(lib, f"{case_id}/input")],
                    "box": cases[(lib, f"{case_id}/box")],
                }
                coefficients = _coeffs(input_record["polynomial"])
                expected = _exact_factor(
                    pari, fmpz_poly, coefficients, input_record["box"]
                )
            else:
                raise OracleMismatch(f"unsupported operation {operation!r}")
            assert_equal(
                lean_value,
                expected,
                library=lib,
                case_id=f"{case_id}:{operation}",
                kind=operation,
                input_record=input_record,
                oracle_name="python-flint+cypari2/PARI",
                oracle_version=oracle_version,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except (
            KeyError,
            OracleMismatch,
            ValueError,
            TypeError,
            cypari2.PariError,
        ) as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({operation}): {exc}", file=sys.stderr)
    print(
        f"number_field_flint_pari.py: checked {checked} case(s), "
        f"{failures} failure(s) with {oracle_version}",
        file=sys.stderr,
    )
    return 1 if failures else 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    source = parser.add_mutually_exclusive_group()
    source.add_argument("input", nargs="?", help="JSONL path (default: stdin)")
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
    parser.add_argument("--seed", type=int, default=0xC0FFEE)
    args = parser.parse_args(argv)
    fixture_source = str(DEFAULT_FIXTURE) if args.check else args.input
    try:
        import cypari2  # noqa: F401
        import flint  # noqa: F401
    except ImportError:
        print("SKIP: python-flint or cypari2 is not installed", file=sys.stderr)
        return 0
    return check(
        fixture_source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
