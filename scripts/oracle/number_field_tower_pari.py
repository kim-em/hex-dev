#!/usr/bin/env python3
"""PARI oracle for ``HexNumberFieldTower``.

The input is the JSONL stream emitted by
``lake exe hexnumberfieldtower_emit_fixtures``. Generator polynomials are
original inputs, not Lean-produced primitive presentations. From those inputs
the oracle independently:

* builds composita with ``polcompositum`` and initializes them with ``nfinit``;
* factors inputs with ``nffactor`` and compares degree/multiplicity buckets;
* computes splitting fields with ``nfsplitting`` and compares their degrees;
* enumerates the specified signed shifts, computes primitive-element
  resultants, and compares the first irreducible full-degree polynomial.

The oracle never refactors or canonicalizes a Lean factor as a substitute for
factoring the original input.
"""
from __future__ import annotations

import argparse
import math
import os
import sys
from functools import reduce
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT
    / "conformance-fixtures"
    / "HexNumberFieldTower"
    / "number_field_tower.jsonl"
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


def _pari_poly(pari, coeffs: list[int], variable: str = "x"):
    """Build a PARI polynomial from ascending integer coefficients."""
    return pari(f"Polrev({coeffs},{variable})")


def _degree(pari, polynomial) -> int:
    return int(pari.poldegree(polynomial))


def _factor_rows(pari, factorization) -> list[tuple[Any, int]]:
    rows = int(pari.matsize(factorization)[0])
    return [
        (factorization[i, 0], int(factorization[i, 1]))
        for i in range(rows)
    ]


def _factor_buckets(pari, factorization) -> list[list[int]]:
    return sorted(
        [[_degree(pari, factor), exponent] for factor, exponent in _factor_rows(pari, factorization)]
    )


def _generators(cases: dict[tuple[str, str], dict[str, Any]], lib: str, case_id: str) -> list[list[int]]:
    generators: list[list[int]] = []
    index = 0
    while (lib, f"{case_id}/generator/{index}") in cases:
        generators.append(_coeffs(cases[(lib, f"{case_id}/generator/{index}")]))
        index += 1
    return generators


def _compositum(pari, generators: list[list[int]]):
    """Independent maximum-degree compositum polynomial in variable ``y``."""
    if not generators:
        return None
    current = _pari_poly(pari, generators[0], "y")
    for coefficients in generators[1:]:
        extension = _pari_poly(pari, coefficients, "y")
        components = list(pari.polcompositum(current, extension))
        if not components:
            raise OracleMismatch("polcompositum returned no component")
        current = max(components, key=lambda polynomial: _degree(pari, polynomial))
    return current


def _signed_shift(index: int) -> int:
    if index == 0:
        return 0
    if index % 2 == 1:
        return (index + 1) // 2
    return -(index // 2)


def _poly_coeffs(pari, polynomial) -> list[int]:
    coefficients = [int(c) for c in pari.Vecrev(polynomial)]
    while coefficients and coefficients[-1] == 0:
        coefficients.pop()
    if not coefficients:
        return []
    content = reduce(math.gcd, (abs(c) for c in coefficients), 0)
    if content > 1:
        coefficients = [c // content for c in coefficients]
    if coefficients[-1] < 0:
        coefficients = [-c for c in coefficients]
    return coefficients


def _primitive_minpoly(pari, generators: list[list[int]]) -> list[int]:
    """First full-degree polynomial in ``0, 1, -1, 2, -2, ...`` order."""
    if not generators:
        return [0, 1]
    current_coeffs = generators[0]
    current_degree = len(current_coeffs) - 1
    # Exercise the same number-field initialization expected of the shipped
    # flattening output even for a one-generator input.
    pari.nfinit(_pari_poly(pari, current_coeffs))
    for alpha_coeffs in generators[1:]:
        target = current_degree * (len(alpha_coeffs) - 1)
        count = math.comb(target, 2) + 1
        theta = _pari_poly(pari, current_coeffs, "z")
        alpha = _pari_poly(pari, alpha_coeffs, "y")
        x = pari("x")
        y = pari("y")
        z = pari("z")
        accepted = None
        for index in range(count):
            shift = _signed_shift(index)
            relation = pari.subst(theta, z, x - shift * y)
            eliminant = pari.polresultant(relation, alpha, y)
            factorization = pari.factor(eliminant)
            candidates = [
                factor
                for factor, _ in _factor_rows(pari, factorization)
                if _degree(pari, factor) == target
            ]
            if candidates:
                accepted = candidates[0]
                break
        if accepted is None:
            raise OracleMismatch(
                f"no full-degree primitive element in {count} signed shifts"
            )
        # nfinit rejects malformed or reducible candidates and independently
        # confirms the field degree used by the comparison.
        field = pari.nfinit(accepted)
        if _degree(pari, field[0]) != target:
            raise OracleMismatch("nfinit returned the wrong primitive degree")
        current_coeffs = _poly_coeffs(pari, accepted)
        current_degree = target
    return current_coeffs


def _factor_degrees(pari, generators: list[list[int]], input_coeffs: list[int]) -> list[list[int]]:
    polynomial = _pari_poly(pari, input_coeffs, "x")
    field_polynomial = _compositum(pari, generators)
    if field_polynomial is None:
        return _factor_buckets(pari, pari.factor(polynomial))
    field = pari.nfinit(field_polynomial)
    return _factor_buckets(pari, pari.nffactor(field, polynomial))


def _split_summary(pari, input_coeffs: list[int]) -> list[int]:
    polynomial = _pari_poly(pari, input_coeffs, "x")
    factorization = pari.factor(polynomial)
    rows = _factor_rows(pari, factorization)
    distinct = pari(1)
    multiplicities: list[int] = []
    for factor, exponent in rows:
        distinct *= factor
        multiplicities.extend([exponent] * _degree(pari, factor))
    splitting = pari.nfsplitting(distinct)
    return [_degree(pari, splitting), len(multiplicities), *sorted(multiplicities)]


def _pari_version(pari) -> str:
    try:
        return str(pari("Str(version())"))
    except Exception:
        return "unknown"


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    import cypari2  # type: ignore[import-not-found]

    pari = cypari2.Pari()
    cases, results = split_fixtures_results(read_fixtures(source))
    oracle_version = _pari_version(pari)
    checked = 0
    failures = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        operation = result["op"]
        lean_value = result["value"]
        generators = _generators(cases, lib, case_id)
        try:
            if operation == "factor_degrees":
                input_coeffs = _coeffs(cases[(lib, f"{case_id}/input")])
                expected = _factor_degrees(pari, generators, input_coeffs)
                input_record = {
                    "generators": generators,
                    "polynomial": input_coeffs,
                }
            elif operation == "split":
                input_coeffs = _coeffs(cases[(lib, f"{case_id}/input")])
                expected = _split_summary(pari, input_coeffs)
                input_record = {"polynomial": input_coeffs}
            elif operation == "flatten_minpoly":
                expected = _primitive_minpoly(pari, generators)
                input_record = {"generators": generators}
            else:
                raise OracleMismatch(f"unsupported operation {operation!r}")
            assert_equal(
                lean_value,
                expected,
                library=lib,
                case_id=f"{case_id}:{operation}",
                kind=operation,
                input_record=input_record,
                oracle_name="cypari2/PARI",
                oracle_version=oracle_version,
                failure_dir=failure_dir,
                profile=profile,
                seed=seed,
            )
            checked += 1
        except (KeyError, OracleMismatch, ValueError, TypeError) as exc:
            failures += 1
            print(f"FAIL {lib}/{case_id} ({operation}): {exc}", file=sys.stderr)
    print(
        f"number_field_tower_pari.py: checked {checked} case(s), "
        f"{failures} failure(s)",
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
    parser.add_argument("--seed", type=int, default=0)
    args = parser.parse_args(argv)
    fixture_source = str(DEFAULT_FIXTURE) if args.check else args.input
    try:
        import cypari2  # noqa: F401
    except ImportError:
        print("SKIP: cypari2 not installed", file=sys.stderr)
        return 0
    return check(
        fixture_source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
