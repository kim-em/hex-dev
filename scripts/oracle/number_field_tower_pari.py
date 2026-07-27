#!/usr/bin/env python3
"""PARI oracle for ``HexNumberFieldTower``.

The input is the JSONL stream emitted by
``lake exe hexnumberfieldtower_emit_fixtures``. Generator polynomials are
original inputs, not Lean-produced primitive presentations. From those inputs
the oracle independently:

* builds the requested relative-degree composita with ``polcompositum``;
* factors inputs with ``nffactor`` and compares actual monic factors and
  multiplicities after interpreting Lean's exact mixed-radix coordinates;
* computes splitting fields with ``nfsplitting`` and compares their degrees;
* enumerates the specified signed shifts, computes primitive-element
  resultants, requires linear coordinate recovery, and compares the first
  accepted irreducible polynomial.

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
    return pari.Polrev(coeffs, variable)


def _degree(pari, polynomial) -> int:
    return int(pari.poldegree(polynomial))


def _factor_rows(pari, factorization) -> list[tuple[Any, int]]:
    rows = int(pari.matsize(factorization)[0])
    return [
        (factorization[i, 0], int(factorization[i, 1]))
        for i in range(rows)
    ]


def _generators(cases: dict[tuple[str, str], dict[str, Any]], lib: str, case_id: str) -> list[list[int]]:
    generators: list[list[int]] = []
    index = 0
    while (lib, f"{case_id}/generator/{index}") in cases:
        generators.append(_coeffs(cases[(lib, f"{case_id}/generator/{index}")]))
        index += 1
    return generators


def _embedding_boxes(
    cases: dict[tuple[str, str], dict[str, Any]], lib: str, case_id: str
) -> list[list[Any]]:
    boxes: list[list[Any]] = []
    index = 0
    while (lib, f"{case_id}/embedding/{index}") in cases:
        record = cases[(lib, f"{case_id}/embedding/{index}")]
        if record["kind"] != "matrix":
            raise OracleMismatch(
                f"expected embedding matrix, got {record['kind']!r}"
            )
        rows = record["rows"]
        if len(rows) != 3 or len(rows[0]) != 2 or len(rows[1]) != 2:
            raise OracleMismatch("malformed generator embedding box")
        boxes.append([rows[0], rows[1], int(rows[2][0])])
        index += 1
    return boxes


def _compositum(pari, generators: list[list[int]], degrees: list[int]):
    """Build the requested tower compositum and retain every generator map."""
    if len(generators) != len(degrees):
        raise OracleMismatch("generator and relative-degree counts differ")
    if not generators:
        return None, []
    current = _pari_poly(pari, generators[0], "y")
    current_degree = _degree(pari, current)
    if current_degree != degrees[0]:
        raise OracleMismatch(
            "first relative degree does not match its absolute polynomial"
        )
    y = pari("y")
    embeddings = [pari.Mod(y, current)]
    for coefficients, relative_degree in zip(generators[1:], degrees[1:]):
        target = current_degree * relative_degree
        extension = _pari_poly(pari, coefficients, "y")
        components = [
            component
            for component in pari.polcompositum(current, extension, 1)
            if _degree(pari, component[0]) == target
        ]
        if not components:
            raise OracleMismatch(
                f"polcompositum has no component of requested degree {target}"
            )
        component = components[0]
        new_polynomial = component[0]
        old_primitive = component[1]
        new_generator = component[2]
        embeddings = [
            pari.subst(pari.lift(embedding), y, old_primitive)
            for embedding in embeddings
        ]
        embeddings.append(new_generator)
        current = new_polynomial
        current_degree = target
    return current, embeddings


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


def _linear_recovery(
    pari,
    theta_coeffs: list[int],
    alpha_coeffs: list[int],
    gamma_coeffs: list[int],
    shift: int,
) -> bool:
    """Whether the two exact relations recover the new generator linearly."""
    if shift == 0:
        return False
    x = pari("x")
    y = pari("y")
    z = pari("z")
    gamma_polynomial = _pari_poly(pari, gamma_coeffs, "y")
    gamma = pari.Mod(y, gamma_polynomial)
    theta_relation = pari.subst(
        _pari_poly(pari, theta_coeffs, "z"), z, gamma - shift * x
    )
    alpha_relation = _pari_poly(pari, alpha_coeffs, "x")
    common = pari.gcd(theta_relation, alpha_relation)
    return _degree(pari, common) == 1


def _primitive_minpoly(
    pari,
    generators: list[list[int]],
    degrees: list[int],
    boxes: list[list[Any]],
) -> list[int]:
    """First full-degree, linearly recoverable signed-shift polynomial."""
    if len(generators) != len(degrees):
        raise OracleMismatch("generator and relative-degree counts differ")
    if len(generators) != len(boxes):
        raise OracleMismatch("generator and embedding-box counts differ")
    if len(generators) < 2:
        raise OracleMismatch("flatten oracle cases must exercise a genuine search")
    current_coeffs = generators[0]
    current_degree = degrees[0]
    if len(current_coeffs) - 1 != current_degree:
        raise OracleMismatch(
            "first relative degree does not match its absolute polynomial"
        )
    imaginary_unit = pari("I")

    def box_data(box):
        center = _rat(pari, box[0]) + _rat(pari, box[1]) * imaginary_unit
        error = pari(2) ** (-int(box[2]))
        return center, error

    current_center, current_error = box_data(boxes[0])
    for alpha_coeffs, relative_degree, box in zip(
        generators[1:], degrees[1:], boxes[1:]
    ):
        alpha_center, alpha_error = box_data(box)
        target = current_degree * relative_degree
        count = 2 * math.comb(target, 2) + 1
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
            candidates = sorted(
                (
                    _poly_coeffs(pari, factor)
                    for factor, _ in _factor_rows(pari, factorization)
                    if _degree(pari, factor) == target
                ),
                key=lambda coefficients: tuple(coefficients),
            )
            recoverable = [
                coefficients
                for coefficients in candidates
                if _linear_recovery(
                    pari, current_coeffs, alpha_coeffs, coefficients, shift
                )
            ]
            target_center = current_center + shift * alpha_center
            target_error = current_error + abs(shift) * alpha_error
            matching = []
            for coefficients in recoverable:
                roots = pari.polroots(_pari_poly(pari, coefficients, "x"))
                distance = min(pari.abs(root - target_center) for root in roots)
                if float(distance) <= 4.0 * float(target_error) + 1.0e-20:
                    matching.append(coefficients)
            if len(matching) > 1:
                raise OracleMismatch(
                    "embedding box matches multiple recoverable full-degree factors"
                )
            if matching:
                accepted = matching[0]
                current_center = target_center
                current_error = target_error
                break
        if accepted is None:
            raise OracleMismatch(
                f"no recoverable primitive element in {count} signed shifts"
            )
        current_coeffs = accepted
        current_degree = target
    return current_coeffs


def _rat(pari, value: list[int]):
    if len(value) != 2 or int(value[1]) <= 0:
        raise OracleMismatch(f"invalid rational pair {value!r}")
    return pari(int(value[0])) / pari(int(value[1]))


def _coordinate(pari, coordinates, degrees: list[int], embeddings):
    dimension = math.prod(degrees)
    if not degrees:
        dimension = 1
    if len(coordinates) != dimension:
        raise OracleMismatch(
            f"coordinate length {len(coordinates)} != tower dimension {dimension}"
        )
    value = pari(0)
    for index, coefficient in enumerate(coordinates):
        term = _rat(pari, coefficient)
        quotient = index
        for degree, generator in zip(degrees, embeddings):
            exponent = quotient % degree
            quotient //= degree
            term *= generator ** exponent
        if quotient:
            raise OracleMismatch("mixed-radix coordinate index overflow")
        value += term
    return value


def _coordinate_polynomial(pari, coefficients, degrees, embeddings):
    values = [
        _coordinate(pari, coordinate, degrees, embeddings)
        for coordinate in coefficients
    ]
    return pari.Polrev(values, "x")


def _monic_signature(pari, factor, exponent: int) -> list[Any]:
    leading = pari.pollead(factor)
    if leading == 0:
        raise OracleMismatch("zero factor in factorization")
    monic = factor / leading
    return [str(pari.liftall(monic)), int(exponent)]


def _factor_signatures(
    pari,
    generators: list[list[int]],
    input_coeffs: list[int],
    value: dict[str, Any],
) -> tuple[list[list[Any]], list[list[Any]]]:
    degrees = [int(degree) for degree in value["degrees"]]
    field_polynomial, embeddings = _compositum(pari, generators, degrees)
    dimension = math.prod(degrees) if degrees else 1
    if int(value["dimension"]) != dimension:
        raise OracleMismatch(
            f"Lean dimension {value['dimension']} != requested dimension {dimension}"
        )
    if field_polynomial is not None and _degree(pari, field_polynomial) != dimension:
        raise OracleMismatch("PARI compositum has the wrong tower dimension")

    input_polynomial = _pari_poly(pari, input_coeffs, "x")
    if field_polynomial is None:
        oracle_rows = _factor_rows(pari, pari.factor(input_polynomial))
    else:
        oracle_rows = _factor_rows(
            pari, pari.nffactor(pari.nfinit(field_polynomial), input_polynomial)
        )
    oracle_signature = sorted(
        _monic_signature(pari, factor, exponent)
        for factor, exponent in oracle_rows
        if _degree(pari, factor) > 0
    )

    lean_factors = []
    reconstructed = _coordinate(pari, value["scalar"], degrees, embeddings)
    for entry in value["factors"]:
        factor = _coordinate_polynomial(
            pari, entry["coefficients"], degrees, embeddings
        )
        exponent = int(entry["multiplicity"])
        if exponent <= 0:
            raise OracleMismatch("Lean emitted a non-positive multiplicity")
        lean_factors.append(_monic_signature(pari, factor, exponent))
        reconstructed *= factor ** exponent
    if reconstructed != input_polynomial:
        raise OracleMismatch("Lean scalar and factors do not reconstruct the input")
    return sorted(lean_factors), oracle_signature


def _split_summary(pari, input_coeffs: list[int]) -> list[int]:
    polynomial = _pari_poly(pari, input_coeffs, "x")
    factorization = pari.factor(polynomial)
    rows = _factor_rows(pari, factorization)
    irreducible_factors = []
    multiplicities: list[int] = []
    for factor, exponent in rows:
        if _degree(pari, factor) <= 0:
            continue
        irreducible_factors.append(factor)
        multiplicities.extend([exponent] * _degree(pari, factor))
    if not irreducible_factors:
        return [1, 0]
    splitting = pari.nfsplitting(irreducible_factors[0])
    for factor in irreducible_factors[1:]:
        next_splitting = pari.nfsplitting(factor)
        components = list(pari.polcompositum(splitting, next_splitting))
        if not components:
            raise OracleMismatch("splitting-field compositum returned no component")
        splitting = max(
            components, key=lambda polynomial: _degree(pari, polynomial)
        )
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
            if operation == "factorization":
                input_coeffs = _coeffs(cases[(lib, f"{case_id}/input")])
                lean_value, expected = _factor_signatures(
                    pari, generators, input_coeffs, lean_value
                )
                input_record = {
                    "generators": generators,
                    "polynomial": input_coeffs,
                }
            elif operation == "split":
                input_coeffs = _coeffs(cases[(lib, f"{case_id}/input")])
                expected = _split_summary(pari, input_coeffs)
                input_record = {"polynomial": input_coeffs}
            elif operation == "flatten_minpoly":
                degrees = [int(degree) for degree in lean_value["degrees"]]
                boxes = _embedding_boxes(cases, lib, case_id)
                expected = _primitive_minpoly(pari, generators, degrees, boxes)
                lean_value = lean_value["minpoly"]
                input_record = {
                    "generators": generators,
                    "degrees": degrees,
                    "embedding_boxes": boxes,
                }
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
