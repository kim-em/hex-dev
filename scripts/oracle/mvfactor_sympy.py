#!/usr/bin/env python3
"""SymPy oracle for ``HexMvFactor`` public answers and Wang points.

``factor_list`` independently supplies the complete irreducible
factorization and irreducibility decision.  Factor comparison is up to
per-factor sign and permutation after normalization in the fixture's
monomial order.

The point route uses SymPy's matching EEZ internals:
``dmp_zz_wang_test_points``, ``dmp_zz_wang_non_divisors``,
``dmp_zz_wang_lead_coeffs``, and ``dmp_zz_wang``.  A startup check calls one
known case through every internal name so API drift fails loudly instead of
silently dropping route coverage.
"""

from __future__ import annotations

import argparse
from functools import reduce
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexMvFactor" / "mvfactor.jsonl"
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


def _internals():
    try:
        from sympy.polys.factortools import (
            dmp_zz_wang,
            dmp_zz_wang_lead_coeffs,
            dmp_zz_wang_non_divisors,
            dmp_zz_wang_test_points,
        )
    except ImportError as exc:  # pragma: no cover - version-drift diagnostic
        raise RuntimeError(
            "SymPy's Wang/EEZ internal API moved; update mvfactor_sympy.py"
        ) from exc
    return (
        dmp_zz_wang_test_points,
        dmp_zz_wang_non_divisors,
        dmp_zz_wang_lead_coeffs,
        dmp_zz_wang,
    )


def _self_test() -> None:
    """Pin the signatures and conventions of every internal operation."""
    from sympy.polys.domains import ZZ

    test_points, non_divisors, lead_coeffs, wang = _internals()
    f = [[1], [], [1, 0]]  # x^2 + y
    if test_points(f, [], 1, [-1], 1, ZZ) != (1, [1, 0, -1], []):
        raise RuntimeError("SymPy dmp_zz_wang_test_points convention changed")
    if non_divisors([5], 1, 6, ZZ) != [5]:
        raise RuntimeError("SymPy dmp_zz_wang_non_divisors convention changed")
    led = lead_coeffs(
        [[6, 0], [2, 0, 3], [1, 0]],
        [([1, 0], 1)],
        1,
        [5],
        [[3, 5], [10, 1]],
        [5],
        1,
        ZZ,
    )
    if led[1:] != ([[3, 5], [10, 1]], [[3], [2, 0]]):
        raise RuntimeError("SymPy dmp_zz_wang_lead_coeffs convention changed")
    product = [[1], [1, 3], [2, 2]]
    if wang(product, 1, ZZ, seed=[0, 1, -1, 2, -2] * 10) != [
        [[1], [1, 1]],
        [[1], [2]],
    ]:
        raise RuntimeError("SymPy dmp_zz_wang convention changed")


def _generators(arity: int):
    import sympy as sp

    return sp.symbols(f"x0:{arity}")


def _expression(terms: list[Any], generators: tuple[Any, ...]):
    import sympy as sp

    result = sp.Integer(0)
    for exponents, coefficient in terms:
        term = sp.Integer(coefficient)
        for generator, exponent in zip(generators, exponents):
            term *= generator**exponent
        result += term
    return result


def _expression_terms(expression, generators: tuple[Any, ...], order: str) -> list[Any]:
    import sympy as sp
    from sympy.polys.domains import ZZ

    polynomial = sp.Poly(expression, *generators, domain=ZZ)
    return [
        [list(monomial), int(coefficient)]
        for monomial, coefficient in reversed(polynomial.terms(order=order))
        if coefficient
    ]


def _factor_value(record: dict[str, Any]) -> dict[str, Any]:
    import sympy as sp

    generators = _generators(int(record["arity"]))
    expression = _expression(record["terms"], generators)
    content, factors = sp.factor_list(expression, *generators)
    normalized = []
    scalar = int(content)
    for factor, multiplicity in factors:
        polynomial = sp.Poly(factor, *generators)
        leading = polynomial.terms(order=record["order"])[0][1]
        if leading < 0:
            factor = -factor
            if multiplicity % 2:
                scalar = -scalar
        normalized.append(
            {
                "terms": _expression_terms(factor, generators, record["order"]),
                "multiplicity": int(multiplicity),
            }
        )
    normalized.sort(key=_factor_key)
    return {"content": scalar, "factors": normalized}


def _factor_key(entry: dict[str, Any]) -> tuple[Any, ...]:
    terms = tuple(
        (tuple(exponents), coefficient) for exponents, coefficient in entry["terms"]
    )
    return (terms, int(entry["multiplicity"]))


def _canonical_factor_value(value: dict[str, Any]) -> dict[str, Any]:
    return {
        "content": int(value["content"]),
        "factors": sorted(value["factors"], key=_factor_key),
    }


def _primitive_in_variable(expression, variable) -> bool:
    import sympy as sp

    coefficients = sp.Poly(expression, variable).all_coeffs()
    content = reduce(sp.gcd, coefficients)
    return sp.expand(content) in (1, -1)


def _irred_value(record: dict[str, Any]) -> dict[str, Any]:
    import sympy as sp

    generators = _generators(int(record["arity"]))
    expression = _expression(record["terms"], generators)
    content, factors = sp.factor_list(expression, *generators)
    irreducible = (
        abs(int(content)) == 1 and len(factors) == 1 and int(factors[0][1]) == 1
    )
    if not irreducible:
        constructor = "split"
    elif any(
        sp.degree(expression, variable) == 1
        and _primitive_in_variable(expression, variable)
        for variable in generators
    ):
        constructor = "degreeOne"
    else:
        # The non-linear fixtures have an irreducible degree-preserving image
        # at the first (origin) point, so Lean's pre-Kronecker route is fixed.
        constructor = "image"
    return {"irreducible": irreducible, "constructor": constructor}


def _ordered_indices(arity: int, main: int) -> list[int]:
    return [main, *(index for index in range(arity) if index != main)]


def _dmp(terms: list[Any], generators: tuple[Any, ...], indices: list[int]):
    import sympy as sp
    from sympy.polys.domains import ZZ

    expression = _expression(terms, generators)
    ordered = tuple(generators[index] for index in indices)
    return sp.Poly(expression, *ordered, domain=ZZ).rep.to_list()


def _side_terms(
    polynomial,
    *,
    arity: int,
    side_indices: list[int],
    order: str,
) -> list[Any]:
    from sympy.polys.densebasic import dmp_to_dict
    from sympy.polys.domains import ZZ
    from sympy.polys.orderings import monomial_key

    if not side_indices:
        coefficient = int(polynomial)
        return [[[0] * arity, coefficient]] if coefficient else []
    encoded = []
    for side_exponents, coefficient in dmp_to_dict(
        polynomial, len(side_indices) - 1, ZZ
    ).items():
        exponents = [0] * len(side_indices)
        for position, exponent in enumerate(side_exponents):
            exponents[position] = int(exponent)
        encoded.append((tuple(exponents), int(coefficient)))
    encoded.sort(key=lambda term: monomial_key(order)(term[0]))
    return [[list(exponents), coefficient] for exponents, coefficient in encoded]


def _point_value(record: dict[str, Any]) -> dict[str, Any]:
    from sympy.polys.densebasic import dmp_LC
    from sympy.polys.densetools import dmp_eval_tail
    from sympy.polys.domains import ZZ
    from sympy.polys.factortools import dmp_zz_factor, dup_zz_factor_sqf
    from sympy.polys.polyerrors import EvaluationFailed
    from sympy.polys.sqfreetools import dup_sqf_p

    test_points, _, lead_coeffs, _ = _internals()
    arity = int(record["arity"])
    main = int(record["main"])
    level = arity - 1
    generators = _generators(arity)
    indices = _ordered_indices(arity, main)
    side_indices = indices[1:]
    f = _dmp(record["terms"], generators, indices)
    point = record["point"]
    leading = dmp_LC(f, ZZ)
    scalar, factors = dmp_zz_factor(leading, level - 1, ZZ)
    try:
        image_scalar, image, values = test_points(f, factors, scalar, point, level, ZZ)
    except EvaluationFailed:
        if not dmp_eval_tail(leading, point, level - 1, ZZ):
            return {"reject": "degreeDrop"}
        image = dmp_eval_tail(f, point, level, ZZ)
        if not dup_sqf_p(image, ZZ):
            return {"reject": "notSquarefree"}
        return {"reject": "leadingSplit"}

    _, image_factors = dup_zz_factor_sqf(image, ZZ)
    _, scaled_images, assigned = lead_coeffs(
        f,
        factors,
        image_scalar,
        values,
        image_factors,
        point,
        level,
        ZZ,
    )
    return {
        "images": [
            list(reversed([int(c) for c in factor])) for factor in scaled_images
        ],
        "leading": [
            _side_terms(
                factor,
                arity=arity - 1,
                side_indices=side_indices,
                order=record["order"],
            )
            for factor in assigned
        ],
    }


def _point_key(pair: tuple[Any, Any]) -> tuple[Any, ...]:
    image, leading = pair
    return (
        tuple(image),
        tuple((tuple(exponents), coefficient) for exponents, coefficient in leading),
    )


def _canonical_point_value(value: dict[str, Any]) -> dict[str, Any]:
    if "reject" in value:
        return value
    pairs = sorted(zip(value["images"], value["leading"]), key=_point_key)
    return {
        "images": [image for image, _ in pairs],
        "leading": [leading for _, leading in pairs],
    }


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    _self_test()
    cases, results = split_fixtures_results(read_fixtures(source))
    version = _sympy_version()
    failures = 0
    checked = 0
    for result in results:
        lib = result["lib"]
        case_id = result["case"]
        operation = result["op"]
        input_record = cases[(lib, case_id)]
        lean_value = result["value"]
        try:
            if operation == "mvfactor":
                lean_value = _canonical_factor_value(lean_value)
                oracle_value: Any = _factor_value(input_record)
            elif operation == "mvirred":
                oracle_value = _irred_value(input_record)
            elif operation == "mvpoint":
                lean_value = _canonical_point_value(lean_value)
                oracle_value = _canonical_point_value(_point_value(input_record))
            else:
                raise OracleMismatch(f"unsupported operation {operation!r}")
            assert_equal(
                lean_value,
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{operation}",
                kind=operation,
                input_record=input_record,
                oracle_name="SymPy factor_list/Wang EEZ",
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
        f"mvfactor_sympy.py: checked {checked} case(s), {failures} failure(s)",
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
    try:
        return check(
            input_path,
            failure_dir=Path(args.failure_dir),
            profile=args.profile,
            seed=args.seed,
        )
    except RuntimeError as exc:
        print(f"FAIL: {exc}", file=sys.stderr)
        return 1


if __name__ == "__main__":
    raise SystemExit(main())
