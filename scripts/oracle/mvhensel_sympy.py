#!/usr/bin/env python3
"""SymPy oracle for ``HexMvHensel`` lift and diophantine fixtures.

The oracle uses SymPy's matching Wang/EEZ internals. For the specified case
where a prescribed leading-coefficient term exceeds the working modulus,
SymPy reduces that coefficient and rejects an otherwise exact lift; that case
is checked against SymPy's exact integer factorization, matched independently
by image and prescribed leading coefficient. The result contract remains the
same exact ordered factor tuple for every successful input.
"""

from __future__ import annotations

import argparse
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexMvHensel" / "mvhensel.jsonl"
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
            dmp_zz_diophantine,
            dmp_zz_wang_hensel_lifting,
            dup_zz_diophantine,
        )
    except ImportError as exc:  # pragma: no cover - version-drift diagnostic
        raise RuntimeError(
            "SymPy's Wang/EEZ internal API moved; update mvhensel_sympy.py"
        ) from exc
    return dup_zz_diophantine, dmp_zz_diophantine, dmp_zz_wang_hensel_lifting


def _self_test() -> None:
    """Fail loudly if the pinned internal routines change shape or convention."""
    from sympy.polys.domains import ZZ

    dup, dmp, wang = _internals()
    factors = [[1, 0], [1, 1]]
    if dup(factors, 0, 5, ZZ) != [[1], [-1]]:
        raise RuntimeError("SymPy dup_zz_diophantine convention changed")
    if dmp(factors, [1], [], 1, 5, 0, ZZ) != [[1], [-1]]:
        raise RuntimeError("SymPy dmp_zz_diophantine convention changed")
    lifted = wang(
        [[1], [1, 1], [1, 0]],
        [[1, 0], [1, 1]],
        [[1], [1]],
        [0],
        5,
        1,
        ZZ,
    )
    if lifted != [[[1], [1, 0]], [[1], [1]]]:
        raise RuntimeError("SymPy dmp_zz_wang_hensel_lifting convention changed")


def _generators(arity: int):
    import sympy as sp

    return sp.symbols(f"x0:{arity}")


def _ordered_indices(arity: int, main: int) -> list[int]:
    return [main, *(index for index in range(arity) if index != main)]


def _expression(terms: list[Any], generators: tuple[Any, ...]):
    import sympy as sp

    result = sp.Integer(0)
    for exponents, coefficient in terms:
        term = sp.Integer(coefficient)
        for generator, exponent in zip(generators, exponents):
            term *= generator**exponent
        result += term
    return result


def _dmp(
    terms: list[Any],
    generators: tuple[Any, ...],
    indices: list[int],
):
    import sympy as sp
    from sympy.polys.domains import ZZ

    expression = _expression(terms, generators)
    ordered_generators = tuple(generators[index] for index in indices)
    return sp.Poly(expression, *ordered_generators, domain=ZZ).rep.to_list()


def _leading_dmp(terms: list[Any], side_generators: tuple[Any, ...]):
    import sympy as sp
    from sympy.polys.domains import ZZ

    if not side_generators:
        return int(_expression(terms, ()))
    return sp.Poly(
        _expression(terms, side_generators), *side_generators, domain=ZZ
    ).rep.to_list()


def _univariate_descending(coefficients: list[int]) -> list[int]:
    return list(reversed(coefficients))


def _dmp_terms(
    polynomial,
    *,
    arity: int,
    indices: list[int],
    order: str,
) -> list[Any]:
    from sympy.polys.densebasic import dmp_to_dict
    from sympy.polys.domains import ZZ
    from sympy.polys.orderings import monomial_key

    encoded: list[tuple[tuple[int, ...], int]] = []
    for ordered_exponents, coefficient in dmp_to_dict(
        polynomial, arity - 1, ZZ
    ).items():
        exponents = [0] * arity
        for index, exponent in zip(indices, ordered_exponents):
            exponents[index] = int(exponent)
        encoded.append((tuple(exponents), int(coefficient)))
    encoded.sort(key=lambda term: monomial_key(order)(term[0]))
    return [[list(exponents), coefficient] for exponents, coefficient in encoded]


def _image_terms(coefficients: list[int], arity: int, main: int) -> list[Any]:
    terms = []
    for exponent, coefficient in enumerate(coefficients):
        if coefficient:
            powers = [0] * arity
            powers[main] = exponent
            terms.append([powers, coefficient])
    return terms


def _expression_terms(expression, generators: tuple[Any, ...], order: str) -> list[Any]:
    import sympy as sp
    from sympy.polys.domains import ZZ

    polynomial = sp.Poly(expression, *generators, domain=ZZ)
    return [
        [list(monomial), int(coefficient)]
        for monomial, coefficient in reversed(polynomial.terms(order=order))
        if coefficient
    ]


def _factor_by_contract(record: dict[str, Any]) -> dict[str, Any] | None:
    """Match an exact SymPy factorization to images and prescribed LCs."""
    import sympy as sp

    arity = int(record["arity"])
    main = int(record["main"])
    generators = _generators(arity)
    main_generator = generators[main]
    side_indices = [index for index in range(arity) if index != main]
    side_generators = tuple(generators[index] for index in side_indices)
    target = _expression(record["target"], generators)
    content, powers = sp.factor_list(target, *generators)
    if content != 1:
        return None
    candidates = [
        factor for factor, multiplicity in powers for _ in range(multiplicity)
    ]
    if len(candidates) != len(record["images"]):
        return None
    substitutions = dict(zip(side_generators, record["point"]))
    matched = []
    for image, leading_terms in zip(record["images"], record["leading"]):
        expected_image = sum(
            coefficient * main_generator**degree
            for degree, coefficient in enumerate(image)
        )
        expected_leading = _expression(leading_terms, side_generators)
        found = None
        for index, candidate in enumerate(candidates):
            actual_image = sp.expand(candidate.subs(substitutions))
            actual_leading = sp.Poly(candidate, main_generator).LC()
            if (
                sp.expand(actual_image - expected_image) == 0
                and sp.expand(actual_leading - expected_leading) == 0
            ):
                found = index
                break
        if found is None:
            return None
        matched.append(candidates.pop(found))
    return {
        "factors": [
            _expression_terms(factor, generators, record["order"]) for factor in matched
        ]
    }


def _images_coprime(images: list[list[int]], prime: int) -> bool:
    import sympy as sp

    x = sp.symbols("x")
    polys = [
        sp.Poly(
            sum(coefficient * x**degree for degree, coefficient in enumerate(image)),
            x,
            modulus=prime,
        )
        for image in images
    ]
    for left_index, left in enumerate(polys):
        if left.degree() < 1 or int(images[left_index][-1]) % prime == 0:
            return False
        for right in polys[left_index + 1 :]:
            if left.gcd(right).degree() != 0:
                return False
    return True


def _mvhensel(record: dict[str, Any]) -> dict[str, Any]:
    from sympy.polys.domains import ZZ
    from sympy.polys.polyerrors import ExtraneousFactors

    _, _, wang = _internals()
    arity = int(record["arity"])
    main = int(record["main"])
    prime = int(record["prime"])
    modulus = prime ** int(record["exponent"])
    images = record["images"]
    if not _images_coprime(images, prime):
        return {"failure": "notCoprime"}

    if arity == 1:
        return {"factors": [_image_terms(image, arity, main) for image in images]}

    generators = _generators(arity)
    indices = _ordered_indices(arity, main)
    side_generators = tuple(generators[index] for index in indices[1:])
    target = _dmp(record["target"], generators, indices)
    dense_images = [_univariate_descending(image) for image in images]
    leading = [_leading_dmp(terms, side_generators) for terms in record["leading"]]
    try:
        factors = wang(
            target,
            dense_images,
            leading,
            record["point"],
            modulus,
            arity - 1,
            ZZ,
        )
    except ExtraneousFactors:
        leading_exceeds_modulus = any(
            abs(coefficient) > modulus
            for polynomial in record["leading"]
            for _, coefficient in polynomial
        )
        if leading_exceeds_modulus:
            contracted = _factor_by_contract(record)
            if contracted is not None:
                return contracted
        return {"failure": f"reconstruct:{modulus}"}
    return {
        "factors": [
            _dmp_terms(
                factor,
                arity=arity,
                indices=indices,
                order=record["order"],
            )
            for factor in factors
        ]
    }


def _main_degree(terms: list[Any], main: int) -> int:
    return max((int(exponents[main]) for exponents, _ in terms), default=0)


def _mvdioph(record: dict[str, Any]) -> list[Any] | None:
    from sympy.polys.domains import ZZ
    from sympy.polys.densebasic import dmp_raise

    _, dmp, _ = _internals()
    arity = int(record["arity"])
    main = int(record["main"])
    images = record["images"]
    product_degree = sum(len(image) - 1 for image in images)
    for base, image in zip(record["bases"], images):
        if _main_degree(base, main) + len(image) - 1 > product_degree:
            return None

    generators = _generators(arity)
    indices = _ordered_indices(arity, main)
    rhs = _dmp(record["rhs"], generators, indices)
    dense_images = [
        dmp_raise(_univariate_descending(image), arity - 1, 0, ZZ) for image in images
    ]
    answer = dmp(
        dense_images,
        rhs,
        [0] * (arity - 1),
        max(record["degrees"], default=0),
        int(record["modulus"]),
        arity - 1,
        ZZ,
    )
    return [
        _dmp_terms(
            polynomial,
            arity=arity,
            indices=indices,
            order=record["order"],
        )
        for polynomial in answer
    ]


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
        try:
            if operation == "mvhensel":
                oracle_value: Any = _mvhensel(input_record)
            elif operation == "mvdioph":
                oracle_value = _mvdioph(input_record)
            else:
                raise OracleMismatch(f"unsupported operation {operation!r}")
            assert_equal(
                result["value"],
                oracle_value,
                library=lib,
                case_id=f"{case_id}:{operation}",
                kind=operation,
                input_record=input_record,
                oracle_name="SymPy Wang/EEZ",
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
        f"mvhensel_sympy.py: checked {checked} case(s), {failures} failure(s)",
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
