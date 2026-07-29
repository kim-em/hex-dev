#!/usr/bin/env python3
"""SymPy oracle driver for ``hex-mv-poly``.

Reads the JSONL stream emitted by ``lake exe hexmvpoly_emit_fixtures`` and
recomputes canonicalization, arithmetic, degree/leading-term queries,
evaluation, collision-producing transformations, recursive views, and
comparator changes with ``sympy.Poly``.

The oracle is ``if_available`` for local development. Release CI installs
SymPy and preflights its import before invoking this script, so it remains a
hard gate there.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = (
    REPO_ROOT / "conformance-fixtures" / "HexMvPoly" / "mvpoly.jsonl"
)
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402
    OracleMismatch,
    assert_equal,
    read_fixtures,
    split_fixtures_results,
)


def _generators(arity: int):
    from sympy import symbols

    if arity == 0:
        return ()
    gens = symbols(f"x0:{arity}")
    return gens if isinstance(gens, tuple) else (gens,)


def _expression(record: dict[str, Any]):
    from sympy import Integer

    gens = _generators(record["arity"])
    expr = Integer(0)
    for exponents, coefficient in record["terms"]:
        term = Integer(coefficient)
        for gen, exponent in zip(gens, exponents):
            term *= gen**exponent
        expr += term
    return expr, gens


def _poly(record: dict[str, Any]):
    from sympy import Poly

    expr, gens = _expression(record)
    if not gens:
        return expr
    return Poly(expr, *gens, domain="ZZ")


def _canonical_terms(record: dict[str, Any], order: str | None = None) -> list[Any]:
    """Return ascending Hex-order ``[[exponents], coefficient]`` terms."""
    arity = record["arity"]
    polynomial = _poly(record)
    if arity == 0:
        coefficient = int(polynomial)
        return [] if coefficient == 0 else [[[], coefficient]]
    chosen_order = order or record["order"]
    # SymPy enumerates from greatest to least; Hex ExtTreeMap iteration is
    # increasing, hence the reversal.
    return [
        [list(monomial), int(coefficient)]
        for monomial, coefficient in reversed(polynomial.terms(order=chosen_order))
        if coefficient != 0
    ]


def _record_from_expr(
    expr: Any, arity: int, order: str, *, generators: tuple[Any, ...] | None = None
) -> dict[str, Any]:
    from sympy import Poly

    gens = generators if generators is not None else _generators(arity)
    if arity == 0:
        terms = [] if expr == 0 else [[[], int(expr)]]
    else:
        poly = Poly(expr, *gens, domain="ZZ")
        terms = [
            [list(monomial), int(coefficient)]
            for monomial, coefficient in reversed(poly.terms(order=order))
            if coefficient != 0
        ]
    return {
        "kind": "mvpoly",
        "lib": "HexMvPoly",
        "case": "<oracle>",
        "arity": arity,
        "order": order,
        "terms": terms,
    }


def _query(record: dict[str, Any], op: str) -> list[int]:
    arity = record["arity"]
    polynomial = _poly(record)
    terms_desc = list(reversed(_canonical_terms(record)))
    if op == "totalDegree":
        if arity == 0 or not terms_desc:
            return [0]
        return [int(polynomial.total_degree())]
    if op == "degreeOf":
        if arity == 0:
            return []
        if not terms_desc:
            return [0] * arity
        return [int(polynomial.degree(gen)) for gen in polynomial.gens]
    if op == "vars":
        if arity == 0:
            return []
        if not terms_desc:
            return []
        return [
            i for i, gen in enumerate(polynomial.gens)
            if polynomial.degree(gen) > 0
        ]
    if op == "leadingCoeff":
        return [0 if not terms_desc else int(terms_desc[0][1])]
    if op == "leadingTerm":
        if not terms_desc:
            return []
        exponents, coefficient = terms_desc[0]
        return [*exponents, int(coefficient)]
    raise ValueError(f"unknown query op {op!r}")


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
            if op == "canonicalize":
                input_record = cases[(lib, case_id)]
                oracle_value = _canonical_terms(input_record)
            elif op in {"add", "sub", "mul"}:
                left = cases[(lib, f"{case_id}/left")]
                right = cases[(lib, f"{case_id}/right")]
                left_expr, generators = _expression(left)
                right_expr, _ = _expression(right)
                if op == "add":
                    expr = left_expr + right_expr
                elif op == "sub":
                    expr = left_expr - right_expr
                else:
                    expr = left_expr * right_expr
                input_record = {"left": left, "right": right}
                oracle_value = _record_from_expr(
                    expr, left["arity"], left["order"], generators=generators
                )["terms"]
            elif op in {
                "totalDegree",
                "degreeOf",
                "vars",
                "leadingCoeff",
                "leadingTerm",
            }:
                input_record = cases[(lib, case_id)]
                oracle_value = _query(input_record, op)
            elif op == "neg":
                input_record = cases[(lib, case_id)]
                expression, generators = _expression(input_record)
                oracle_value = _record_from_expr(
                    -expression,
                    input_record["arity"],
                    input_record["order"],
                    generators=generators,
                )["terms"]
            elif op.startswith("pow/"):
                input_record = cases[(lib, case_id)]
                expression, generators = _expression(input_record)
                exponent = int(op.removeprefix("pow/"))
                oracle_value = _record_from_expr(
                    expression**exponent,
                    input_record["arity"],
                    input_record["order"],
                    generators=generators,
                )["terms"]
            elif op.startswith("rename/"):
                from sympy import symbols

                input_record = cases[(lib, case_id)]
                expression, generators = _expression(input_record)
                variant = op.removeprefix("rename/")
                if variant == "swapFanIn":
                    targets = symbols("y0:2")
                    mapping = {
                        generators[0]: targets[1],
                        generators[1]: targets[0],
                        generators[2]: targets[1],
                    }
                    target_order = "grlex"
                elif variant == "identity":
                    targets = symbols(f"y0:{input_record['arity']}")
                    mapping = dict(zip(generators, targets, strict=True))
                    target_order = "lex"
                elif variant == "allToX0":
                    targets = (symbols("y"),)
                    mapping = {gen: targets[0] for gen in generators}
                    target_order = "lex"
                else:
                    raise ValueError(f"unknown rename variant {variant!r}")
                renamed = expression.subs(mapping, simultaneous=True)
                oracle_value = _record_from_expr(
                    renamed, len(targets), target_order, generators=targets
                )["terms"]
            elif op.startswith("subst/"):
                from sympy import symbols

                input_record = cases[(lib, case_id)]
                expression, generators = _expression(input_record)
                variant = op.removeprefix("subst/")
                if variant == "typical":
                    targets = symbols("y0:2")
                    mapping = {
                        generators[0]: targets[0] + targets[1],
                        generators[1]: targets[1],
                        generators[2]: 2,
                    }
                    target_order = "grlex"
                elif variant == "allToX0":
                    targets = (symbols("y"),)
                    mapping = {gen: targets[0] for gen in generators}
                    target_order = "lex"
                else:
                    raise ValueError(f"unknown substitution variant {variant!r}")
                substituted = expression.subs(mapping, simultaneous=True)
                oracle_value = _record_from_expr(
                    substituted, len(targets), target_order, generators=targets
                )["terms"]
            elif op.startswith("partialEval/"):
                input_record = cases[(lib, case_id)]
                expression, generators = _expression(input_record)
                variant = op.removeprefix("partialEval/")
                if variant == "x0=2":
                    assignments = {generators[0]: 2}
                elif variant == "all":
                    assignments = dict(
                        zip(generators, [4, 0, -2], strict=True)
                    )
                else:
                    raise ValueError(f"unknown partialEval variant {variant!r}")
                partially_evaluated = expression.subs(
                    assignments, simultaneous=True
                )
                oracle_value = _record_from_expr(
                    partially_evaluated,
                    input_record["arity"],
                    input_record["order"],
                    generators=generators,
                )["terms"]
            elif op.startswith("reorder/"):
                input_record = cases[(lib, case_id)]
                target_order = op.removeprefix("reorder/")
                oracle_value = _canonical_terms(input_record, target_order)
            elif op.startswith("derivative/i"):
                input_record = cases[(lib, case_id)]
                expression, generators = _expression(input_record)
                position = int(op.removeprefix("derivative/i"))
                oracle_value = _record_from_expr(
                    expression.diff(generators[position]),
                    input_record["arity"],
                    input_record["order"],
                    generators=generators,
                )["terms"]
            elif op.startswith("eval/") or op.startswith("evalHorner/"):
                input_record = cases[(lib, case_id)]
                expression, generators = _expression(input_record)
                point = json.loads(op.split("/", 1)[1])
                oracle_value = [
                    int(expression.subs(dict(zip(generators, point, strict=True))))
                ]
            else:
                raise OracleMismatch(
                    f"{lib}/{case_id}: unsupported op {op!r}; extend "
                    "mvpoly_sympy.py"
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
        f"mvpoly_sympy.py: checked {checked} case(s), {failures} failure(s)",
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
