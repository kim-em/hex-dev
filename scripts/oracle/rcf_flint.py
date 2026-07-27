#!/usr/bin/env python3
"""Independent python-flint oracle for ``hex-rcf`` sentences.

The input is the JSONL stream emitted by ``lake exe hexrcf_emit_fixtures``.
For each version-1 ``rcf_sentence`` record this driver forms the product of
the nonconstant atom polynomials and factors it over ``ZZ``.  Discarding
factor multiplicities gives an independently square-free carrier.  FLINT/Arb
then supplies certified real-root balls for its irreducible factors.

Formula truth is reconstructed without consuming any Lean carrier,
certificate, cells, isolations, or signs.  Open-cell signs are exact Horner
evaluations over ``Fraction``.  At a root cell an atom is zero exactly when
the root's irreducible factor divides it; otherwise continuity gives the sign
from the immediately preceding open cell.  Dyadic bounds and rational roots
are exact.  Nonlinear root balls are refined through a finite precision
ladder until their order and every endpoint comparison are certified.  Any
remaining ambiguity is a hard failure, never a guessed verdict.

Usage::

    lake exe hexrcf_emit_fixtures | python3 scripts/oracle/rcf_flint.py
    python3 scripts/oracle/rcf_flint.py --check
    python3 scripts/oracle/rcf_flint.py path/to/file.jsonl
"""
from __future__ import annotations

import argparse
import os
import sys
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any, Iterator


REPO_ROOT = Path(__file__).resolve().parent.parent.parent
DEFAULT_FIXTURE = REPO_ROOT / "conformance-fixtures" / "HexRCF" / "rcf.jsonl"
DEFAULT_FAILURE_DIR = REPO_ROOT / "conformance-failures"

sys.path.insert(0, str(REPO_ROOT))

from scripts.oracle.common import (  # noqa: E402  (after sys.path insert)
    OracleMismatch,
    read_fixtures,
    write_failure,
)


PREC_LADDER = (64, 128, 256, 512, 1024, 2048, 4096)
DEFAULT_SEED = 0x524346


@dataclass(frozen=True)
class Root:
    """Certified enclosure and irreducible factor for one real root."""

    lower: Fraction
    upper: Fraction
    factor: tuple[int, ...]


def _flint_version() -> str:
    try:
        import flint  # type: ignore[import-not-found]

        return getattr(flint, "__version__", "unknown")
    except Exception:
        return "unknown"


def _trim(coeffs: list[int]) -> list[int]:
    out = list(coeffs)
    while out and out[-1] == 0:
        out.pop()
    return out


def _eval(coeffs: list[int] | tuple[int, ...], x: Fraction) -> Fraction:
    value = Fraction(0)
    for coefficient in reversed(coeffs):
        value = value * x + coefficient
    return value


def _sign(value: Fraction) -> int:
    return (value > 0) - (value < 0)


def _dyadic(pair: list[int]) -> Fraction:
    numerator, exponent = pair
    return Fraction(numerator) * Fraction(2) ** (-exponent)


def _atoms(formula: dict[str, Any]) -> Iterator[dict[str, Any]]:
    tag = formula["tag"]
    if tag == "atom":
        yield formula
    elif tag == "not":
        yield from _atoms(formula["arg"])
    elif tag in {"and", "or", "imp"}:
        yield from _atoms(formula["left"])
        yield from _atoms(formula["right"])


def _carrier_factors(formula: dict[str, Any]) -> list[tuple[int, ...]]:
    """Irreducible factors of the square-free atom product, once each."""
    from flint import fmpz_poly  # type: ignore[import-not-found]

    product = fmpz_poly([1])
    has_nonconstant = False
    for atom in _atoms(formula):
        coeffs = _trim(atom["coeffs"])
        if len(coeffs) > 1:
            product *= fmpz_poly(coeffs)
            has_nonconstant = True
    if not has_nonconstant:
        return []
    _content, factors = product.factor()
    return [tuple(int(c) for c in factor.coeffs()) for factor, _mult in factors]


def _fraction(q: Any) -> Fraction:
    return Fraction(int(q.numer()), int(q.denom()))


def _roots_at_precision(
    factors: list[tuple[int, ...]], endpoints: tuple[Fraction, ...]
) -> list[Root] | None:
    """Return certified ordered roots, or ``None`` when more bits are needed."""
    from flint import fmpz_poly  # type: ignore[import-not-found]

    roots: list[Root] = []
    for factor_coeffs in factors:
        factor = fmpz_poly(list(factor_coeffs))
        degree = factor.degree()
        if degree == 1:
            root = Fraction(-factor_coeffs[0], factor_coeffs[1])
            roots.append(Root(root, root, factor_coeffs))
            continue

        complex_roots = factor.complex_roots()
        if sum(int(mult) for _ball, mult in complex_roots) != degree:
            return None
        for ball, multiplicity in complex_roots:
            if int(multiplicity) != 1:
                raise OracleMismatch(
                    "FLINT returned a multiple root for a square-free irreducible factor"
                )
            if ball.imag.is_zero():
                lower = _fraction(ball.real.lower().fmpq())
                upper = _fraction(ball.real.upper().fmpq())
                roots.append(Root(lower, upper, factor_coeffs))
            elif ball.imag.contains(0):
                return None

    roots.sort(key=lambda root: (root.lower + root.upper) / 2)
    if any(left.upper >= right.lower for left, right in zip(roots, roots[1:])):
        return None

    # A rational endpoint equals this algebraic root iff its irreducible
    # factor vanishes there.  Otherwise the ball must be disjoint from it.
    for root in roots:
        for endpoint in endpoints:
            if _eval(root.factor, endpoint) == 0:
                continue
            if not (root.upper < endpoint or endpoint < root.lower):
                return None
    return roots


def _certified_roots(
    factors: list[tuple[int, ...]], endpoints: tuple[Fraction, ...]
) -> list[Root]:
    from flint import ctx  # type: ignore[import-not-found]

    saved = ctx.prec
    try:
        for precision in PREC_LADDER:
            ctx.prec = precision
            roots = _roots_at_precision(factors, endpoints)
            if roots is not None:
                return roots
    finally:
        ctx.prec = saved
    raise OracleMismatch(
        "FLINT/Arb could not certify real-root order and endpoint relations "
        "within the finite precision ladder"
    )


def _floor(value: Fraction) -> int:
    return value.numerator // value.denominator


def _ceil(value: Fraction) -> int:
    return -((-value.numerator) // value.denominator)


def _open_samples(roots: list[Root]) -> list[Fraction]:
    if not roots:
        return [Fraction(0)]
    samples = [Fraction(_floor(roots[0].lower) - 1)]
    samples.extend(
        (left.upper + right.lower) / 2 for left, right in zip(roots, roots[1:])
    )
    samples.append(Fraction(_ceil(roots[-1].upper) + 1))
    return samples


def _compare(sign: int, comparison: str) -> bool:
    if comparison == "lt":
        return sign < 0
    if comparison == "le":
        return sign <= 0
    if comparison == "eq":
        return sign == 0
    if comparison == "ge":
        return sign >= 0
    if comparison == "gt":
        return sign > 0
    if comparison == "ne":
        return sign != 0
    raise OracleMismatch(f"unsupported comparison {comparison!r}")


def _eval_formula(
    formula: dict[str, Any], sample: Fraction, root: Root | None = None
) -> bool:
    tag = formula["tag"]
    if tag == "tt":
        return True
    if tag == "ff":
        return False
    if tag == "atom":
        coeffs = _trim(formula["coeffs"])
        if root is not None:
            from flint import fmpz_poly  # type: ignore[import-not-found]

            polynomial = fmpz_poly(coeffs)
            factor = fmpz_poly(list(root.factor))
            atom_sign = 0 if (polynomial % factor).is_zero() else _sign(_eval(coeffs, sample))
        else:
            atom_sign = _sign(_eval(coeffs, sample))
        return _compare(atom_sign, formula["cmp"])
    if tag == "not":
        return not _eval_formula(formula["arg"], sample, root)
    if tag == "and":
        return _eval_formula(formula["left"], sample, root) and _eval_formula(
            formula["right"], sample, root
        )
    if tag == "or":
        return _eval_formula(formula["left"], sample, root) or _eval_formula(
            formula["right"], sample, root
        )
    if tag == "imp":
        return (not _eval_formula(formula["left"], sample, root)) or _eval_formula(
            formula["right"], sample, root
        )
    raise OracleMismatch(f"unsupported formula tag {tag!r}")


def _root_cmp(root: Root, endpoint: Fraction) -> int:
    """Sign of ``root - endpoint``, certified by factor or enclosure."""
    if _eval(root.factor, endpoint) == 0:
        return 0
    if root.upper < endpoint:
        return -1
    if endpoint < root.lower:
        return 1
    raise OracleMismatch("an endpoint/root comparison escaped precision certification")


def _bounded_values(
    roots: list[Root],
    open_values: list[bool],
    root_values: list[bool],
    lower: Fraction,
    upper: Fraction,
) -> list[bool]:
    """Values on exactly the cells intersecting the half-open ``(a,b]``."""
    if lower >= upper:
        return []
    relevant: list[bool] = []
    for index, value in enumerate(open_values):
        left_ok = index == 0 or _root_cmp(roots[index - 1], upper) < 0
        right_ok = index == len(roots) or _root_cmp(roots[index], lower) > 0
        if left_ok and right_ok:
            relevant.append(value)
        if index < len(roots):
            above_lower = _root_cmp(roots[index], lower) > 0
            at_or_below_upper = _root_cmp(roots[index], upper) <= 0
            if above_lower and at_or_below_upper:
                relevant.append(root_values[index])
    return relevant


def _decide(sentence: dict[str, Any]) -> bool:
    formula = sentence["formula"]
    bounds = sentence["bounds"]
    quantifier = sentence["quantifier"]
    endpoints: tuple[Fraction, ...]
    if bounds is None:
        endpoints = ()
    else:
        endpoints = (_dyadic(bounds["lower"]), _dyadic(bounds["upper"]))
        if endpoints[0] >= endpoints[1]:
            return quantifier == "forall_ioc"

    roots = _certified_roots(_carrier_factors(formula), endpoints)
    samples = _open_samples(roots)
    open_values = [_eval_formula(formula, sample) for sample in samples]
    # The sample immediately left of root i has the same signs for every
    # atom not divisible by that root's irreducible factor.
    root_values = [
        _eval_formula(formula, samples[index], root)
        for index, root in enumerate(roots)
    ]

    if quantifier in {"forall_real", "exists_real"}:
        values: list[bool] = []
        for index, value in enumerate(open_values):
            values.append(value)
            if index < len(root_values):
                values.append(root_values[index])
    else:
        lower, upper = endpoints
        values = _bounded_values(roots, open_values, root_values, lower, upper)

    if quantifier in {"forall_real", "forall_ioc"}:
        return all(values)
    return any(values)


def check(
    source: str | Path | None,
    *,
    failure_dir: Path,
    profile: str,
    seed: int,
) -> int:
    records = list(read_fixtures(source))
    cases: dict[tuple[str, str], dict[str, Any]] = {}
    results: dict[tuple[str, str], list[dict[str, Any]]] = {}
    failures = 0
    checked = 0
    oracle_version = _flint_version()

    for record in records:
        key = (record["lib"], record["case"])
        if record["kind"] == "result":
            results.setdefault(key, []).append(record)
        elif record["kind"] != "rcf_sentence":
            print(f"FAIL {key[0]}/{key[1]}: expected rcf_sentence fixture", file=sys.stderr)
            failures += 1
        elif key in cases:
            print(f"FAIL {key[0]}/{key[1]}: duplicate fixture record", file=sys.stderr)
            failures += 1
        else:
            cases[key] = record

    for (lib, case_id), record in cases.items():
        emitted = results.pop((lib, case_id), [])
        lean_value: Any = [item.get("value") for item in emitted]
        oracle_value: Any = "not computed"
        try:
            if len(emitted) != 1 or emitted[0]["op"] != "decide":
                raise OracleMismatch(
                    "expected exactly one result with op='decide', got "
                    f"{[(item['op'], item.get('value')) for item in emitted]!r}"
                )
            lean_value = emitted[0]["value"]
            if type(lean_value) is not bool:
                raise OracleMismatch(f"decide result must be bool, got {lean_value!r}")
            oracle_value = _decide(record["sentence"])
            if lean_value != oracle_value:
                raise OracleMismatch(
                    f"Lean verdict {lean_value!r} != python-flint verdict {oracle_value!r}"
                )
            checked += 1
        except OracleMismatch as exc:
            failures += 1
            path = write_failure(
                failure_dir,
                library=lib,
                profile=profile,
                seed=seed,
                case_id=case_id,
                kind="rcf_sentence",
                input_record=record,
                lean_output=lean_value,
                oracle_output=oracle_value,
                oracle_name="python-flint",
                oracle_version=oracle_version,
                diff=str(exc),
            )
            print(f"FAIL {lib}/{case_id}: {exc}\n  failure record: {path}", file=sys.stderr)

    for (lib, case_id), emitted in results.items():
        print(
            f"FAIL {lib}/{case_id}: result record has no matching rcf_sentence fixture "
            f"({len(emitted)} result(s))",
            file=sys.stderr,
        )
        failures += 1

    print(
        f"rcf_flint.py: checked {checked} sentence(s), {failures} failure(s)",
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
    parser.add_argument("--seed", type=int, default=DEFAULT_SEED)
    args = parser.parse_args(argv)

    source: str | None = str(DEFAULT_FIXTURE) if args.check else args.input
    try:
        import flint  # noqa: F401  (presence check)
    except ImportError:
        print("SKIP: python-flint not installed", file=sys.stderr)
        return 0
    return check(
        source,
        failure_dir=Path(args.failure_dir),
        profile=args.profile,
        seed=args.seed,
    )


if __name__ == "__main__":
    raise SystemExit(main())
