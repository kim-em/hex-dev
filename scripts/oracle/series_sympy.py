#!/usr/bin/env python3
"""SymPy oracle for ``hex-truncated-series`` JSONL fixtures.

The implementation intentionally uses ``sympy.polys.ring_series`` rather
than expanding expressions through SymPy's generic series machinery.  This
matches Hex's fixed-precision coefficient model and independently exercises
the same operation surface: bounded products, inverse, roots, exp/log,
substitution, and reversion.
"""
from __future__ import annotations

from fractions import Fraction
import json
import sys
from typing import Any


def _decode(value: dict[str, list[int]]) -> list[Fraction]:
    return [Fraction(a, b) for a, b in zip(value["num"], value["den"], strict=True)]


def _encode(values: list[Any]) -> dict[str, list[int]]:
    coeffs = [Fraction(str(value)) for value in values]
    return {
        "num": [q.numerator for q in coeffs],
        "den": [q.denominator for q in coeffs],
    }


def _load() -> tuple[list[dict[str, Any]], dict[str, dict[str, Any]]]:
    records = [json.loads(line) for line in sys.stdin if line.strip()]
    cases = {
        record["case"]: record
        for record in records
        if record.get("kind") == "series"
    }
    results = [record for record in records if record.get("kind") == "result"]
    return results, cases


def _ring(record: dict[str, Any], *, variables: str = "x"):
    from sympy.polys.domains import QQ, ZZ
    from sympy.polys.rings import ring

    domain = ZZ if record["domain"] == "ZZ" else QQ
    return ring(variables, domain)


def _poly(record: dict[str, Any], ring_obj, x):
    values = _decode(record["coeffs"])
    domain = ring_obj.domain
    out = ring_obj.zero
    for i, value in enumerate(values):
        coeff = domain(int(value)) if value.denominator == 1 else domain(value.numerator, value.denominator)
        out += coeff * x**i
    return out


def _coeffs(poly, variable_index: int, precision: int) -> list[Any]:
    data = poly.to_dict()
    arity = len(poly.ring.gens)
    out = []
    for i in range(precision):
        exponent = [0] * arity
        exponent[variable_index] = i
        out.append(data.get(tuple(exponent), poly.ring.domain.zero))
    return out


def _unit(record: dict[str, Any], value: Fraction) -> bool:
    if record["domain"] == "ZZ":
        return value in (Fraction(1), Fraction(-1))
    return value != 0


def _reversion(record: dict[str, Any], precision: int):
    from sympy.polys.ring_series import rs_series_reversion

    ring_obj, x, y = _ring(record, variables="x,y")
    p = _poly(record, ring_obj, x)
    return _coeffs(rs_series_reversion(p, x, precision, y), 1, precision)


def _series_result(
    result: dict[str, Any], cases: dict[str, dict[str, Any]]
) -> Any:
    from sympy.polys.ring_series import (
        rs_exp,
        rs_log,
        rs_mul,
        rs_nth_root,
        rs_pow,
        rs_series_inversion,
        rs_subs,
        rs_trunc,
    )

    case_id = result["case"]
    op = result["op"]
    expected = result["value"]

    if op == "comp?" or op in {"comp", "compHorner"}:
        outer = cases[f"{case_id}/outer"]
        inner = cases[f"{case_id}/inner"]
        ring_obj, x = _ring(outer)
        n = outer["precision"]
        a = _poly(outer, ring_obj, x)
        b = _poly(inner, ring_obj, x)
        b0 = _decode(inner["coeffs"])[0] if n else Fraction(0)
        if op == "comp?" and b0 != 0:
            return None
        return _encode(_coeffs(rs_subs(a, {x: b}, x, n), 0, n))

    record = cases[case_id]
    ring_obj, x = _ring(record)
    n = record["precision"]
    p = _poly(record, ring_obj, x)
    raw = _decode(record["coeffs"])
    c0 = raw[0] if n else Fraction(0)

    if n == 0 and op in {"exp", "log"}:
        return _encode([])
    if n <= 1 and (op == "revLagrange" or op.startswith("revOfUnit/")):
        return _encode([Fraction(0)] * n)

    if op == "neg":
        answer = -p
        precision = n
    elif op == "add/self":
        answer = p + p
        precision = n
    elif op == "mul/self":
        answer = rs_mul(p, p, x, n)
        precision = n
    elif op.startswith("pow/"):
        answer = rs_pow(p, int(op.split("/")[1]), x, n)
        precision = n
    elif op.startswith("mulUpTo/"):
        bound = int(op.split("/")[1])
        answer = rs_mul(p, p, x, min(bound, n))
        precision = n
    elif op == "truncate/self":
        answer = rs_trunc(p, x, n)
        precision = n
    elif op == "extend/plus1":
        return _encode(raw + [Fraction(0)])
    elif op.startswith("mulXPow/"):
        shift = int(op.split("/")[1])
        answer = rs_trunc(p * x**shift, x, n)
        precision = n
    elif op == "valuation?":
        return next((i for i, value in enumerate(raw) if value != 0), None)
    elif op == "deriv":
        answer = p.diff(x)
        precision = max(n - 1, 0)
    elif op == "integrate":
        values = [Fraction(0)] + [value / (i + 1) for i, value in enumerate(raw)]
        return _encode(values)
    elif op == "inv?" or op.startswith("invOfUnit/"):
        if n == 0:
            return _encode([])
        if op == "inv?" and not _unit(record, c0):
            return None
        answer = rs_series_inversion(p, x, n)
        precision = n
    elif op == "exp":
        answer = rs_exp(p, x, n)
        precision = n
    elif op == "log":
        answer = rs_log(p, x, n)
        precision = n
    elif op.startswith("sqrtOfRoot/"):
        if n == 0:
            return _encode([])
        root = int(op.split("/")[1])
        answer = rs_nth_root(p, 2, x, n)
        if root < 0:
            answer = -answer
        precision = n
    elif op.startswith("sqrt?/"):
        root = Fraction(int(op.split("/")[1]))
        if n == 0:
            return _encode([])
        if root * root != c0:
            return None
        if n <= 1:
            return _encode([root])
        if not _unit(record, 2 * root):
            return None
        answer = rs_nth_root(p, 2, x, n)
        if root < 0:
            answer = -answer
        precision = n
    elif op == "rev?":
        if c0 != 0:
            return None
        if n <= 1:
            return _encode([Fraction(0)] * n)
        linear = raw[1]
        if not _unit(record, linear):
            return None
        return _encode(_reversion(record, n))
    elif op.startswith("revOfUnit/") or op == "revLagrange":
        return _encode(_reversion(record, n))
    elif op.startswith("divXPow?/"):
        shift = int(op.split("/")[1])
        if any(value != 0 for value in raw[: min(shift, n)]):
            return None
        return _encode(raw[shift:n])
    elif op == "mulThenExtend/3":
        squared = rs_mul(p, p, x, n)
        return _encode(_coeffs(squared, 0, n) + [0])
    elif op == "extendThenMul/3":
        answer = rs_mul(p, p, x, 3)
        precision = 3
    else:
        raise ValueError(f"unknown operation {op!r}")

    # A `None` result has already returned. For series values, the result type's
    # precision is fixed by the operation rather than by polynomial degree.
    if expected is None:
        raise AssertionError(f"oracle unexpectedly produced a value for {case_id} {op}")
    return _encode(_coeffs(answer, 0, precision))


def main() -> int:
    try:
        import sympy  # noqa: F401
    except ImportError:
        print("SKIP: HexTruncatedSeries SymPy oracle unavailable")
        return 0

    results, cases = _load()
    failures = 0
    for result in results:
        try:
            oracle = _series_result(result, cases)
            if oracle != result["value"]:
                failures += 1
                print(
                    f"FAIL {result['case']} {result['op']}: "
                    f"Lean={result['value']!r} SymPy={oracle!r}",
                    file=sys.stderr,
                )
        except Exception as exc:  # keep the case marker visible in sequential CI
            failures += 1
            print(
                f"ERROR {result['case']} {result['op']}: {type(exc).__name__}: {exc}",
                file=sys.stderr,
            )
    if failures:
        print(f"HexTruncatedSeries SymPy oracle: {failures} failure(s)", file=sys.stderr)
        return 1
    print(f"HexTruncatedSeries SymPy oracle: checked {len(results)} results")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
