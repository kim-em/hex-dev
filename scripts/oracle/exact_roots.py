"""Shared exact rational-domain and selected-root sign oracle helpers.

FLINT evaluates original serialized inputs independently of Lean answers.
This neutral test module is shared by Sturm and sign determination.
"""
from fractions import Fraction
from functools import cmp_to_key
from math import lcm
from typing import Any

from scripts.oracle.common import OracleMismatch
from scripts.oracle.real_algebraic_qqbar import QQBar


def require(condition: bool, message: str) -> None:
    if not condition:
        raise OracleMismatch(message)


def rational(value: Any) -> Fraction:
    require(isinstance(value, list) and len(value) == 2 and
            all(type(x) is int for x in value) and value[1] > 0,
            f"invalid exact rational: {value!r}")
    return Fraction(*value)


def polynomial(value: Any) -> list[Fraction]:
    require(isinstance(value, list), "polynomial coefficients must be a list")
    return [rational(c) for c in value]


def endpoint(value: Any) -> tuple[int, Fraction]:
    if value == "-inf":
        return (0, Fraction(0))
    if value == "+inf":
        return (2, Fraction(0))
    return (1, rational(value))


def root_words(data: dict[str, Any]) -> list[list[int]] | None:
    """Exact sign vectors in numerical root order, or domain failure."""
    from flint import fmpq, fmpq_poly

    p = polynomial(data["head"])
    require(isinstance(data["queries"], list), "queries must be an ordered list")
    queries = [polynomial(q) for q in data["queries"]]
    lower, upper = endpoint(data["lower"]), endpoint(data["upper"])
    poly = fmpq_poly([fmpq(c.numerator, c.denominator) for c in p])
    if poly.is_zero() or poly.gcd(poly.derivative()).degree() > 0 or not lower < upper:
        return None
    for tag, value in (lower, upper):
        if tag == 1 and poly(fmpq(value.numerator, value.denominator)) == 0:
            return None
    if poly.degree() == 0:
        return []

    denominator = lcm(*(c.denominator for c in p))
    integers = [int(c * denominator) for c in p]
    words: list[list[int]] = []
    with QQBar() as q:
        roots = q.roots([q.number(c, q.integer) for c in integers], integer=True)
        zero = q.number(0)
        lo = q.number(lower[1]) if lower[0] == 1 else None
        hi = q.number(upper[1]) if upper[0] == 1 else None
        operands = [[q.number(c) for c in reversed(query)] for query in queries]
        roots.sort(key=cmp_to_key(lambda a, b: q.compare(a[0], b[0])))
        for root, multiplicity in roots:
            require(multiplicity == 1, "squarefree root has nonunit multiplicity")
            if lo is not None and q.compare(lo, root) >= 0:
                continue
            if hi is not None and q.compare(root, hi) >= 0:
                continue
            signs = []
            for coefficients in operands:
                value = zero
                for coefficient in coefficients:
                    value = q.binary("add", q.binary("mul", value, root), coefficient)
                sign = q.compare(value, zero)
                signs.append((sign > 0) - (sign < 0))
            words.append(signs)
    return words

