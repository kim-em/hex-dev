#!/usr/bin/env python3
"""Check the finite dyadic search against exact Cauchy thresholds."""

from fractions import Fraction
import json
import sys


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def expected_bound(coefficients: list[str]) -> Fraction | None:
    if not coefficients:
        return None
    values = [Fraction(value) for value in coefficients]
    degree = len(values) - 1
    # Independent formula: B must exceed 1 + max |a_i/a_n|.
    threshold = 1 + max((abs(value / values[-1]) for value in values[:-1]), default=0)
    candidates = [Fraction(2**exponent) for exponent in range(1, 2 * (degree + 1) + 1)]
    return next((value for value in candidates if value > threshold), None)


def leading(value, depth: int):
    """Iterated Laurent valuation and rational leading coefficient."""
    if depth == 0:
        coefficient = Fraction(value)
        return ((), coefficient) if coefficient else None
    require(set(value) == {"num", "den"}, "invalid fraction fields")
    terms = []
    for polynomial in (value["num"], value["den"]):
        terms.append(next(((index, signature) for index, coefficient in enumerate(polynomial)
                           if (signature := leading(coefficient, depth - 1)) is not None), None))
    numerator, denominator = terms
    require(denominator is not None, "zero denominator")
    if numerator is None:
        return None
    ni, (nv, nc) = numerator
    di, (dv, dc) = denominator
    return ((ni - di,) + tuple(a - b for a, b in zip(nv, dv)), nc / dc)


def is_constant(value, depth: int) -> bool:
    if depth == 0:
        return True
    return (len(value["num"]) <= 1 and len(value["den"]) == 1
            and all(is_constant(coefficient, depth - 1)
                    for coefficient in value["num"] + value["den"]))


def infinitesimal_bound(coefficients, depth: int) -> Fraction | None:
    require(depth in (1, 2), "unsupported infinitesimal depth")
    signatures = [leading(coefficient, depth) for coefficient in coefficients]
    require(bool(signatures) and signatures[-1] is not None, "zero leading coefficient")
    lead_value, lead_coefficient = signatures[-1]
    for exponent in range(1, 2 * len(coefficients) + 1):
        bound = Fraction(2**exponent)
        accepted = True
        for index, signature in enumerate(signatures[:-1]):
            if signature is None:
                continue
            valuation, coefficient = signature
            relative = tuple(a - b for a, b in zip(valuation, lead_value))
            if relative < (0,) * depth:
                accepted = False
            elif relative == (0,) * depth:
                ratio = abs(coefficient / lead_coefficient)
                if ratio == bound - 1:
                    require(is_constant(coefficients[index], depth)
                            and is_constant(coefficients[-1], depth),
                            "leading-coefficient equality needs higher terms")
                accepted &= ratio < bound - 1
        if accepted:
            return bound
    return None


def verify(fixtures: list[dict]) -> None:
    require(bool(fixtures), "no fixtures")
    require(len({fixture["name"] for fixture in fixtures}) == len(fixtures), "duplicate fixture")
    for fixture in fixtures:
        if fixture["kind"] == "rational":
            expected = expected_bound(fixture["coefficients"])
            actual = Fraction(fixture["bound"]) if fixture["bound"] is not None else None
        else:
            require(fixture["kind"] == "infinitesimal", "unknown fixture kind")
            depth = fixture["depth"]
            expected = infinitesimal_bound(fixture["coefficients"], depth)
            actual = None
            if fixture["bound"] is not None:
                require(is_constant(fixture["bound"], depth), "bound is not a rational constant")
                signature = leading(fixture["bound"], depth)
                actual = signature[1] if signature is not None else Fraction(0)
        require(actual == expected, f"{fixture['name']}: got {actual}, expected {expected}")


def main() -> None:
    fixtures = [json.loads(line) for line in sys.stdin if line.strip()]
    verify(fixtures)
    print(f"verified {len(fixtures)} finite-bound fixtures")


if __name__ == "__main__":
    main()
