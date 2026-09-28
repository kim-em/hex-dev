#!/usr/bin/env python3
"""Exact deflation and zero multiplicities in QQ(epsilon, delta)."""

from fractions import Fraction
import json
import sys

from sympy import QQ
from sympy.polys.fields import field


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def verify(fixtures: list[dict]) -> None:
    require(bool(fixtures), "no fixtures")
    require(len({row["name"] for row in fixtures}) == len(fixtures), "duplicate fixture")
    coefficient_field, epsilon, delta = field("epsilon,delta", QQ)
    variables = (epsilon, delta)

    def decode(value, depth: int):
        if depth == 0:
            number = Fraction(value)
            return coefficient_field(QQ(number.numerator, number.denominator))
        require(set(value) == {"num", "den"}, "invalid fraction fields")
        variable = variables[depth - 1]
        numerator, denominator = (
            sum((decode(a, depth - 1) * variable**i for i, a in enumerate(value[key])),
                coefficient_field.zero)
            for key in ("num", "den")
        )
        require(bool(denominator), "zero denominator")
        return numerator / denominator

    for row in fixtures:
        depth = row["depth"]
        require(depth in (0, 1, 2), "unsupported coefficient depth")
        coefficients = [decode(a, depth) for a in row["coefficients"]]
        require(not coefficients or bool(coefficients[-1]), "zero leading coefficient")
        if row.get("kind") == "zero-factor":
            # The order of the first nonzero coefficient determines the exact
            # power of X, independently of the executable division recurrence.
            multiplicity = next((i for i, a in enumerate(coefficients) if a), 0)
            require(type(row["multiplicity"]) is int and row["multiplicity"] == multiplicity,
                    f"{row['name']}: wrong zero multiplicity")
            actual = [decode(a, depth) for a in row["head"]]
            require(actual == coefficients[multiplicity:],
                    f"{row['name']}: wrong zero quotient or scalar")
            continue
        root = decode(row["root"], depth)
        # Independent Horner recurrence, not the executable long-division kernel.
        quotient = []
        remainder = coefficient_field.zero
        if coefficients:
            remainder = coefficients[-1]
            for coefficient in reversed(coefficients[:-1]):
                quotient.append(remainder)
                remainder = coefficient + root * remainder
            quotient.reverse()
        succeeds = bool(coefficients) and not remainder
        require((row["quotient"] is not None) == succeeds, f"{row['name']}: wrong success result")
        if succeeds:
            actual = [decode(a, depth) for a in row["quotient"]]
            require(actual == quotient, f"{row['name']}: wrong quotient or scalar")
            remaining = coefficient_field.zero
            for coefficient in reversed(quotient):
                remaining = coefficient + root * remaining
            require(decode(row["remaining_at_root"], depth) == remaining,
                    f"{row['name']}: wrong residual evaluation")
        else:
            require(row["remaining_at_root"] is None, f"{row['name']}: result on failed division")


def main() -> None:
    fixtures = [json.loads(line) for line in sys.stdin if line.strip()]
    verify(fixtures)
    print(f"verified {len(fixtures)} exact-deflation and zero-factor fixtures")


if __name__ == "__main__":
    main()
