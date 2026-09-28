#!/usr/bin/env python3
"""Exact deflation, bisection and frontier checks using FLINT and QQ(epsilon, delta)."""

from fractions import Fraction
from pathlib import Path
import json
import sys

from sympy import QQ, Poly, symbols
from sympy.polys.fields import field

sys.path.insert(0, str(Path(__file__).resolve().parents[2]))


def require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def divide_linear(coefficients, root, zero):
    quotient = []
    remainder = zero
    if coefficients:
        remainder = coefficients[-1]
        for coefficient in reversed(coefficients[:-1]):
            quotient.append(remainder)
            remainder = coefficient + root * remainder
        quotient.reverse()
    return quotient, remainder


def root_checks(name, depth, coefficient_field):
    from flint import fmpq, fmpq_poly
    from scripts.oracle.real_algebraic_qqbar import QQBar

    def sign(value):
        if not value:
            return 0
        # delta is infinitesimal over the entire epsilon field. Compare the
        # least delta power first, then the least epsilon power within it.
        def initial(polynomial):
            _, coefficient = min(polynomial.items(), key=lambda item: tuple(reversed(item[0])))
            return 1 if coefficient > 0 else -1
        return initial(value.numer) * initial(value.denom)

    def evaluate(poly, value):
        result = coefficient_field.zero
        for coefficient in reversed(poly):
            result = coefficient + value * result
        return result

    def formal_polynomial(poly):
        x = symbols("X")
        return Poly.from_list([c.as_expr() for c in reversed(poly)], x,
                              domain=coefficient_field.to_domain())

    def squarefree(poly):
        if depth == 0:
            p = fmpq_poly([fmpq(str(c)) for c in poly])
            return p.gcd(p.derivative()).degree() == 0
        p = formal_polynomial(poly)
        return p.gcd(p.diff()).degree() == 0

    def count(poly, a, b):
        if depth == 0:
            # FLINT's exact algebraic roots; no native Sturm recurrence is replayed.
            with QQBar() as q:
                lo, hi = q.number(str(a)), q.number(str(b))
                roots = q.roots([q.number(str(c)) for c in poly])
                require(all(m == 1 for _, m in roots), f"{name}: repeated active root")
                return sum(q.compare(lo, root) < 0 and q.compare(root, hi) < 0 for root, _ in roots)
        _, factors = formal_polynomial(poly).factor_list()
        roots = []
        for factor, multiplicity in factors:
            require(multiplicity == 1, f"{name}: repeated active root")
            require(factor.degree() == 1, f"{name}: unsupported infinitesimal factor")
            roots.append(coefficient_field.from_expr(-factor.nth(0) / factor.nth(1)))
        return sum(sign(root - a) > 0 and sign(b - root) > 0 for root in roots)

    return sign, evaluate, squarefree, count


def verify_bisection(row, decode, coefficient_field):
    name, depth = row["name"], row["depth"]
    coefficients = [decode(a, depth) for a in row["coefficients"]]
    lower, upper, point = (decode(row[key], depth) for key in ("lower", "upper", "point"))
    require(point == (lower + upper) / 2, f"{name}: wrong midpoint")
    require(not coefficients or bool(coefficients[-1]), f"{name}: zero leading coefficient")

    sign, evaluate, squarefree, count = root_checks(name, depth, coefficient_field)

    valid = bool(coefficients) and squarefree(coefficients) and sign(upper - lower) > 0
    valid = valid and bool(evaluate(coefficients, lower)) and bool(evaluate(coefficients, upper))
    payload = row["result"]
    require((payload is not None) == valid, f"{name}: wrong split success")
    if not valid:
        require(row["original_count"] is None, f"{name}: count on invalid domain")
        return

    require(type(row["original_count"]) is int and row["original_count"] == count(coefficients, lower, upper),
            f"{name}: wrong original count")
    require(set(payload) == {"removed", "active", "left_head", "right_head", "left_lower", "left_upper",
                             "right_lower", "right_upper", "left_count", "right_count"},
            f"{name}: invalid split fields")
    removed = not evaluate(coefficients, point)
    require((payload["removed"] is not None) == removed, f"{name}: wrong removed point")
    if removed:
        require(decode(payload["removed"], depth) == point, f"{name}: wrong removed point")
    expected = divide_linear(coefficients, point, coefficient_field.zero)[0] if removed else coefficients
    active = [decode(c, depth) for c in payload["active"]]
    require(active == expected, f"{name}: wrong active head or scalar")
    require(bool(evaluate(active, point)), f"{name}: cut remains a root")
    for side, a, b in (("left", lower, point), ("right", point, upper)):
        require([decode(c, depth) for c in payload[side + "_head"]] == active,
                f"{name}: wrong {side} head")
        for key, expected_endpoint in (("lower", a), ("upper", b)):
            endpoint = payload[side + "_" + key]
            require(isinstance(endpoint, dict) and set(endpoint) == {"finite"} and
                    decode(endpoint["finite"], depth) == expected_endpoint,
                    f"{name}: wrong {side} {key} endpoint")
        actual_count = payload[side + "_count"]
        require(type(actual_count) is int and actual_count == count(active, a, b),
                f"{name}: wrong {side} count")
    require(payload["left_count"] + payload["right_count"] + int(removed) == row["original_count"],
            f"{name}: lost or duplicated root")


def verify_frontier(row, decode, coefficient_field):
    from functools import cmp_to_key

    name, depth = row["name"], row["depth"]
    sign, evaluate, squarefree, count = root_checks(name, depth, coefficient_field)
    coefficients = [decode(a, depth) for a in row["coefficients"]]
    lower, upper = (decode(row[key], depth) for key in ("lower", "upper"))
    require(not coefficients or bool(coefficients[-1]), f"{name}: zero leading coefficient")
    valid = bool(coefficients) and squarefree(coefficients) and sign(upper - lower) > 0
    valid = valid and bool(evaluate(coefficients, lower)) and bool(evaluate(coefficients, upper))
    payload = row["result"]
    require((payload is not None) == valid, f"{name}: wrong frontier success")
    if not valid:
        require(row["original_count"] is None, f"{name}: count on invalid domain")
        return
    require(set(payload) == {"active", "removed", "nodes", "cells"}, f"{name}: invalid frontier fields")
    require(type(row["original_count"]) is int and row["original_count"] == count(coefficients, lower, upper),
            f"{name}: wrong original count")
    removed = [decode(a, depth) for a in payload["removed"]]
    expected = coefficients
    for i, root in enumerate(removed):
        require(root not in removed[:i], f"{name}: duplicate emitted root")
        require(sign(root - lower) > 0 and sign(upper - root) > 0, f"{name}: emitted root outside domain")
        expected, remainder = divide_linear(expected, root, coefficient_field.zero)
        require(not remainder, f"{name}: emitted nonroot")
    active = [decode(a, depth) for a in payload["active"]]
    require(active == expected, f"{name}: wrong active head or scalar")
    require(all(evaluate(active, root) for root in removed), f"{name}: emitted root remains active")
    cells = payload["cells"]
    require(isinstance(cells, list) and bool(cells), f"{name}: no retained cells")
    nodes, cap = payload["nodes"], 2 * len(coefficients)
    require(type(nodes) is int and 0 <= nodes <= cap, f"{name}: wrong node allowance")
    require(len(cells) == nodes + 1, f"{name}: lost or duplicated cell")
    intervals = []
    for cell in cells:
        require(set(cell) == {"head", "lower", "upper", "count"}, f"{name}: invalid cell fields")
        require([decode(a, depth) for a in cell["head"]] == active, f"{name}: stale pending head")
        ends = []
        for key in ("lower", "upper"):
            endpoint = cell[key]
            require(isinstance(endpoint, dict) and set(endpoint) == {"finite"}, f"{name}: invalid cell endpoint")
            ends.append(decode(endpoint["finite"], depth))
        a, b = ends
        require(sign(b - a) > 0, f"{name}: reversed cell")
        require(evaluate(active, a) and evaluate(active, b), f"{name}: active root endpoint")
        require(type(cell["count"]) is int and cell["count"] == count(active, a, b),
                f"{name}: wrong cached count")
        intervals.append((a, b))
    intervals.sort(key=cmp_to_key(lambda a, b: sign(a[0] - b[0])))
    require(intervals[0][0] == lower and intervals[-1][1] == upper and
            all(a[1] == b[0] for a, b in zip(intervals, intervals[1:])),
            f"{name}: interval gap or overlap")
    require(nodes == cap or all(cell["count"] <= 1 for cell in cells), f"{name}: premature traversal stop")
    require(sum(cell["count"] for cell in cells) + len(removed) == row["original_count"],
            f"{name}: inconsistent root coverage")


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
        require(row.get("kind", "deflation") in ("deflation", "bisection", "frontier"), "unknown fixture kind")
        if row.get("kind") == "frontier":
            verify_frontier(row, decode, coefficient_field)
            continue
        if row.get("kind") == "bisection":
            verify_bisection(row, decode, coefficient_field)
            continue
        coefficients = [decode(a, depth) for a in row["coefficients"]]
        root = decode(row["root"], depth)
        require(not coefficients or bool(coefficients[-1]), "zero leading coefficient")
        # Independent Horner recurrence, not the executable long-division kernel.
        quotient, remainder = divide_linear(coefficients, root, coefficient_field.zero)
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
    print(f"verified {len(fixtures)} exact deflation/bisection/frontier fixtures")


if __name__ == "__main__":
    main()
