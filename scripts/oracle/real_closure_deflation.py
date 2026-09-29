#!/usr/bin/env python3
"""Exact deflation, zero extraction, bisection, frontier and dispatch checks."""

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
                lo = None if a is None else q.number(str(a))
                hi = None if b is None else q.number(str(b))
                roots = q.roots([q.number(str(c)) for c in poly])
                require(all(m == 1 for _, m in roots), f"{name}: repeated active root")
                return sum((lo is None or q.compare(lo, root) < 0) and
                           (hi is None or q.compare(root, hi) < 0) for root, _ in roots)
        _, factors = formal_polynomial(poly).factor_list()
        roots = []
        for factor, multiplicity in factors:
            require(multiplicity == 1, f"{name}: repeated active root")
            require(factor.degree() == 1, f"{name}: unsupported infinitesimal factor")
            roots.append(coefficient_field.from_expr(-factor.nth(0) / factor.nth(1)))
        return sum((a is None or sign(root - a) > 0) and
                   (b is None or sign(b - root) > 0) for root in roots)

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
    # Independently evaluate the deterministic policy with exact root counts.
    # This also distinguishes a cap-spending split of a root-free cell from
    # the prescribed first cell whose count exceeds one.
    policy_head, policy_removed, policy_cells = coefficients, [], [(lower, upper)]
    policy_nodes = 0
    for _ in range(cap):
        selected = next((i for i, (a, b) in enumerate(policy_cells) if count(policy_head, a, b) > 1), None)
        if selected is None:
            break
        a, b = policy_cells[selected]
        point = (a + b) / 2
        if not evaluate(policy_head, point):
            policy_head = divide_linear(policy_head, point, coefficient_field.zero)[0]
            policy_removed.append(point)
        remaining = policy_cells[:selected] + policy_cells[selected + 1:]
        policy_cells = [(a, point), (point, b)] + remaining
        policy_nodes += 1
    actual_cells = [(decode(cell["lower"]["finite"], depth), decode(cell["upper"]["finite"], depth))
                    for cell in cells]
    require(nodes == policy_nodes and removed == policy_removed and active == policy_head and
            actual_cells == policy_cells, f"{name}: wrong selection policy")
    require(sum(cell["count"] for cell in cells) + len(removed) == row["original_count"],
            f"{name}: inconsistent root coverage")


def verify_dispatch(row, decode, coefficient_field):
    name, depth = row["name"], row["depth"]
    coefficients = [decode(a, depth) for a in row["coefficients"]]
    require(not coefficients or bool(coefficients[-1]), f"{name}: zero leading coefficient")
    sign, _, squarefree, count = root_checks(name, depth, coefficient_field)
    valid = bool(coefficients) and squarefree(coefficients)
    payload = row["result"]
    require((payload is not None) == valid, f"{name}: wrong dispatch success")
    if not valid:
        return

    def absolute(value):
        return -value if sign(value) < 0 else value

    bound = None
    for exponent in range(1, 2 * len(coefficients) + 1):
        candidate = coefficient_field(2**exponent)
        limit = (candidate - 1) * absolute(coefficients[-1])
        if all(sign(limit - absolute(a)) > 0 for a in coefficients[:-1]):
            bound = candidate
            break
    require(payload.get("route") == ("whole" if bound is None else "bounded"),
            f"{name}: wrong dispatch route")
    if bound is None:
        require(set(payload) == {"route", "head", "lower", "upper", "count"},
                f"{name}: invalid whole-line fields")
        require([decode(a, depth) for a in payload["head"]] == coefficients,
                f"{name}: wrong whole-line head")
        require(payload["lower"] == "-infinity" and payload["upper"] == "+infinity",
                f"{name}: wrong whole-line endpoints")
        require(type(payload["count"]) is int and payload["count"] == count(coefficients, None, None),
                f"{name}: wrong whole-line count")
    else:
        require(set(payload) == {"route", "bound", "frontier"}, f"{name}: invalid bounded fields")
        require(decode(payload["bound"], depth) == bound, f"{name}: wrong first accepted bound")
        # Native casts at depth d are represented by constant rational functions.
        def encode_constant(value, level):
            if level == 0:
                return str(value)
            return {"num": [encode_constant(value, level - 1)],
                    "den": [encode_constant(1, level - 1)]}
        bounded_count = count(coefficients, -bound, bound)
        require(bounded_count == count(coefficients, None, None), f"{name}: bound misses a real root")
        frontier_row = dict(row, kind="frontier", lower=encode_constant(-bound, depth),
                            upper=encode_constant(bound, depth),
                            original_count=bounded_count, result=payload["frontier"])
        verify_frontier(frontier_row, decode, coefficient_field)


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
        require(row.get("kind", "deflation") in ("deflation", "zero-factor", "bisection", "frontier", "dispatch"), "unknown fixture kind")
        if row.get("kind") == "dispatch":
            verify_dispatch(row, decode, coefficient_field)
            continue
        if row.get("kind") == "frontier":
            verify_frontier(row, decode, coefficient_field)
            continue
        if row.get("kind") == "bisection":
            verify_bisection(row, decode, coefficient_field)
            continue
        coefficients = [decode(a, depth) for a in row["coefficients"]]
        require(not coefficients or bool(coefficients[-1]), "zero leading coefficient")
        if row.get("kind") == "zero-factor":
            require(set(row) == {"kind", "name", "depth", "coefficients", "cofactor", "multiplicity"},
                    "invalid zero-factor fields")
            # The order of the first nonzero coefficient determines the exact
            # power of X, independently of the executable division recurrence.
            multiplicity = next((i for i, a in enumerate(coefficients) if a), 0)
            require(type(row["multiplicity"]) is int and row["multiplicity"] == multiplicity,
                    f"{row['name']}: wrong zero multiplicity")
            actual = [decode(a, depth) for a in row["cofactor"]]
            require(actual == coefficients[multiplicity:],
                    f"{row['name']}: wrong zero quotient or scalar")
            continue
        require(row.get("kind") is None, "unsupported fixture kind")
        root = decode(row["root"], depth)
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
    print(f"verified {len(fixtures)} exact deflation/zero-factor/bisection/frontier/dispatch fixtures")


if __name__ == "__main__":
    main()
