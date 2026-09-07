#!/usr/bin/env python3
"""Exact Cartesian lattice oracle, independent of Gram–Schmidt enumeration.

For row basis B, L=(BBᵀ)⁻¹B satisfies z=Lv for v=Bᵀz. A ball of squared
radius r bounds |v_j| by ceil(|t_j|)+ceil(sqrt(r)). The triangle inequality
then bounds |z_i| by the corresponding weighted row sum of |L|. Enumerating
this Cartesian box and filtering exact distances proves finite exhaustion.
Only Python integers and Fraction arithmetic are used.
"""

from __future__ import annotations

import argparse
from fractions import Fraction
from itertools import product
from math import ceil, isqrt
from pathlib import Path
import json


def inverse(a: list[list[Fraction]]) -> list[list[Fraction]]:
    n = len(a)
    work = [list(row) + [Fraction(i == j) for j in range(n)] for i, row in enumerate(a)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if work[i][j]), None)
        if pivot is None:
            raise ValueError("dependent rows")
        work[j], work[pivot] = work[pivot], work[j]
        scale = work[j][j]
        work[j] = [x / scale for x in work[j]]
        for i in range(n):
            if i != j:
                scale = work[i][j]
                work[i] = [x - scale * y for x, y in zip(work[i], work[j])]
    return [row[n:] for row in work]


def left_inverse(b: list[list[int]], m: int) -> list[list[Fraction]]:
    n = len(b)
    gram = [[sum(Fraction(b[i][k] * b[j][k]) for k in range(m)) for j in range(n)]
            for i in range(n)]
    inv = inverse(gram)
    return [[sum(inv[i][k] * b[k][j] for k in range(n)) for j in range(m)] for i in range(n)]


def ball(b: list[list[int]], t: list[Fraction], r: Fraction,
         left: list[list[Fraction]]) -> list[tuple[tuple[int, ...], tuple[int, ...], Fraction]]:
    if r < 0:
        return []
    h = isqrt(r.numerator // r.denominator)
    if h * h < r:
        h += 1
    ambient_bounds = [ceil(abs(x)) + h for x in t]
    coeff_bounds = [ceil(sum(abs(x) * h for x, h in zip(row, ambient_bounds))) for row in left]
    result = []
    for z in product(*(range(-h, h + 1) for h in coeff_bounds)):
        v = tuple(sum(z[i] * b[i][j] for i in range(len(b))) for j in range(len(t)))
        d = sum((Fraction(x) - y) ** 2 for x, y in zip(v, t))
        if d <= r:
            result.append((v, z, d))
    return sorted(result)


def validate(case: dict) -> None:
    b, n, m = case["basis"], case["n"], case["m"]
    assert len(b) == n and all(len(row) == m for row in b), "basis dimensions"
    t = list(map(Fraction, case["target"]))
    assert len(t) == m, "target dimension"
    try:
        left = left_inverse(b, m)
    except ValueError:
        assert case["status"] == "rejected", "dependent input accepted"
        return
    assert case["status"] != "rejected", "independent input rejected"
    points = []
    for p in case["points"]:
        z, v, d = tuple(p["coefficients"]), tuple(p["ambient"]), Fraction(p["distanceSq"])
        assert len(z) == n and len(v) == m, "output dimensions"
        assert v == tuple(sum(z[i] * b[i][j] for i in range(n)) for j in range(m)), "reconstruction"
        assert d == sum((Fraction(x) - y) ** 2 for x, y in zip(v, t)), "distance"
        points.append((v, z, d))
    assert points == sorted(set(points)), "duplicate or unsorted output"
    op, status = case["operation"], case["status"]
    if op == "babai":
        assert len(points) == 1 and status == "candidate"
        return
    if op == "shortest" and n == 0:
        assert status == "none" and not points
        return
    radius = Fraction(case["radiusSq"])
    if status == "incomplete":
        assert all(p[2] <= radius for p in points), "partial point outside initial radius"
        return
    assert status == "complete", "unknown status"
    if op == "enumerate":
        expected = ball(b, t, radius, left)
    else:
        if op == "closest":
            initial = sum(x * x for x in t)  # zero is an independent finite bound
            expected = ball(b, t, initial, left)
        else:
            assert op == "shortest" and all(x == 0 for x in t)
            initial = min(sum(x * x for x in row) for row in b)
            expected = [p for p in ball(b, t, Fraction(initial), left) if any(p[0])]
        optimum = min(p[2] for p in expected)
        expected = [p for p in expected if p[2] == optimum]
        assert radius == optimum, "incorrect optimum distance"
    assert points == expected, f"complete output differs: expected {expected}, got {points}"


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixtures", nargs="?", type=Path,
                        default=Path("conformance-fixtures/HexLatticeEnum/latticeenum.jsonl"))
    args = parser.parse_args()
    count = 0
    for line_number, line in enumerate(args.fixtures.read_text().splitlines(), 1):
        case = json.loads(line)
        try:
            validate(case)
        except (AssertionError, ValueError) as error:
            raise AssertionError(f"{args.fixtures}:{line_number}: {case.get('id')}: {error}") from error
        count += 1
    assert count, "no fixtures"
    print(f"lattice enumeration: {count} exact Cartesian oracle cases passed")


if __name__ == "__main__":
    main()
