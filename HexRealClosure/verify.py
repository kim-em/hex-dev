#!/usr/bin/env python3
"""Exact independent oracle for the rational selected-root smoke tests."""

from fractions import Fraction as Q
import re
import subprocess
import time


def add(x, y):
    return (x[0] + y[0], x[1] + y[1])


def mul(x, y):
    return (x[0] * y[0] + 2 * x[1] * y[1], x[0] * y[1] + x[1] * y[0])


def neg(x):
    return (-x[0], -x[1])


def inv(x):
    denominator = x[0] * x[0] - 2 * x[1] * x[1]
    assert denominator
    return (x[0] / denominator, -x[1] / denominator)


def sign(x):
    a, b = x
    if not b:
        return (a > 0) - (a < 0)
    if not a:
        return (b > 0) - (b < 0)
    if (a > 0) == (b > 0):
        return (a > 0) - (a < 0)
    return ((a > 0) - (a < 0)) if a * a > 2 * b * b else ((b > 0) - (b < 0))


def eval_poly(coeffs, x):
    result = (Q(0), Q(0))
    for coeff in reversed(coeffs):
        result = add(mul(result, x), (Q(coeff), Q(0)))
    return result


def poly_mul(p, q):
    result = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            result[i + j] += a * b
    return result


def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def rem(p, q):
    p, q = trim(p[:]), trim(q[:])
    while len(p) >= len(q):
        c = p[-1] / q[-1]
        k = len(p) - len(q)
        for i, x in enumerate(q):
            p[i + k] -= c * x
        trim(p)
    return p


def gcd(p, q):
    while q:
        p, q = q, rem(p, q)
    return [c / p[-1] for c in p]


alpha = (Q(0), Q(1))
below = add(alpha, (Q(-3), Q(0)))
head = poly_mul([Q(-2), Q(0), Q(1)], [Q(-3), Q(1)])
assert eval_poly(head, alpha) == (0, 0)
assert mul(below, inv(below)) == (1, 0)
expected = [
    f"some ({sign(alpha)}, {sign(below)}, {sign(eval_poly(head, alpha))}, "
    f"{sign(inv(below))}, {sign(add(mul(alpha, alpha), (Q(-2), Q(0))))})",
    "true",  # an old descriptor is rejected by the changed context binding
    f"some ({sign(alpha)}, {sign(add(alpha, neg(alpha)))})",
    str((0, 0) == (Q(0), Q(0))).lower(),
    str(len(gcd(head, [Q(-3), Q(1)])) - 1),
    f"some ({sign(alpha)}, {sign(alpha)}, {len([Q(-2), Q(0), Q(1)]) - 1})",
]
expected[3] = f"some {expected[3]}"

start = time.perf_counter()
run = subprocess.run(
    ["lake", "build", "HexRealClosure.Tests"],
    capture_output=True, text=True, check=True,
)
elapsed = time.perf_counter() - start
actual = re.findall(r"info: HexRealClosure/Tests\.lean:\d+:0: (.+)", run.stdout + run.stderr)
assert actual == expected, f"Lean outputs {actual!r}; exact oracle expects {expected!r}"
print(f"exact oracle passed; warm Lake build and six evaluations: {elapsed:.3f}s")
