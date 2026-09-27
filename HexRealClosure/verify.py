#!/usr/bin/env python3
"""Exact independent oracle for the rational selected-root smoke tests."""

from fractions import Fraction as Q
import re
import subprocess


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
    return divmod_poly(p, q)[1]


def divmod_poly(p, q):
    p, q = trim(p[:]), trim(q[:])
    quotient = [Q(0)] * max(0, len(p) - len(q) + 1)
    while len(p) >= len(q):
        c = p[-1] / q[-1]
        k = len(p) - len(q)
        quotient[k] = c
        for i, x in enumerate(q):
            p[i + k] -= c * x
        trim(p)
    return trim(quotient), p


def gcd(p, q):
    while q:
        p, q = q, rem(p, q)
    return [c / p[-1] for c in p]


def inverse_or_none(x):
    return None if x == (Q(0), Q(0)) else inv(x)


alpha = (Q(0), Q(1))
below = add(alpha, (Q(-3), Q(0)))
head = poly_mul([Q(-2), Q(0), Q(1)], [Q(-3), Q(1)])
assert eval_poly(head, alpha) == (0, 0)
assert mul(below, inv(below)) == (1, 0)
expected_inverse = (Q(-3, 7), Q(-1, 7))
constant_inverse = inv(alpha)
linear_gcd = gcd(head, [Q(-3), Q(1)])
split, remainder = divmod_poly(head, linear_gcd)
assert not remainder
alpha_cubed = mul(mul(alpha, alpha), alpha)
assert alpha_cubed == (Q(0), Q(2))
candidate_roots = [neg(alpha), alpha, (Q(3), Q(0))]
derivative = [i * c for i, c in enumerate(head)][1:]


def between(x, lower, upper):
    return sign(add(x, neg(lower))) > 0 and sign(add(upper, neg(x))) > 0


wide_selection = [r for r in candidate_roots
                  if between(r, (Q(0), Q(0)), (Q(4), Q(0)))
                  and sign(eval_poly(derivative, r)) == -1]
scaled_head = [2 * c for c in head]
scaled_selection = [r for r in candidate_roots
                    if between(r, (Q(1), Q(0)), (Q(2), Q(0)))
                    and eval_poly(scaled_head, r) == (0, 0)]
negative_selection = [r for r in candidate_roots if sign(r) < 0]
assert len(wide_selection) == len(scaled_selection) == len(negative_selection) == 1
wide_root, scaled_root, negative_root = (
    wide_selection[0], scaled_selection[0], negative_selection[0]
)
old_version, new_version = 7, 8
expected = [
    f"some ({sign(alpha)}, {sign(below)}, {sign(eval_poly(head, alpha))}, "
    f"{sign(inv(below))}, {sign(add(mul(alpha, alpha), (Q(-2), Q(0))))}, "
    f"{sign(add(inv(below), neg(expected_inverse)))})",
    str(old_version != new_version).lower(),
    f"some ({sign(alpha)}, {sign(add(alpha, neg(alpha)))}, {sign((Q(6), Q(0)))}, "
    f"{sign(inv(below))})",
    f"some ({str(inverse_or_none((Q(0), Q(0))) is None).lower()}, "
    f"{str(inverse_or_none(add(mul(alpha, alpha), (Q(-2), Q(0)))) is None).lower()})",
    str(len(linear_gcd) - 1),
    f"some ({len(gcd(head, [Q(0), Q(1)])) - 1}, {sign(constant_inverse)}, "
    f"{sign(add(constant_inverse, neg((Q(0), Q(1, 2)))))})",
    f"some ({sign(alpha)}, {sign(alpha)}, {sign(alpha)}, {sign(inv(below))}, "
    f"{len(split) - 1}, {new_version})",
    f"some {str(eval_poly([Q(-2), Q(0), Q(1)], alpha) == (0, 0)).lower()}",
    f"some ({2 * head[-1] / linear_gcd[-1]}, {len(split) - 1}, {sign(alpha)})",
    # The unnormalized Euclidean sequence ends with split mod (x - 3),
    # whose constant remainder is split(3).
    f"some ({len(gcd([Q(-3), Q(1)], split)) - 1}, "
    f"{eval_poly(split, (Q(3), Q(0)))[0]})",
    f"some (3, {sign(inv(alpha_cubed))}, "
    f"{sign(add(inv(alpha_cubed), neg(mul((Q(1, 4), Q(0)), alpha))))})",
    f"some ({sign(alpha)}, {str(mul(alpha, alpha) == (Q(2), Q(0))).lower()}, "
    f"{str(mul(below, inv(below)) == (Q(1), Q(0))).lower()})",
    f"some ({str(wide_root == alpha).lower()}, {sign(wide_root)}, "
    f"{str(mul(wide_root, wide_root) == (Q(2), Q(0))).lower()}, "
    f"{sign(add(wide_root, (Q(-3), Q(0))))})",
    f"some ({str(scaled_root == alpha).lower()}, {sign(scaled_root)}, "
    f"{str(mul(scaled_root, scaled_root) == (Q(2), Q(0))).lower()})",
    f"some ({sign(negative_root)}, "
    f"{str(mul(negative_root, negative_root) == (Q(2), Q(0))).lower()}, "
    f"{sign(add(negative_root, (Q(1), Q(0))))})",
]

run = subprocess.run(
    ["lake", "build", "HexRealClosure.Tests"],
    capture_output=True, text=True, check=True,
)
actual = re.findall(r"info: HexRealClosure/Tests\.lean:\d+:0: (.+)", run.stdout + run.stderr)
assert actual == expected, f"Lean outputs {actual!r}; exact oracle expects {expected!r}"
print("exact oracle passed for fifteen runnable cases")
