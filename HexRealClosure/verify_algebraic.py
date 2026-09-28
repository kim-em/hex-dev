#!/usr/bin/env python3
"""Independent exact arithmetic for selected-root and infinitesimal examples."""

import argparse
from fractions import Fraction as Q
from pathlib import Path
import re
import subprocess


def trim(p):
    p = list(p)
    while p and not p[-1]:
        p.pop()
    return p


def add(p, q):
    return trim([(p[i] if i < len(p) else 0) + (q[i] if i < len(q) else 0)
                 for i in range(max(len(p), len(q)))])


def neg(p):
    return [-c for c in p]


def sub(p, q):
    return add(p, neg(q))


def mul(p, q):
    if not p or not q:
        return []
    r = [Q(0)] * (len(p) + len(q) - 1)
    for i, a in enumerate(p):
        for j, b in enumerate(q):
            r[i + j] += a * b
    return trim(r)


def divmod_poly(p, q):
    p, q = trim(p), trim(q)
    assert q
    quotient = [Q(0)] * max(0, len(p) - len(q) + 1)
    while p and len(p) >= len(q):
        k, c = len(p) - len(q), p[-1] / q[-1]
        quotient[k] = c
        p = sub(p, [Q(0)] * k + [c * a for a in q])
    return trim(quotient), p


# Work in Q[b]/(b^4-2); the positive b in (1,2) is 2^(1/4).
MODULUS = [Q(-2), Q(0), Q(0), Q(0), Q(1)]
ONE = [Q(1)]
B = [Q(0), Q(1)]
A = [Q(0), Q(0), Q(1)]


def reduce(p):
    return divmod_poly(p, MODULUS)[1]


def product(p, q):
    return reduce(mul(p, q))


def inverse(p):
    p = reduce(p)
    assert p
    r0, r1, t0, t1 = MODULUS, p, [], ONE
    while r1:
        quotient, remainder = divmod_poly(r0, r1)
        r0, r1 = r1, remainder
        t0, t1 = t1, sub(t0, mul(quotient, t1))
    assert len(r0) == 1 and r0[0]
    return reduce([c / r0[0] for c in t0])


def interval_mul(p, q):
    endpoints = [a * b for a in p for b in q]
    return min(endpoints), max(endpoints)


def sign(p):
    p = reduce(p)
    if not p:
        return 0
    lower, upper = Q(1), Q(2)
    for _ in range(128):
        bounds = (Q(0), Q(0))
        for c in reversed(p):
            lo, hi = interval_mul(bounds, (lower, upper))
            bounds = lo + c, hi + c
        if bounds[0] > 0:
            return 1
        if bounds[1] < 0:
            return -1
        midpoint = (lower + upper) / 2
        if midpoint**4 < 2:
            lower = midpoint
        else:
            upper = midpoint
    raise AssertionError("exact root interval did not determine a sign")


RATIONAL_HEAD = mul([Q(-2), Q(0), Q(1)], [Q(-3), Q(1)])


def retained(p, head, clean):
    return divmod_poly(p, head)[1] if head[-1] == 1 and all(clean(c) for c in head) else p


def rational_expected(scale):
    head = [scale * c for c in RATIONAL_HEAD]
    raw_square = retained([Q(0), Q(0), Q(1)], head, lambda c: c.denominator == 1)
    below = sub(A, [Q(3)])
    inv_below = inverse(below)
    expected_inv = [c * Q(-1, 7) for c in add(A, [Q(3)])]
    square = product(A, A)
    equation = sub(square, [Q(2)])
    raw_fourth = retained([Q(0)] * 4 + [Q(1)], head, lambda c: c.denominator == 1)
    return [sign(A), sign(below), sign(equation), sign(inv_below),
            sign(sub(product(below, inv_below), ONE)), sign(sub(inv_below, expected_inv)),
            int(not equation), int(raw_square == [Q(2)]), int(not equation),
            int(sign(sub(A, [Q(2)])) < 0), len(raw_fourth) - 1]


def field_remainder(p, q):
    """Univariate division with coefficients in the independently constructed quartic field."""
    p, q = trim(p), trim(q)
    while p and len(p) >= len(q):
        k, c = len(p) - len(q), product(p[-1], inverse(q[-1]))
        for i, a in enumerate(q):
            p[k + i] = sub(p[k + i], product(c, a))
        p = trim(p)
    return p


def nested_expected(scale):
    # The stored parent representative of (a-3)/(a-3) is (9-X²)/7,
    # computed in the full reducible cubic before selected-root evaluation.
    raw_inverse = [Q(-3, 7), Q(-1, 7)]
    raw_one = retained(mul([Q(-3), Q(1)], raw_inverse), RATIONAL_HEAD,
                       lambda c: c.denominator == 1)
    semantic_one = product(sub(A, [Q(3)]), inverse(sub(A, [Q(3)])))
    assert semantic_one == ONE and raw_one != [Q(1)]
    head = [product([Q(3)], A), neg(A), [Q(-3)], ONE]
    scaled_head = [[Q(scale) * c for c in coefficient] for coefficient in head]
    # scale=0 means the semantic-one representative, whose leading coefficient
    # differs structurally from literal one and whose coefficients are unclean.
    literal_monic = scale != 0 and scaled_head[-1] == ONE
    raw_fourth = [[], [], [], [], ONE]
    kept = field_remainder(raw_fourth, scaled_head) if literal_monic else raw_fourth
    remainder = field_remainder([neg(A), [], ONE], [neg(B), ONE])
    below = sub(B, [Q(3)])
    return [sign(B), sign(sub(B, A)), sign(sub(product(B, B), A)),
            sign(sub(product(B, inverse(B)), ONE)), int(not remainder),
            sign(inverse(below)), sign(sub(product(below, inverse(below)), ONE)),
            len(kept) - 1, int(semantic_one == ONE), int(raw_one == [Q(1)])]


def germ_add(p, q):
    return {n: p.get(n, Q(0)) + q.get(n, Q(0)) for n in p.keys() | q.keys()
            if p.get(n, Q(0)) + q.get(n, Q(0))}


def germ_neg(p):
    return {n: -c for n, c in p.items()}


def germ_mul(p, q):
    r = {}
    for i, a in p.items():
        for j, b in q.items():
            r[i + j] = r.get(i + j, Q(0)) + a * b
    return {n: c for n, c in r.items() if c}


def germ_sign(p):
    if not p:
        return 0
    c = p[min(p)]
    return (c > 0) - (c < 0)


def expected():
    # Embed epsilon=t² and its selected positive square root=t in positive Laurent germs.
    t, epsilon, inv_t, one = {1: Q(1)}, {2: Q(1)}, {-1: Q(1)}, {0: Q(1)}
    assert germ_sign(t) > 0 and germ_sign(germ_add(one, germ_neg(t))) > 0
    assert not germ_add(germ_mul(t, t), germ_neg(epsilon))
    # Monic division of Y³ by Y²-epsilon leaves epsilon*Y.
    remainder = [germ_mul(epsilon, {}), epsilon]
    clean = lambda g: all(n >= 0 and c.denominator == 1 for n, c in g.items())
    infinitesimal = [germ_sign(t), germ_sign(germ_add(t, germ_neg(epsilon))),
                    germ_sign(germ_add(germ_mul(t, t), germ_neg(epsilon))),
                    germ_sign(germ_add(germ_mul(t, inv_t), germ_neg(one))),
                    germ_sign(inv_t), int(clean(one)), len(trim(remainder)) - 1]
    return [rational_expected(Q(1)), rational_expected(Q(2)), infinitesimal,
            nested_expected(1), nested_expected(2), nested_expected(0)]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lean-log", type=Path, help="reuse a successful focused build log")
    args = parser.parse_args()
    if args.lean_log:
        output = args.lean_log.read_text()
        assert "Build completed successfully" in output
    else:
        run = subprocess.run(["lake", "build", "HexRealClosure.AlgebraicTests"],
                             capture_output=True, text=True, check=True)
        output = run.stdout + run.stderr
    rows = re.findall(r"info: HexRealClosure/AlgebraicTests\.lean:\d+:0: some #\[([^\]]*)\]", output)
    actual = [[int(x.strip()) for x in row.split(",")] for row in rows]
    assert actual == expected(), f"Lean: {actual!r}; independent exact arithmetic: {expected()!r}"
    print(f"exact selected-root oracle passed ({sum(map(len, actual))} observations)")


if __name__ == "__main__":
    main()
