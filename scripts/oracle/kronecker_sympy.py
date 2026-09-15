#!/usr/bin/env python3
"""Independent ZZ polynomial identities and exact structural preflight bounds.

The wire format is one self-contained `kind: kronecker` record per line.
Metadata is computed from the original syntax/support, before SymPy expands
the accepted polynomial comparison. Declines never request that expansion.
"""

import json
import sys
from dataclasses import dataclass

import sympy as sp


class ShapeError(ValueError):
    pass


@dataclass
class Bound:
    degrees: list[int]
    height: int

    def add(self, other, cap):
        return Bound(list(map(max, self.degrees, other.degrees)), min(self.height + other.height, cap))

    def mul(self, other, cap):
        return Bound([a + b for a, b in zip(self.degrees, other.degrees)], min(self.height * other.height, cap))

    def sup(self, other):
        return Bound(list(map(max, self.degrees, other.degrees)), max(self.height, other.height))


def satpow(a, n, cap):
    result = 1
    while n:
        if n & 1:
            result = min(result * a, cap)
        n //= 2
        if n:
            a = min(a * a, cap)
    return min(result, cap)


def log2(n):
    return max(0, n.bit_length() - 1)


def expr_bound(e, k, cap, observed):
    op, *args = e
    if op == "int":
        b = Bound([0] * k, min(abs(args[0]), cap))
    elif op == "atom":
        if not 0 <= args[0] < k:
            raise ShapeError("atomIndex")
        b = Bound([int(i == args[0]) for i in range(k)], min(1, cap))
    else:
        a = expr_bound(args[0], k, cap, observed)
        if op == "neg":
            b = a
        elif op == "pow":
            b = Bound([d * args[1] for d in a.degrees], satpow(a.height, args[1], cap))
        else:
            c = expr_bound(args[1], k, cap, observed)
            if op in ("add", "sub"):
                b = a.add(c, cap)
            elif op == "mul":
                b = a.mul(c, cap)
            else:
                raise ValueError(f"unknown expression constructor {op}")
    observed.append(b)
    return b


def term_shape(ts, k):
    return all(len(e) == k and all(isinstance(d, int) and d >= 0 for d in e) for e, _ in ts)


def canonical(ts, k):
    return term_shape(ts, k) and all(c != 0 for _, c in ts) and all(
        a[0] > b[0] for a, b in zip(ts, ts[1:]))


def term_bound(ts, k, cap):
    if not term_shape(ts, k):
        raise ShapeError("termShape")
    return Bound([max([0] + [e[i] for e, _ in ts]) for i in range(k)],
                 min(sum(abs(c) for _, c in ts), cap))


def residue_expr(e, p):
    if e[0] == "int":
        return 0 <= e[1] < p
    if e[0] == "atom":
        return True
    return residue_expr(e[1], p) and (e[0] in ("neg", "pow") or residue_expr(e[2], p))


def residue_terms(ts, p):
    return all(0 <= c < p for _, c in ts)


def matrix_shape(a, k, n, m):
    return len(a) == n and all(len(row) == m and all(term_shape(t, k) for t in row) for row in a)


def flatten(a):
    return [x for row in a for x in row]


def preflight(case):
    k = case["k"]
    dmax, nmax = case["budget"]
    cap = 1 << nmax
    op = case["op"]
    mod = op.endswith("Mod")
    p = case.get("p", 0)
    zero = Bound([0] * k, 0)
    observed = []
    if mod and p == 0:
        raise ShapeError("modulus")
    if op.startswith("expr") or op.startswith("terms"):
        is_expr = op.startswith("expr")
        def bound(x):
            return expr_bound(x, k, cap, observed) if is_expr else term_bound(x, k, cap)
        a, b = bound(case["lhs"]), bound(case["rhs"])
        if not is_expr:
            observed = [a, b]
        common = a.add(b, cap)
        if mod:
            residue = residue_expr if is_expr else residue_terms
            if not residue(case["lhs"], p) or not residue(case["rhs"], p):
                raise ShapeError("residue")
            if not canonical(case["q"], k):
                raise ShapeError("quotient")
            q = term_bound(case["q"], k, cap)
            scaled = Bound([0] * k, min(p, cap)).mul(q, cap)
            observed += [q, common, scaled]
            common = common.add(scaled, cap)
    else:
        n, r, m = (case[x] for x in ("n", "r", "m"))
        a, b, c = (case[x] for x in ("a", "b", "c"))
        if not (matrix_shape(a, k, n, r) and matrix_shape(b, k, r, m) and matrix_shape(c, k, n, m)
                and (not mod or matrix_shape(case["q"], k, n, m))):
            raise ShapeError("matrixShape")
        if mod:
            if not all(residue_terms(t, p) for mat in (a, b, c) for t in flatten(mat)):
                raise ShapeError("residue")
            if not all(canonical(t, k) for t in flatten(case["q"])):
                raise ShapeError("quotient")
        aa, bb, cc = [[[term_bound(t, k, cap) for t in row] for row in mat] for mat in (a, b, c)]
        products = []
        for i in range(n):
            row = []
            for j in range(m):
                dot = zero
                for t in range(r):
                    dot = dot.add(aa[i][t].mul(bb[t][j], cap), cap)
                row.append(dot)
            products.append(row)
        observed = flatten(aa) + flatten(bb) + flatten(cc) + flatten(products)
        left, right = flatten(products), flatten(cc)
        if mod:
            qq = [term_bound(t, k, cap) for t in flatten(case["q"])]
            left = [x.add(y, cap) for x, y in zip(left, right)]
            right = [Bound([0] * k, min(p, cap)).mul(q, cap) for q in qq]
            observed += qq + left + right
        common = zero
        for x, y in zip(left, right):
            common = common.sup(x.add(y, cap))
    strides = []
    dense = 1
    for d in common.degrees:
        strides.append(dense)
        dense *= d + 1
    width = log2(common.height) + 2
    inner = min(nmax + 1, max([0] + [
        sum(s * d for s, d in zip(strides, b.degrees)) * width + log2(b.height) + 2 for b in observed]))
    outer, bits, stage = None, inner, "inner"
    if op.startswith("mul") and case["mode"].endswith("signedPacked"):
        r = case["r"]
        outer = log2(r) + 2 * max(0, inner - 1) + 1 if r else 0
        product = 2 * r * outer + 2
        bits = min(nmax + 1, max(inner, product))
        stage = "result" if inner < product else "inner"
    return dict(degrees=common.degrees, strides=strides, digits=min(dense, dmax + 1),
                coefficientBound=common.height, digitBits=width, innerBits=inner,
                outerSlotBits=outer, packedBits=bits, limitingStage="Hex.Kronecker.Stage." + stage)


def expr(e, xs):
    op, *args = e
    if op == "int":
        return sp.Integer(args[0])
    if op == "atom":
        return xs[args[0]]
    a = expr(args[0], xs)
    if op == "neg":
        return -a
    if op == "pow":
        return a ** args[1]
    b = expr(args[1], xs)
    return {"add": lambda: a+b, "sub": lambda: a-b, "mul": lambda: a*b}[op]()


def terms(ts, xs):
    return sum((sp.Integer(c)*sp.prod(x**d for x, d in zip(xs, e)) for e, c in ts), sp.Integer(0))


def identity(case):
    xs = sp.symbols(f"x0:{case['k']}")
    op, p = case["op"], case.get("p", 0)
    if op.startswith("expr") or op.startswith("terms"):
        parse = expr if op.startswith("expr") else terms
        difference = parse(case["lhs"], xs) - parse(case["rhs"], xs)
        if op.endswith("Mod"):
            difference -= p*terms(case["q"], xs)
        return sp.expand(difference) == 0
    for i in range(case["n"]):
        for j in range(case["m"]):
            difference = sum(terms(case["a"][i][t], xs)*terms(case["b"][t][j], xs)
                             for t in range(case["r"])) - terms(case["c"][i][j], xs)
            if op.endswith("Mod"):
                difference -= p*terms(case["q"][i][j], xs)
            if sp.expand(difference) != 0:
                return False
    return True


def verify(case):
    assert case["kind"] == "kronecker" and case["lib"] == "HexKronecker"
    try:
        size = preflight(case)
    except ShapeError as e:
        assert case["size"] == {"error": "Hex.Kronecker.SizeError." + str(e)}, case["case"]
        assert case["result"] is False, case["case"]
        return
    assert size == case["size"], (case["case"], size, case["size"])
    dmax, nmax = case["budget"]
    accepted = size["digits"] <= dmax and size["packedBits"] <= nmax
    assert case["result"] == (accepted and identity(case)), case["case"]


def main():
    count = 0
    for line in sys.stdin:
        if line.strip():
            verify(json.loads(line))
            count += 1
    if not count:
        raise ValueError("empty Kronecker fixture stream")
    print(f"HexKronecker: {count} independent SymPy and preflight checks passed")


if __name__ == "__main__":
    main()
