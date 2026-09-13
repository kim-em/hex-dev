#!/usr/bin/env python3
"""Generate the complete seeded structural-tactic proof ladders.

Only Python's standard library is needed. Minimal-polynomial targets for the
rational-dense family use exact Faddeev–LeVerrier on integer numerators. Smith
ranks and factors follow from the specified unimodular transforms; Hermite
members are row combinations and nonmembers differ by an odd coordinate from
an even lattice. The Lean certificates independently establish every target.
"""
from __future__ import annotations

from fractions import Fraction
import json
from pathlib import Path
import random

ROOT = Path(__file__).resolve().parents[2]
HEADER = """/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
"""
DIMENSIONS = (2, 4, 8, 16)
SEED = 10238


def identity(n):
    return [[int(i == j) for j in range(n)] for i in range(n)]


def product(a, b):
    return [[sum(x * y for x, y in zip(row, col)) for col in zip(*b)] for row in a]


def triangular(n, rng, lower):
    return [[int(i == j) if i == j or (i < j) == lower else rng.choice((-1, 1))
             for j in range(n)] for i in range(n)]


def transformed(n, m, rank, bits, rng, even=False):
    # Each output entry sums at most rank diagonal entries. The reserved bits
    # bound those additions; the actual maximum input height is also recorded.
    exponent = max(1, bits - max(1, rank).bit_length())
    factors = [2 ** (i * exponent // max(1, rank - 1)) for i in range(rank)]
    if even:
        factors = [2 * d for d in factors]
    d = [[factors[i] if i == j and i < rank else 0 for j in range(m)] for i in range(n)]
    a = product(product(triangular(n, rng, True), d), triangular(m, rng, False))
    return a, factors


def companion(coeffs):
    n = len(coeffs) - 1
    return [[int(i == j + 1) if j != n - 1 else -coeffs[i]
             for j in range(n)] for i in range(n)]


def characteristic(a):
    n = len(a)
    b = identity(n)
    cs = []
    for k in range(1, n + 1):
        b = product(a, b)
        trace = sum(b[i][i] for i in range(n))
        assert trace % k == 0
        c = -trace // k
        cs.append(c)
        for i in range(n):
            b[i][i] += c
    assert all(x == 0 for row in b for x in row)
    return list(reversed(cs)) + [1]


def rational(q):
    q = Fraction(q)
    return str(q.numerator) if q.denominator == 1 else f"({q.numerator} / {q.denominator})"


def matrix(a, columns=None):
    if not a:
        return "!![" + "," * (columns or 0) + "]"
    if not a[0]:
        return "!![" + ";" * len(a) + "]"
    return "!![" + "; ".join(", ".join(rational(x) for x in row) for row in a) + "]"


def vector(xs):
    return "![" + ", ".join(map(rational, xs)) + "]"


def polynomial(cs):
    terms = []
    for i, c in enumerate(cs):
        if not c:
            continue
        coefficient = f"Polynomial.C {rational(c)}"
        if Fraction(c).denominator == 1 and c < 0:
            coefficient = f"Polynomial.C ({c})"
        power = "Polynomial.X" if i == 1 else f"Polynomial.X ^ {i}"
        terms.append(coefficient if i == 0 else power if c == 1 else f"{coefficient} * {power}")
    return " + ".join(terms) or "0"


def max_bits(a):
    return max((abs(Fraction(x).numerator).bit_length() for row in a for x in row), default=0)


def fixture_cases():
    cases = []

    def add(owner, family, n, bits, a, rank=None, factors=None, coeffs=None, components=("basis",)):
        m = len(a[0]) if a else n
        stem = "".join(s.title() for s in family.split("-")) + f"N{n}M{m}Bits{bits}"
        for component in components:
            name = stem + component.title().replace("-", "")
            literal = matrix(a, m)
            if owner == "HexMinPolyMathlib":
                proposition = f"minpoly ℚ ({literal} : Matrix (Fin {len(a)}) (Fin {m}) ℚ) =\n    {polynomial(coeffs)}"
                tactic = "min_poly"
            elif owner == "HexSmithMathlib":
                proposition = f"Nonempty (HexSmithMathlib.SmithQuotient {literal} {rank} {vector(factors)})"
                tactic = "smith"
            elif component == "basis":
                proposition = f"Nonempty (HexHermiteMathlib.HermiteBasis {literal} {rank})"
                tactic = "hermite"
            else:
                v = [sum((1 if i % 2 else -1) * row[j] for i, row in enumerate(a)) for j in range(m)]
                if component == "nonmember":
                    v[-1] += 1
                membership = "∉" if component == "nonmember" else "∈"
                proposition = f"({vector(v)} : Fin {m} → ℤ) {membership}\n    Submodule.span ℤ (Set.range {literal})"
                tactic = "hermite"
            cases.append(dict(owner=owner, family=family, n=n, rows=len(a), columns=m,
                              configured_input_bits=bits, actual_input_numerator_bits=max_bits(a),
                              actual_input_denominator_bits=max((Fraction(x).denominator.bit_length()
                                  for row in a for x in row), default=0),
                              rank=rank, component=component, module=f"{owner}.ProofProbe.{name}",
                              proposition=proposition, tactic=tactic, seed=SEED,
                              comparator_status="no-comparable-surface-in-named-comparator",
                              fresh_module_budget_ms=60_000))

    for fidx, family in enumerate(("cyclic", "repeated-block", "nilpotent", "rational-dense")):
        for n in DIMENSIONS:
            for bits in (8, 32):
                rng = random.Random(SEED + 100000 * fidx + 100 * n + bits)
                bound = 2 ** (bits - 1)
                if family in ("cyclic", "repeated-block"):
                    d = n if family == "cyclic" else n // 2
                    cs = [rng.randrange(-bound, bound) for _ in range(d)] + [1]
                    c = companion(cs)
                    a = c if d == n else [[c[i % d][j % d] if i // d == j // d else 0
                                           for j in range(n)] for i in range(n)]
                elif family == "nilpotent":
                    a = [[rng.randrange(1, bound) if j == i + 1 else 0 for j in range(n)] for i in range(n)]
                    cs = [0] * n + [1]
                else:
                    z = [[rng.randrange(-bound, bound) for _ in range(n)] for _ in range(n)]
                    denominator = bound + 1
                    a = [[Fraction(x, denominator) for x in row] for row in z]
                    cs = [Fraction(c, denominator ** (n - i)) for i, c in enumerate(characteristic(z))]
                add("HexMinPolyMathlib", family, n, bits, a, coeffs=cs, components=("equality",))

    for fidx, family in enumerate(("chain-conjugate", "rectangular-presentation", "rank-deficient", "large-coefficients")):
        for n in DIMENSIONS:
            for bits in ((8, 32, 64, 256) if family == "large-coefficients" else (8, 32)):
                shapes = ((n, 2 * n), (2 * n, n)) if family == "rectangular-presentation" else ((n, n),)
                for nr, nc in shapes:
                    rng = random.Random(SEED + 1000000 + 100000 * fidx + 1000 * nr + 100 * nc + bits)
                    rank = n // 2 if family == "rank-deficient" else n
                    a, factors = transformed(nr, nc, rank, bits, rng)
                    add("HexSmithMathlib", family, n, bits, a, rank, factors, components=("quotient",))

    for fidx, family in enumerate(("unimodular-conjugate", "tall-hermite", "rank-deficient-hermite", "membership-residual")):
        for n in DIMENSIONS:
            for bits in (8, 32, 128):
                rng = random.Random(SEED + 2000000 + 100000 * fidx + 100 * n + bits)
                nr = 2 * n if family == "tall-hermite" else n
                rank = n // 2 if family in ("rank-deficient-hermite", "membership-residual") else n
                a, _ = transformed(nr, n, rank, bits - 1, rng, even=True)
                components = ("basis", "member", "nonmember") if family == "membership-residual" else ("basis", "member")
                add("HexHermiteMathlib", family, n, bits, a, rank, components=components)
    add("HexMinPolyMathlib", "empty", 0, 0, [], coeffs=[1], components=("equality",))
    for owner in ("HexSmithMathlib", "HexHermiteMathlib"):
        component = "quotient" if owner == "HexSmithMathlib" else "basis"
        add(owner, "empty-rows", 3, 0, [], 0, [], components=(component,))
        add(owner, "empty-columns", 3, 0, [[], [], []], 0, [], components=(component,))
    return cases


def main():
    cases = fixture_cases()
    for owner in ("HexMinPolyMathlib", "HexSmithMathlib", "HexHermiteMathlib"):
        directory = ROOT / "bench" / owner / "ProofProbe"
        directory.mkdir(parents=True, exist_ok=True)
        (directory / "Baseline.lean").write_text(HEADER + f"import {owner}.Tactic\n")
    for case in cases:
        source = HEADER + f"import {case['owner']}.Tactic\n\n"
        source += "set_option maxHeartbeats 0\nset_option maxRecDepth 100000\n"
        source += "set_option profiler true\nset_option profiler.threshold 1000000\n"
        source += "set_option trace.HexMatrix.certificate true\n\n"
        source += f"theorem result : {case['proposition']} := by {case['tactic']}\n\n#print axioms result\n"
        path = ROOT / "bench" / Path(*case['module'].split(".")).with_suffix(".lean")
        path.write_text(source)
    manifest = [{k: v for k, v in case.items() if k != "proposition"} for case in cases]
    (ROOT / "scripts/bench/structural_tactic_probes.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print(f"Generated {len(cases)} candidates and three import-only baselines")


if __name__ == "__main__":
    main()
