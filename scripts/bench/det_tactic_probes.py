#!/usr/bin/env python3
"""Write the fresh-module proof probes of the `det` tactic.

Each family is one seeded closed matrix literal written twice under
``bench/HexBareissMathlib/ProofProbe``: ``<Family>Hex.lean`` proves its
determinant by ``det`` (importing ``HexBareissMathlib``) and
``<Family>Mathlib.lean`` by ``eval_det`` (importing only
``Mathlib.Tactic.NormDet``); ``Baseline.lean`` and ``MathlibBaseline.lean``
are the import-only baselines.  The families follow the fixture ladders of
``SPEC/matrix-tactics.md``: dense square integer matrices with 8-bit
entries, structured matrices (tridiagonal, and a column-reversed
Vandermonde matrix whose leading entry is zero, so the pivot search must
swap rows), a singular product of rank ``n - 1``, large coefficients (64-
and 256-bit entries) and a rational matrix with small denominators.
``dense-32`` has no ``eval_det`` probe: Bird's algorithm does not finish it
within the sweep's budget.

The generator is deterministic; ``scripts/bench/det_tactic_sweep.py`` runs
the probes.
"""

from __future__ import annotations

import random
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
PROBES = ROOT / "bench" / "HexBareissMathlib" / "ProofProbe"

HEADER = """/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
"""

SEED = 2026


def det(m: list[list[Fraction]]) -> Fraction:
    n = len(m)
    m = [row[:] for row in m]
    d = Fraction(1)
    for c in range(n):
        p = next((r for r in range(c, n) if m[r][c] != 0), None)
        if p is None:
            return Fraction(0)
        if p != c:
            m[c], m[p] = m[p], m[c]
            d = -d
        d *= m[c][c]
        for r in range(c + 1, n):
            f = m[r][c] / m[c][c]
            m[r] = [a - f * b for a, b in zip(m[r], m[c])]
    return d


def dense(n: int, bits: int, rng: random.Random) -> list[list[Fraction]]:
    lo, hi = -(1 << (bits - 1)), (1 << (bits - 1)) - 1
    return [[Fraction(rng.randint(lo, hi)) for _ in range(n)] for _ in range(n)]


def tridiagonal(n: int, rng: random.Random) -> list[list[Fraction]]:
    m = [[Fraction(0)] * n for _ in range(n)]
    for i in range(n):
        m[i][i] = Fraction(rng.randint(2, 9))
        if i + 1 < n:
            m[i][i + 1] = Fraction(rng.randint(-9, 9))
            m[i + 1][i] = Fraction(rng.randint(-9, 9))
    return m


def vandermonde(n: int) -> list[list[Fraction]]:
    """Nodes ``0, …, n - 1`` with the columns in decreasing degree, so the
    leading entry is ``0``."""
    return [[Fraction(i) ** (n - 1 - j) for j in range(n)] for i in range(n)]


def singular(n: int, rng: random.Random) -> list[list[Fraction]]:
    left = [[rng.randint(-9, 9) for _ in range(n - 1)] for _ in range(n)]
    right = [[rng.randint(-9, 9) for _ in range(n)] for _ in range(n - 1)]
    return [[Fraction(sum(left[i][k] * right[k][j] for k in range(n - 1))) for j in range(n)]
            for i in range(n)]


def rational(n: int, rng: random.Random) -> list[list[Fraction]]:
    return [[Fraction(rng.randint(-20, 20), rng.choice([1, 2, 3, 4, 6])) for _ in range(n)]
            for i in range(n)]


def entry(q: Fraction) -> str:
    return str(q.numerator) if q.denominator == 1 else f"{q.numerator} / {q.denominator}"


def literal(m: list[list[Fraction]]) -> str:
    return "!![" + "; ".join(", ".join(entry(x) for x in row) for row in m) + "]"


# name, module stem, carrier, generator, whether `eval_det` gets a probe
FAMILIES: list[tuple[str, str, str, object, bool]] = [
    ("dense-8", "Dense8", "ℤ", lambda rng: dense(8, 8, rng), True),
    ("dense-12", "Dense12", "ℤ", lambda rng: dense(12, 8, rng), True),
    ("dense-16", "Dense16", "ℤ", lambda rng: dense(16, 8, rng), True),
    ("dense-32", "Dense32", "ℤ", lambda rng: dense(32, 8, rng), False),
    ("tridiagonal-16", "Tridiagonal16", "ℤ", lambda rng: tridiagonal(16, rng), True),
    ("vandermonde-8", "Vandermonde8", "ℤ", lambda rng: vandermonde(8), True),
    ("singular-16", "Singular16", "ℤ", lambda rng: singular(16, rng), True),
    ("large-8-64", "Large8Bits64", "ℤ", lambda rng: dense(8, 64, rng), True),
    ("large-4-256", "Large4Bits256", "ℤ", lambda rng: dense(4, 256, rng), True),
    ("rational-8", "Rational8", "ℚ", lambda rng: rational(8, rng), True),
]


def probe(stem: str, family: str, carrier: str, m: list[list[Fraction]], d: Fraction,
          imp: str, tactic: str) -> str:
    n = len(m)
    return (
        f"{HEADER}import {imp}\n\n"
        f"/-! `{stem}`: the `{family}` family, a `{n} × {n}` literal over `{carrier}`, "
        f"proved by `{tactic}`. -/\n\n"
        "set_option maxHeartbeats 0\n\n"
        f"theorem result : Matrix.det (R := {carrier}) {literal(m)} = {entry(d)} := by {tactic}\n\n"
        "#print axioms result\n"
    )


def main() -> int:
    PROBES.mkdir(parents=True, exist_ok=True)
    (PROBES / "Baseline.lean").write_text(
        f"{HEADER}import HexBareissMathlib\n\n/-! Import-only baseline for the `det` fresh-module probes. -/\n")
    (PROBES / "MathlibBaseline.lean").write_text(
        f"{HEADER}import Mathlib.Tactic.NormDet\n\n"
        "/-! Import-only baseline for the Mathlib `eval_det` fresh-module probes. -/\n")
    modules = ["Baseline", "MathlibBaseline"]
    for family, stem, carrier, gen, mathlib in FAMILIES:
        rng = random.Random(f"{SEED}:{family}")
        m = gen(rng)
        d = det(m)
        (PROBES / f"{stem}Hex.lean").write_text(
            probe(f"{stem}Hex", family, carrier, m, d, "HexBareissMathlib", "det"))
        modules.append(f"{stem}Hex")
        if mathlib:
            (PROBES / f"{stem}Mathlib.lean").write_text(
                probe(f"{stem}Mathlib", family, carrier, m, d, "Mathlib.Tactic.NormDet", "eval_det"))
            modules.append(f"{stem}Mathlib")
    print("\n".join(f"`HexBareissMathlib.ProofProbe.{m}" for m in modules))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
