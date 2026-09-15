#!/usr/bin/env python3
"""Generate matched ``ring``/``grobner`` closed-form determinant probes."""

from __future__ import annotations

from pathlib import Path


ROOT = Path(__file__).resolve().parents[2]
DEST = ROOT / "bench/HexPolyDetMathlib/ProofProbe"
PREFIX = "HexPolyDetMathlib.ProofProbe"
HEADER = """/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
"""

CASES = (
    ("RingSolverInteger1", "(x : Int)",
     "x + x = 2 * x"),
    ("RingSolverInteger2", "(x y : Int)",
     "(x + 1) * (x - 1) - y * y = x ^ 2 - y ^ 2 - 1"),
    ("RingSolverInteger3", "(x : Int)",
     "x * x * x - x * 1 * 1 - 1 * 1 * x + 1 * 1 * 0 + 0 * 1 * 1 - 0 * x * 0 = "
     "x ^ 3 - 2 * x"),
    ("RingSolverRational1", "(x : Rat)",
     "x / 2 + x / 3 = 5 * x / 6"),
    ("RingSolverRational2", "(x : Rat)",
     "(x / 2) * (x / 3) - 1 * 1 = x ^ 2 / 6 - 1"),
    ("RingSolverRational3", "(x : Rat)",
     "(x / 2) * (x / 3) * (x / 5) - (x / 2) * 0 * 0 - 0 * 0 * (x / 5) + "
     "0 * 0 * 0 + 0 * 0 * 0 - 0 * (x / 3) * 0 = x ^ 3 / 30"),
    ("RingSolverPower1", "(x : Int)",
     "(x + 1) ^ 4 = x ^ 4 + 4 * x ^ 3 + 6 * x ^ 2 + 4 * x + 1"),
    ("RingSolverPower2", "(x : Int)",
     "x ^ 4 * x ^ 2 - 1 * 1 = x ^ 6 - 1"),
    ("RingSolverPower3", "(x : Int)",
     "x ^ 4 * x ^ 3 * x ^ 2 - x ^ 4 * 1 * 1 - 1 * 1 * x ^ 2 + "
     "1 * 1 * 0 + 0 * 1 * 1 - 0 * x ^ 3 * 0 = x ^ 9 - x ^ 4 - x ^ 2"),
)


def main() -> None:
    DEST.mkdir(parents=True, exist_ok=True)
    for stem, binders, target in CASES:
        for arm, tactic in (("Ring", "ring"), ("Grobner", "grobner")):
            source = HEADER + f"""import Mathlib.Tactic

set_option maxHeartbeats 0
set_option profiler true

theorem result {binders} : {target} := by
  {tactic}

#print axioms result
"""
            (DEST / f"{stem}{arm}.lean").write_text(source, encoding="utf-8")

    (DEST / "RingSolverVariableExponent.lean").write_text(
        HEADER + """import Mathlib.Tactic

theorem result (x : Int) (k : Nat) : (x ^ k) * (x ^ k) = x ^ (2 * k) := by
  fail_if_success grobner
  rw [two_mul, pow_add]

#print axioms result
""",
        encoding="utf-8",
    )
    (DEST / "RingSolverAlgebraic.lean").write_text(
        HEADER + f"""import Mathlib.Tactic
import {PREFIX}.AlgebraicSupport

theorem result (h : ClosedAlgebraic.α ^ 2 = 2) :
    ClosedAlgebraic.α * ClosedAlgebraic.α - 1 * 2 = 0 := by
  grobner

#print axioms result
""",
        encoding="utf-8",
    )


if __name__ == "__main__":
    main()
