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
RING_AXIOMS = {
    "RingSolverInteger1": ("propext",),
    "RingSolverInteger2": ("propext", "Quot.sound"),
    "RingSolverInteger3": ("propext",),
    "RingSolverRational1": ("propext", "Classical.choice", "Quot.sound"),
    "RingSolverRational2": ("propext", "Classical.choice", "Quot.sound"),
    "RingSolverRational3": ("propext", "Classical.choice", "Quot.sound"),
    "RingSolverPower1": ("propext",),
    "RingSolverPower2": ("propext",),
    "RingSolverPower3": ("propext",),
}


def probe_sources() -> dict[str, str]:
    sources = {}
    for stem, binders, target in CASES:
        for arm, tactic in (("Ring", "ring"), ("Grobner", "grobner")):
            source = HEADER + f"""import Mathlib.Tactic

set_option maxHeartbeats 0
set_option profiler true

theorem result {binders} : {target} := by
  {tactic}

#print axioms result
"""
            sources[f"{stem}{arm}.lean"] = source

    sources["RingSolverVariableExponent.lean"] = HEADER + """import Mathlib.Tactic

set_option maxHeartbeats 0

theorem result (x : Int) (k : Nat) : (x ^ k) * (x ^ k) = x ^ (2 * k) := by
  fail_if_success grobner
  ring

#print axioms result
"""
    sources["RingSolverAlgebraic.lean"] = HEADER + f"""import Mathlib.Tactic
import {PREFIX}.AlgebraicSupport

set_option maxHeartbeats 0

theorem result (h : ClosedAlgebraic.α ^ 2 = 2) :
    ClosedAlgebraic.α * ClosedAlgebraic.α - 1 * 2 = 0 := by
  fail_if_success (solve | ring)
  grobner

#print axioms result
"""
    return sources


def main() -> None:
    DEST.mkdir(parents=True, exist_ok=True)
    for name, source in probe_sources().items():
        (DEST / name).write_text(source, encoding="utf-8")


if __name__ == "__main__":
    main()
