/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic

namespace HexPolyDetMathlib.ProofProbe

/-- Shared tridiagonal symbolic fixture; both measured arms elaborate this same input. -/
def tridiagonal (x : Int) : Matrix (Fin 4) (Fin 4) Int :=
  !![x, 1, 0, 0; 1, x, 1, 0; 0, 1, x, 1; 0, 0, 1, x]

/-- Rank-one update of the identity with symbolic entries. -/
def rankOne (x : Int) : Matrix (Fin 4) (Fin 4) Int :=
  fun i j => (if i = j then 1 else 0) + x * (i.val + 1) * (j.val + 1)

end HexPolyDetMathlib.ProofProbe
