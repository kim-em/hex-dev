/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRankMathlib
import Mathlib.Algebra.Field.ZMod


open Matrix

theorem result : (!![(MvPolynomial.X (0 : Fin 1))] : Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) ℤ)).rank = 1 := by
  rank

/-- info: 'result' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms result
