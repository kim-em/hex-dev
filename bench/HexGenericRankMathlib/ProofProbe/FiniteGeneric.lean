/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRankMathlib
import Mathlib.Algebra.Field.ZMod

set_option maxHeartbeats 0

open Matrix MvPolynomial in
theorem result : (!![X (0 : Fin 1) ^ 3 - X 0] :
    Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) (ZMod 3))).rank = 1 := by rank

#print axioms result
