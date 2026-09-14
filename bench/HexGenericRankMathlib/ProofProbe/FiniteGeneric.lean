/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRankMathlib
import Mathlib.Algebra.Field.ZMod

/-
Non-test pending the shared residue-list encoding, #10257 (the domain
coefficient provider, #10255, has merged). Enable this declaration unchanged
when that kernel representation is available and add it to the sweep manifest.

open Matrix MvPolynomial in
 theorem result : (!![X (0 : Fin 1) ^ 3 - X 0] :
    Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) (ZMod 3))).rank = 1 := by rank

#print axioms result
-/
