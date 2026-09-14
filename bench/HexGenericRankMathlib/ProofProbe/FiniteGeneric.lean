/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexGenericRankMathlib
import Mathlib.Algebra.Field.ZMod

/-
Reserved non-test for the shared Nat residue-list encoding, #10257, as required
by issue #10223. The integer-representative fallback can already prove this
declaration with the domain provider from #10255; it is not a logical blocker.
Enable the declaration unchanged against the shared Nat kernel representation
when available and add it to the sweep manifest.

open Matrix MvPolynomial in
 theorem result : (!![X (0 : Fin 1) ^ 3 - X 0] :
    Matrix (Fin 1) (Fin 1) (MvPolynomial (Fin 1) (ZMod 3))).rank = 1 := by rank

#print axioms result
-/
