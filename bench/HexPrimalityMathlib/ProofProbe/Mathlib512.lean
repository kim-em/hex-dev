/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPrimalityMathlib

namespace HexPrimalityMathlib.ProofProbe

/-! End-to-end Mathlib elaboration at the exact 512-bit policy ceiling. -/

theorem mathlib512 : Nat.Prime 7859410849558636629901668462083065564472157552549398559549382574798817245167623606274731491674495881319278928590271730493130632966670828721041794742091777 := by
  primality

#print axioms mathlib512

end HexPrimalityMathlib.ProofProbe
