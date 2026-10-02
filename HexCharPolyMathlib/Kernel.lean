/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly.Kernel
public import HexCharPolyMathlib.Basic
public import HexMatrixMathlib.Literal

public section

namespace HexCharPolyMathlib

open Hex.Matrix.CharPolyKernel

private theorem intRing_eq : CommRing.toGrindCommRing Int = Lean.Grind.instCommRingInt := by
  unfold CommRing.toGrindCommRing Ring.toGrindRing Semiring.toGrindSemiring
    Lean.Grind.instCommRingInt
  dsimp only
  congr
  all_goals first
    | exact proof_irrel_heq _ _
    | (funext n; match n with | 0 => rfl | 1 => rfl | n + 2 => rfl)

/-- The kernel certificate identifies Mathlib's characteristic polynomial.
The arithmetic proof consumes only the literal row list. -/
theorem charpoly_eq_of_checkList (n : Nat) (rs : List (List Int)) (w : Witness)
    (result : List Int) (h : checkCharPolyList n rs w result = true) :
    (HexMatrixMathlib.ofLists n n rs).charpoly =
      HexPolyMathlib.equiv (Hex.DensePoly.ofCoeffs result.reverse.toArray) := by
  have he : HexMatrixMathlib.matrixEquiv (ofLists n rs) =
      HexMatrixMathlib.ofLists n n rs := by
    ext i j
    simp only [HexMatrixMathlib.matrixEquiv_apply, ofLists, Hex.Matrix.getElem_ofFn,
      HexMatrixMathlib.ofLists_apply]
  rw [← he, ← equiv_charPoly]
  apply congrArg HexPolyMathlib.equiv
  have hb := congrArg (fun r : Lean.Grind.CommRing Int =>
    @Hex.Matrix.berkowitz Int r n (ofLists n rs)) intRing_eq
  unfold Hex.Matrix.charPoly
  rw [hb]
  exact charPoly_eq_of_checkList n rs w result h

end HexCharPolyMathlib
