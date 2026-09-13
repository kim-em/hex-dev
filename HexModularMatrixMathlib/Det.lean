/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Det
public import HexModularMatrixMathlib.Bound
public import HexBareissMathlib
meta import HexModularMatrix.Det

public section

/-! Total determinant correspondence, including the Bareiss fallback. -/

namespace HexModularMatrixMathlib

/-- Every route of the modular/Bareiss dispatcher returns Mathlib's determinant. -/
theorem detWith_eq (A : Hex.Matrix Int n n) (fuel : Nat) :
    (Hex.ModularMatrix.detWith A fuel).value = Matrix.det (HexMatrixMathlib.matrixEquiv A) := by
  cases h : A.detModular? fuel with
  | none =>
    rw [Hex.ModularMatrix.detWith_bareiss h]
    exact (HexMatrixMathlib.bareiss_eq_det A).trans (HexMatrixMathlib.det_eq A)
  | some d =>
    rw [Hex.ModularMatrix.detWith_modular h]
    exact (Hex.Matrix.detModular?_eq h).trans (HexMatrixMathlib.det_eq A)

/-- The total executable determinant agrees with Mathlib's determinant. -/
theorem det_eq (A : Hex.Matrix Int n n) :
    Hex.ModularMatrix.det A = Matrix.det (HexMatrixMathlib.matrixEquiv A) :=
  detWith_eq A (Hex.ModularMatrix.defaultFuel A)

/-- Decide integer-matrix singularity through the total modular determinant.
This instance supports compiled evaluation; it does not promise kernel reduction
of the modular prime-supply and default-fuel computations for `by decide`. -/
instance (priority := 1100) detDecidable (A : Matrix (Fin n) (Fin n) Int) :
    Decidable (A.det = 0) :=
  decidable_of_iff (Hex.ModularMatrix.det (HexMatrixMathlib.matrixEquiv.symm A) = 0)
    (by rw [det_eq, Equiv.apply_symm_apply])

#guard decide ((0 : Matrix (Fin 2) (Fin 2) Int).det = 0)
#guard !(decide ((1 : Matrix (Fin 2) (Fin 2) Int).det = 0))

end HexModularMatrixMathlib
