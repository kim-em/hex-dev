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
import all HexModularMatrix.Det

public section

/-! Total determinant correspondence, including the Bareiss fallback. -/

namespace HexModularMatrixMathlib

/-- Every route of the modular/Bareiss dispatcher returns Mathlib's determinant. -/
theorem detWith_eq (A : Hex.Matrix Int n n) (fuel : Nat)
    (seed : Nat := Hex.ModularMatrix.defaultSeed) (useDivisor : Bool := false) :
    (Hex.ModularMatrix.detWith A fuel seed useDivisor).value =
      Matrix.det (HexMatrixMathlib.matrixEquiv A) := by
  have ho : (Hex.ModularMatrix.ordinaryWith A fuel).value =
      Matrix.det (HexMatrixMathlib.matrixEquiv A) := by
    cases h : A.detModular? fuel with
    | none =>
      simp only [Hex.ModularMatrix.ordinaryWith, h]
      exact (HexMatrixMathlib.bareiss_eq_det A).trans (HexMatrixMathlib.det_eq A)
    | some d =>
      simp only [Hex.ModularMatrix.ordinaryWith, h]
      exact (Hex.Matrix.detModular?_eq h).trans (HexMatrixMathlib.det_eq A)
  cases useDivisor with
  | false => exact ho
  | true =>
    cases h : (A.detViaDivisorWith (Hex.Rand.ofSeed seed) fuel).1 with
    | none => simpa only [Hex.ModularMatrix.detWith, h, Bool.true_eq, ↓reduceIte] using ho
    | some d =>
      rw [Hex.ModularMatrix.detWith_divisor h]
      exact (Hex.Matrix.detViaDivisorWith_eq h).trans (HexMatrixMathlib.det_eq A)

/-- The seeded total divisor route has a seed-independent mathematical value. -/
theorem detViaDivisor_eq (A : Hex.Matrix Int n n) (seed : Nat) :
    Hex.ModularMatrix.detViaDivisor A seed = Matrix.det (HexMatrixMathlib.matrixEquiv A) := by
  unfold Hex.ModularMatrix.detViaDivisor
  split
  · exact (HexMatrixMathlib.bareiss_eq_det A).trans (HexMatrixMathlib.det_eq A)
  · exact detWith_eq A (Hex.ModularMatrix.defaultFuel A) seed true

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
