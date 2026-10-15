/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmith
public import HexPolyTheory
public import HexMatrixTheory
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Roots

public section

/-! Transport of executable polynomial matrices to Mathlib. -/

namespace HexPolySmithTheory

universe u

open Hex

noncomputable section

private theorem toPolynomial_fold_products {F : Type u} [Field F]
    [DecidableEq F] {k : Nat} (xs : List (Fin k))
    (p q : Fin k → DensePoly F) (acc : DensePoly F) :
    HexPolyTheory.toPolynomial
        (xs.foldl (fun z i => z + p i * q i) acc) =
      xs.foldl
        (fun z i => z + HexPolyTheory.toPolynomial (p i) *
          HexPolyTheory.toPolynomial (q i))
        (HexPolyTheory.toPolynomial acc) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      simp only [List.foldl_cons]
      rw [ih, HexPolyTheory.toPolynomial_add, HexPolyTheory.toPolynomial_mul]

/-- The executable polynomial matrix as a Mathlib matrix over `Polynomial F`. -/
def polyMatrixEquiv {F : Type u} [Field F] [DecidableEq F] {n m : Nat}
    (A : Hex.Matrix (DensePoly F) n m) :
    Matrix (Fin n) (Fin m) (Polynomial F) :=
  (HexMatrixTheory.matrixEquiv A).map HexPolyTheory.toPolynomial

@[simp]
theorem polyMatrixEquiv_apply {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) (i : Fin n) (j : Fin m) :
    polyMatrixEquiv A i j = HexPolyTheory.toPolynomial A[i][j] := by
  simp [polyMatrixEquiv, HexMatrixTheory.matrixEquiv_apply]

@[simp]
theorem polyMatrixEquiv_add {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A B : Hex.Matrix (DensePoly F) n m) :
    polyMatrixEquiv (A + B) = polyMatrixEquiv A + polyMatrixEquiv B := by
  ext i j
  simp [polyMatrixEquiv, HexPolyTheory.toPolynomial_add]

/-- Entrywise polynomial transport preserves matrix multiplication. -/
@[simp]
theorem polyMatrixEquiv_mul {F : Type u} [Field F] [DecidableEq F]
    {n m k : Nat} (A : Hex.Matrix (DensePoly F) n m)
    (B : Hex.Matrix (DensePoly F) m k) :
    polyMatrixEquiv (A * B) = polyMatrixEquiv A * polyMatrixEquiv B := by
  funext i j
  rw [polyMatrixEquiv_apply, Matrix.mul_apply, Hex.Matrix.getElem_mul]
  unfold Vector.dotProduct
  rw [toPolynomial_fold_products, HexPolyTheory.toPolynomial_zero,
    HexMatrixTheory.foldl_finRange_eq_sum]
  apply Finset.sum_congr rfl
  intro l _
  rw [Hex.Matrix.getElem_col]
  rw [polyMatrixEquiv_apply, polyMatrixEquiv_apply]
  rfl

/-- Monic normalization in the executable representation agrees with
Mathlib's canonical associate for polynomials over a field. -/
theorem monicize_eq_normalize {F : Type u} [Field F] [DecidableEq F]
    (p : DensePoly F) :
    HexPolyTheory.toPolynomial (DensePoly.monicize p) =
      normalize (HexPolyTheory.toPolynomial p) := by
  by_cases hp : p = 0
  · subst p
    simp [HexPolyTheory.toPolynomial_zero]
  · have hmonic := DensePoly.monic_monicize hp
    have hpolyMonic :
        (HexPolyTheory.toPolynomial (DensePoly.monicize p)).Monic := by
      rw [Polynomial.Monic, HexPolyTheory.leadingCoeff_toPolynomial]
      exact hmonic
    apply Polynomial.eq_of_monic_of_associated hpolyMonic
      (Polynomial.monic_normalize (by
        intro hzero
        apply hp
        apply HexPolyTheory.equiv.injective
        simpa using hzero))
    have hleft : HexPolyTheory.toPolynomial (DensePoly.monicize p) ∣
        HexPolyTheory.toPolynomial p :=
      HexPolyTheory.toPolynomial_dvd
        (DensePoly.monicize_dvd_of_dvd hp (DensePoly.dvd_refl_poly p))
    have hright : HexPolyTheory.toPolynomial p ∣
        HexPolyTheory.toPolynomial (DensePoly.monicize p) :=
      HexPolyTheory.toPolynomial_dvd (DensePoly.dvd_monicize p)
    exact (associated_of_dvd_dvd hleft hright).trans (associated_normalize _)

/-- Pairwise-distinct evaluation points separate all dense polynomials whose
degrees are strictly smaller than the number of points. -/
theorem evaluationSeparatesUpTo_of_nodup {F : Type u} [Field F]
    [DecidableEq F] {k D : Nat} (pts : Vector F k) (hnodup : pts.toList.Nodup)
    (hD : D < k) : Hex.PolyMatrix.EvaluationSeparatesUpTo pts D := by
  unfold Hex.PolyMatrix.EvaluationSeparatesUpTo
  intro p q hp hq heval
  apply HexPolyTheory.equiv.injective
  apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq
      (f := fun i : Fin k => pts[i])
  · intro i j hij
    let ii : Fin pts.toList.length := ⟨i.val, by simp⟩
    let jj : Fin pts.toList.length := ⟨j.val, by simp⟩
    have hget : pts.toList.get ii = pts.toList.get jj := by
      simpa [ii, jj] using hij
    have hij' := hnodup.injective_get hget
    apply Fin.ext
    exact congrArg (fun z : Fin pts.toList.length => z.val) hij'
  · intro i
    rw [HexPolyTheory.equiv_apply, HexPolyTheory.equiv_apply,
      HexPolyTheory.eval_toPolynomial, HexPolyTheory.eval_toPolynomial,
      DensePoly.eval_eq_evalImpl, DensePoly.eval_eq_evalImpl]
    apply heval
    simp
  · rw [HexPolyTheory.equiv_apply, HexPolyTheory.equiv_apply,
      HexPolyTheory.natDegree_toPolynomial,
      HexPolyTheory.natDegree_toPolynomial, Fintype.card_fin]
    omega

end

end HexPolySmithTheory
