/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolySmithMathlib.Equiv
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

public section

/-! A Mathlib Smith basis built from the executable transformations. -/

namespace HexPolySmithMathlib

universe u

open Hex
open Hex.PolyMatrix

noncomputable section

private def mappedRight {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Matrix (Fin m) (Fin m) (Polynomial F) :=
  polyMatrixEquiv (snfData A).right

private def mappedRightInv {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Matrix (Fin m) (Fin m) (Polynomial F) :=
  polyMatrixEquiv (snfData A).rightInv

private theorem mappedRight_mul_inv {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    mappedRight A * mappedRightInv A = 1 := by
  have h := congrArg polyMatrixEquiv (snfData_isSNF A).right_inv
  rw [polyMatrixEquiv_mul] at h
  have hid : polyMatrixEquiv (Hex.Matrix.identity m :
      Hex.Matrix (DensePoly F) m m) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [polyMatrixEquiv_apply, Hex.Matrix.getElem_identity]
      simp [HexPolyMathlib.toPolynomial_one]
    · rw [polyMatrixEquiv_apply, Hex.Matrix.getElem_identity]
      simp [hij, HexPolyMathlib.toPolynomial_zero]
  exact (show mappedRight A * mappedRightInv A =
      polyMatrixEquiv (Hex.Matrix.identity m) from h).trans hid

private theorem mappedRightInv_mul {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    mappedRightInv A * mappedRight A = 1 := by
  rw [mul_eq_one_comm]
  exact mappedRight_mul_inv A

/-- The ambient basis whose vectors are the rows of the executable right
inverse. -/
private def ambientBasis {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Module.Basis (Fin m) (Polynomial F) (Fin m → Polynomial F) :=
  (Pi.basisFun (Polynomial F) (Fin m)).map
    (Matrix.toLinearEquivRight'OfInv (mappedRight_mul_inv A) (mappedRightInv_mul A))

@[simp]
private theorem ambientBasis_apply {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) (i : Fin m) :
    ambientBasis A i = (mappedRightInv A).row i := by
  rw [ambientBasis, Module.Basis.map_apply, Pi.basisFun_apply]
  change Matrix.vecMul (Pi.single i 1) (mappedRightInv A) = _
  simp

private def smithFamily {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Fin (snfData A).rank → (Fin m → Polynomial F) := fun i =>
  HexPolyMathlib.toPolynomial (snfData A).diag[i] •
    ambientBasis A (Fin.castLE (snfData_isSNF A).rank_le_m i)

private theorem smithFamily_linearIndependent {F : Type u} [Field F]
    [DecidableEq F] {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    LinearIndependent (Polynomial F) (smithFamily A) := by
  let f : Fin (snfData A).rank ↪ Fin m :=
    Fin.castLEEmb (snfData_isSNF A).rank_le_m
  have hbase : LinearIndependent (Polynomial F)
      (fun i => ambientBasis A (f i)) :=
    (ambientBasis A).linearIndependent.comp f f.injective
  rw [linearIndependent_iff'] at hbase ⊢
  intro s g hsum i hi
  have hsum' : ∑ j ∈ s,
      (g j * HexPolyMathlib.toPolynomial (snfData A).diag[j]) •
        ambientBasis A (f j) = 0 := by
    simpa [smithFamily, f, mul_smul] using hsum
  have hprod := hbase s
    (fun j => g j * HexPolyMathlib.toPolynomial (snfData A).diag[j])
    hsum' i hi
  rcases mul_eq_zero.mp hprod with hg | hd
  · exact hg
  · exfalso
    apply (show (HexPolyMathlib.toPolynomial (snfData A).diag[i]).Monic from ?_).ne_zero hd
    rw [Polynomial.Monic, HexPolyMathlib.leadingCoeff_toPolynomial]
    exact (snfData_isSNF A).diag_monic i

private theorem span_rows_mul_left_le {R : Type u} [CommRing R]
    {n m : Nat} (L : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R) :
    Submodule.span R (Set.range (L * A)) ≤
      Submodule.span R (Set.range A) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  rw [Matrix.mul_apply_eq_vecMul, Matrix.vecMul_eq_sum]
  apply Submodule.sum_mem
  intro j _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

private theorem span_rows_mul_left_eq {R : Type u} [CommRing R]
    {n m : Nat} (L Li : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R) (h : Li * L = 1) :
    Submodule.span R (Set.range (L * A)) =
      Submodule.span R (Set.range A) := by
  apply le_antisymm (span_rows_mul_left_le L A)
  have hback : Li * (L * A) = A := by
    calc
      Li * (L * A) = (Li * L) * A := (Matrix.mul_assoc Li L A).symm
      _ = 1 * A := congrArg (fun Q => Q * A) h
      _ = A := by
        ext i j
        classical
        simp [Matrix.mul_apply, Matrix.one_apply]
  have hle := span_rows_mul_left_le Li (L * A)
  simpa only [hback] using hle

private theorem mappedLeftInv_mul {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    polyMatrixEquiv (snfData A).leftInv *
        polyMatrixEquiv (snfData A).left = 1 := by
  have h := congrArg polyMatrixEquiv (snfData_isSNF A).left_inv
  rw [polyMatrixEquiv_mul] at h
  have hid : polyMatrixEquiv (Hex.Matrix.identity n :
      Hex.Matrix (DensePoly F) n n) = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      rw [polyMatrixEquiv_apply, Hex.Matrix.getElem_identity]
      simp [HexPolyMathlib.toPolynomial_one]
    · rw [polyMatrixEquiv_apply, Hex.Matrix.getElem_identity]
      simp [hij, HexPolyMathlib.toPolynomial_zero]
  have hleft : polyMatrixEquiv (snfData A).left *
      polyMatrixEquiv (snfData A).leftInv = 1 := h.trans hid
  rw [mul_eq_one_comm]
  exact hleft

private theorem mappedDiag_apply {F : Type u} [Field F] [DecidableEq F]
    {r n m : Nat} (d : Vector (DensePoly F) r) (i : Fin n) (j : Fin m) :
    polyMatrixEquiv (Hex.Matrix.diagMatrix d n m) i j =
      if h : i.val = j.val ∧ i.val < r then
        HexPolyMathlib.toPolynomial (d[i.val]'(h.2)) else 0 := by
  rw [polyMatrixEquiv_apply]
  unfold Hex.Matrix.diagMatrix
  rw [Hex.Matrix.getElem_ofFn]
  split <;> simp [HexPolyMathlib.toPolynomial_zero]

private theorem mapped_snf_mul_rightInv {F : Type u} [Field F]
    [DecidableEq F] {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    polyMatrixEquiv (snfData A).left * polyMatrixEquiv A =
      polyMatrixEquiv (Hex.Matrix.diagMatrix (snfData A).diag n m) *
        mappedRightInv A := by
  have h := congrArg polyMatrixEquiv (snfData_isSNF A).mul_eq
  rw [polyMatrixEquiv_mul, polyMatrixEquiv_mul] at h
  let X := polyMatrixEquiv (snfData A).left * polyMatrixEquiv A
  calc
    polyMatrixEquiv (snfData A).left * polyMatrixEquiv A = X * 1 := by
      simp [X]
    _ = X * (mappedRight A * mappedRightInv A) :=
      congrArg (fun Q => X * Q) (mappedRight_mul_inv A).symm
    _ = (X * mappedRight A) * mappedRightInv A :=
      (Matrix.mul_assoc X (mappedRight A) (mappedRightInv A)).symm
    _ = polyMatrixEquiv (Hex.Matrix.diagMatrix (snfData A).diag n m) *
        mappedRightInv A := by
      apply congrArg (fun Q => Q * mappedRightInv A)
      simpa [X, mappedRight] using h

private theorem mapped_snf_row {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m)
    (i : Fin (snfData A).rank) :
    (polyMatrixEquiv (snfData A).left * polyMatrixEquiv A).row
        (Fin.castLE (snfData_isSNF A).rank_le_n i) = smithFamily A i := by
  rw [mapped_snf_mul_rightInv A]
  funext j
  change (polyMatrixEquiv (Hex.Matrix.diagMatrix (snfData A).diag n m) *
    mappedRightInv A) (Fin.castLE (snfData_isSNF A).rank_le_n i) j =
      smithFamily A i j
  rw [Matrix.mul_apply]
  let ii : Fin n := Fin.castLE (snfData_isSNF A).rank_le_n i
  let kk : Fin m := Fin.castLE (snfData_isSNF A).rank_le_m i
  rw [Finset.sum_eq_single kk]
  · rw [mappedDiag_apply]
    rw [dite_eq_left (by exact ⟨rfl, i.isLt⟩)]
    simp [kk, smithFamily, ambientBasis_apply,
      Pi.smul_apply]
  · intro b _ hb
    have hne : ii.val ≠ b.val := by
      intro heq
      apply hb
      apply Fin.ext
      simpa [ii, kk] using heq.symm
    rw [mappedDiag_apply]
    rw [dite_eq_right (by
      intro h
      exact hne h.1)]
    simp
  · intro hnot
    exact (hnot (Finset.mem_univ kk)).elim

private theorem mapped_snf_row_eq_zero {F : Type u} [Field F]
    [DecidableEq F] {n m : Nat} (A : Hex.Matrix (DensePoly F) n m)
    (i : Fin n) (hi : (snfData A).rank ≤ i.val) :
    (polyMatrixEquiv (snfData A).left * polyMatrixEquiv A).row i = 0 := by
  rw [mapped_snf_mul_rightInv A]
  funext j
  change (polyMatrixEquiv (Hex.Matrix.diagMatrix (snfData A).diag n m) *
    mappedRightInv A) i j = 0
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [mappedDiag_apply]
  simp [hi]

private theorem span_smithFamily {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Submodule.span (Polynomial F) (Set.range (smithFamily A)) =
      Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A)) := by
  let B := polyMatrixEquiv (snfData A).left * polyMatrixEquiv A
  have hfamilies : Submodule.span (Polynomial F) (Set.range (smithFamily A)) =
      Submodule.span (Polynomial F) (Set.range B) := by
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      apply Submodule.subset_span
      refine ⟨Fin.castLE (snfData_isSNF A).rank_le_n i, ?_⟩
      exact mapped_snf_row A i
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i.val < (snfData A).rank
      · apply Submodule.subset_span
        refine ⟨(⟨i.val, hi⟩ : Fin (snfData A).rank), ?_⟩
        exact (mapped_snf_row A (⟨i.val, hi⟩ : Fin (snfData A).rank)).symm
      · rw [show B i = 0 from mapped_snf_row_eq_zero A i (Nat.not_lt.mp hi)]
        exact Submodule.zero_mem _
  rw [hfamilies]
  exact span_rows_mul_left_eq _ _ _ (mappedLeftInv_mul A)

private def smithNormalFormData {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Module.Basis.SmithNormalForm
      (Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A))) (Fin m)
      (snfData A).rank := by
  let hspan := span_smithFamily A
  let bN0 := Module.Basis.span (smithFamily_linearIndependent A)
  let bN := bN0.map (LinearEquiv.ofEq _ _ hspan)
  exact
    { bM := ambientBasis A
      bN := bN
      f := Fin.castLEEmb (snfData_isSNF A).rank_le_m
      a := fun i => HexPolyMathlib.toPolynomial (snfData A).diag[i]
      snf := by
        intro i
        simp [bN, bN0, smithFamily] }

/-- The executable polynomial Smith form as Mathlib's simultaneous-basis
structure for the submodule spanned by the rows of the input matrix. -/
noncomputable def smithNormalForm {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) :
    Module.Basis.SmithNormalForm
      (Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A))) (Fin m)
      (snfRank A) :=
  Eq.mp (congrArg
    (fun r => Module.Basis.SmithNormalForm
      (Submodule.span (Polynomial F) (Set.range (polyMatrixEquiv A))) (Fin m) r)
    (snfRank_eq A).symm) (smithNormalFormData A)

private theorem castSmith_a {R M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {N : Submodule R M} {r s : Nat}
    (e : r = s) (D : Module.Basis.SmithNormalForm N ι s) (i : Fin r) :
    (Eq.mp (congrArg (fun k => Module.Basis.SmithNormalForm N ι k) e.symm) D).a i =
      D.a (Fin.cast e i) := by
  cases e
  rfl

private theorem castSmith_f {R M ι : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] {N : Submodule R M} {r s : Nat}
    (e : r = s) (D : Module.Basis.SmithNormalForm N ι s) (i : Fin r) :
    (Eq.mp (congrArg (fun k => Module.Basis.SmithNormalForm N ι k) e.symm) D).f i =
      D.f (Fin.cast e i) := by
  cases e
  rfl

/-- The coefficients of the transported basis are the executable diagonal
entries, with only the rank index transported. -/
theorem smithNormalForm_a_snfData {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) (i : Fin (snfRank A)) :
    (smithNormalForm A).a i = HexPolyMathlib.toPolynomial
      (snfData A).diag[Fin.cast (snfRank_eq A) i] := by
  rw [smithNormalForm, castSmith_a]
  rfl

/-- The Smith-basis embedding uses the initial `snfRank A` ambient
coordinates. -/
@[simp]
theorem smithNormalForm_f_val {F : Type u} [Field F] [DecidableEq F]
    {n m : Nat} (A : Hex.Matrix (DensePoly F) n m) (i : Fin (snfRank A)) :
    ((smithNormalForm A).f i).val = i.val := by
  rw [smithNormalForm, castSmith_f]
  change (Fin.castLE (snfData_isSNF A).rank_le_m
    (Fin.cast (snfRank_eq A) i)).val = i.val
  rfl

end

end HexPolySmithMathlib
