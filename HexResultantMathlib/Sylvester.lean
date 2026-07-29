/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexResultantMathlib.Basic
public import Mathlib.Data.Fin.Rev

public section

/-!
Full-value correspondence between Brown's executable recurrence and Mathlib's
Sylvester-determinant resultant.
-/
namespace Hex

universe u

variable {R : Type u}

namespace SubresultantMinor

/-- The parity sign used by the proof-only Laplace recursion is the usual
power of `-1`. -/
theorem sign_eq_pow [CommRing R] (j : Nat) :
    Hex.SubresultantMinor.sign (R := R) j = (-1 : R) ^ j := by
  induction j with
  | zero => simp [Hex.SubresultantMinor.sign]
  | succ j ih =>
      rw [Hex.SubresultantMinor.sign_succ, ih, pow_succ]
      ring

/-- The dependency-free Laplace determinant used by `hex-resultant` agrees
with Mathlib's determinant on the same finite square matrix. -/
theorem det_eq_matrixDet [CommRing R] {n : Nat}
    (M : Hex.SubresultantMinor.Square R n) :
    Hex.SubresultantMinor.det M = Matrix.det (Matrix.of M) := by
  induction n with
  | zero => simp [Hex.SubresultantMinor.det]
  | succ n ih =>
      let term := fun j : Fin (n + 1) =>
        Hex.SubresultantMinor.sign (R := R) j.val * M 0 j *
          Hex.SubresultantMinor.det (Hex.SubresultantMinor.deleteFirst M j)
      have hfold (xs : List (Fin (n + 1))) (acc : R) :
          xs.foldl (fun a j => a + term j) acc = acc + (xs.map term).sum := by
        induction xs generalizing acc with
        | nil => simp
        | cons j js hjs =>
            simp only [List.foldl_cons, List.map_cons, List.sum_cons, hjs]
            ring
      have hfold0 :
          (List.finRange (n + 1)).foldl (fun a j => a + term j) 0 =
            ∑ j, term j := by
        rw [hfold]
        calc
          0 + (List.map term (List.finRange (n + 1))).sum =
              (List.map term (List.finRange (n + 1))).sum := by ring
          _ = ∑ j, term j := by
            rw [← List.sum_toFinset term (List.nodup_finRange _),
              List.toFinset_finRange]
      rw [Hex.SubresultantMinor.det]
      change (List.finRange (n + 1)).foldl (fun a j => a + term j) 0 = _
      rw [hfold0]
      rw [Matrix.det_succ_row_zero]
      apply Finset.sum_congr rfl
      intro j _
      simp only [term, Matrix.of_apply]
      rw [sign_eq_pow, ih]
      congr 3

end SubresultantMinor

namespace DensePoly
namespace Subresultant

/-- A value-indexed presentation of Mathlib's Sylvester matrix. -/
private def sylvesterByVal [CommRing R] (f g : Polynomial R) (df dg : Nat) :
    Matrix (Fin (df + dg)) (Fin (df + dg)) R :=
  Matrix.of fun i j =>
    if _ : j.val < df then
      if j.val ≤ i.val ∧ i.val ≤ j.val + dg then
        g.coeff (i.val - j.val)
      else 0
    else
      let jj := j.val - df
      if jj ≤ i.val ∧ i.val ≤ jj + df then
        f.coeff (i.val - jj)
      else 0

private theorem sylvester_eq_byVal [CommRing R] (f g : Polynomial R)
    (df dg : Nat) :
    Polynomial.sylvester f g df dg = sylvesterByVal f g df dg := by
  ext i j
  induction j using Fin.addCases with
  | left j =>
      have hle : Fin.castAdd dg j ≤ i ↔ j.val ≤ i.val := by
        change (Fin.castAdd dg j).val ≤ i.val ↔ j.val ≤ i.val
        rw [Fin.val_castAdd]
      simp [Polynomial.sylvester, sylvesterByVal, Set.mem_Icc]
      simp only [hle]
  | right j =>
      simp [Polynomial.sylvester, sylvesterByVal, Set.mem_Icc]
      split <;> simp_all <;> omega

/-- Integer coefficient lookup is the bounded coefficient selected by one
reversed Sylvester block. -/
private theorem coeffInt_eq_ite [CommRing R] [DecidableEq R]
    (p : DensePoly R) (d i j : Nat) (hp : p.size ≤ d + 1) :
    coeffInt p ((d : Int) - (i : Int) + (j : Int)) =
      if j ≤ i ∧ i ≤ d + j then p.coeff (d + j - i) else 0 := by
  unfold coeffInt
  by_cases hnonneg : 0 ≤ (d : Int) - (i : Int) + (j : Int)
  · rw [if_neg (by omega)]
    have hnat : ((d : Int) - (i : Int) + (j : Int)).toNat = d + j - i := by
      omega
    rw [hnat]
    by_cases hji : j ≤ i
    · have hidj : i ≤ d + j := by omega
      rw [if_pos ⟨hji, hidj⟩]
    · rw [if_neg (by omega)]
      exact coeff_eq_zero_of_size_le p (by omega)
  · rw [if_pos (by omega), if_neg (by omega)]

/-- At index zero, the generalized coefficient matrix is Mathlib's
Sylvester matrix with both axes reversed. -/
private theorem coeffMatrixAt_zero_eq_sylvester [CommRing R] [DecidableEq R]
    (df dg : Nat) (f g : DensePoly R) (hf : f.size ≤ df + 1)
    (hg : g.size ≤ dg + 1) :
    Matrix.of (coeffMatrixAt df dg 0 0 f g) =
      (Polynomial.sylvester (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g) df dg).submatrix
          Fin.revPerm Fin.revPerm := by
  rw [sylvester_eq_byVal]
  ext i j
  simp only [Matrix.of_apply, Matrix.submatrix_apply, Fin.revPerm_apply]
  unfold coeffMatrixAt sylvesterByVal
  simp only [Nat.sub_zero, Matrix.of_apply, HexPolyMathlib.coeff_toPolynomial,
    Int.ofNat_eq_natCast, Int.natCast_zero]
  by_cases hj : j.val < dg
  · rw [if_pos hj]
    have hiBound : i.val < df + dg := by simp
    have hrow :
        (if i.val = df + dg - 1 then
            coeffInt f ((0 : Int) - (dg - 1 : Nat) + j.val)
          else coeffInt f ((df : Int) - i.val + j.val)) =
          coeffInt f ((df : Int) - i.val + j.val) := by
      by_cases hi : i.val = df + dg - 1
      · rw [if_pos hi]
        congr 1
        omega
      · rw [if_neg hi]
    rw [hrow, coeffInt_eq_ite f df i.val j.val hf]
    have hjrev : ¬(Fin.rev j).val < df := by
      simp [Fin.rev]
      omega
    rw [dif_neg hjrev]
    by_cases hji : j.val ≤ i.val ∧ i.val ≤ df + j.val
    · rw [if_pos hji]
      have hraw :
          (Fin.rev j).val - df ≤ (Fin.rev i).val ∧
            (Fin.rev i).val ≤ (Fin.rev j).val - df + df := by
        simp [Fin.rev]
        omega
      rw [if_pos hraw]
      congr 1
      simp [Fin.rev]
      omega
    · rw [if_neg hji]
      rw [if_neg]
      simp [Fin.rev] at hji ⊢
      omega
  · rw [if_neg hj]
    have hiBound : i.val < df + dg := by simp
    have hrow :
        (if i.val = df + dg - 1 then
            coeffInt g
              ((0 : Int) - (df - 1 : Nat) + ((j.val - dg : Nat) : Int))
          else coeffInt g
            ((dg : Int) - i.val + ((j.val - dg : Nat) : Int))) =
          coeffInt g
            ((dg : Int) - i.val + ((j.val - dg : Nat) : Int)) := by
      by_cases hi : i.val = df + dg - 1
      · rw [if_pos hi]
        congr 1
        omega
      · rw [if_neg hi]
    rw [hrow, coeffInt_eq_ite g dg i.val (j.val - dg) hg]
    have hjrev : (Fin.rev j).val < df := by
      simp [Fin.rev]
      omega
    rw [dif_pos hjrev]
    by_cases hji : j.val - dg ≤ i.val ∧ i.val ≤ dg + (j.val - dg)
    · rw [if_pos hji]
      have hraw :
          (Fin.rev j).val ≤ (Fin.rev i).val ∧
            (Fin.rev i).val ≤ (Fin.rev j).val + dg := by
        simp [Fin.rev]
        omega
      rw [if_pos hraw]
      congr 1
      simp [Fin.rev]
      omega
    · rw [if_neg hji]
      rw [if_neg]
      simp [Fin.rev] at hji ⊢
      omega

/-- The zeroth generalized coefficient minor at explicit degree bounds is
Mathlib's Sylvester determinant at those same bounds. -/
theorem coeffMinorAt_zero_eq_resultant [CommRing R] [DecidableEq R]
    (df dg : Nat) (f g : DensePoly R)
    (hf : f.size ≤ df + 1) (hg : g.size ≤ dg + 1) :
    coeffMinorAt df dg 0 0 f g =
      Polynomial.resultant (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g)
        (m := df) (n := dg) := by
  unfold coeffMinorAt Polynomial.resultant
  rw [Hex.SubresultantMinor.det_eq_matrixDet]
  rw [coeffMatrixAt_zero_eq_sylvester _ _ f g hf hg]
  exact Matrix.det_submatrix_equiv_self Fin.revPerm _

/-- The zeroth generalized coefficient minor is Mathlib's Sylvester
determinant at the same formal degrees. -/
theorem coeffMinor_zero_eq_resultant [CommRing R] [DecidableEq R]
    (f g : DensePoly R) :
    coeffMinor 0 0 f g =
      Polynomial.resultant (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g)
        (m := formalDegree f) (n := formalDegree g) := by
  have hf : f.size ≤ formalDegree f + 1 := by
    unfold formalDegree
    omega
  have hg : g.size ≤ formalDegree g + 1 := by
    unfold formalDegree
    omega
  unfold coeffMinor
  exact coeffMinorAt_zero_eq_resultant _ _ f g hf hg

end Subresultant

/-- The executable and Mathlib resultants agree under dense-polynomial
correspondence, with the executable default formal degrees made explicit. -/
theorem toPolynomial_resultant [CommRing R] [IsDomain R] [DecidableEq R]
    [Div R] [Hex.ExactDivLaws R] (f g : DensePoly R) :
    resultant f g =
      Polynomial.resultant (HexPolyMathlib.toPolynomial f)
        (HexPolyMathlib.toPolynomial g)
        (m := f.degree?.getD 0) (n := g.degree?.getD 0) := by
  by_cases hf : f = 0
  · subst f
    have hz : (0 : DensePoly R).isZero = true :=
      (isZero_eq_true_iff (0 : DensePoly R)).2 rfl
    have hzdeg : (0 : DensePoly R).degree?.getD 0 = 0 := by simp
    by_cases hgsmall : g.size ≤ 1
    · have hgdeg : g.degree?.getD 0 = 0 := by
        by_cases hg : g = 0
        · subst g
          simp
        · have hgpos : 0 < g.size := by
            by_contra h
            apply hg
            exact (size_eq_zero_iff g).mp (by omega)
          rw [degree?_eq_some_of_pos_size g hgpos, Option.getD_some]
          omega
      unfold resultant
      rw [hz]
      simp only [↓reduceIte]
      rw [if_pos hgsmall, HexPolyMathlib.toPolynomial_zero, hzdeg, hgdeg]
      simp [Polynomial.resultant]
    · have hgdeg : 0 < g.degree?.getD 0 := by
        have hgpos : 0 < g.size := by omega
        rw [degree?_eq_some_of_pos_size g hgpos, Option.getD_some]
        omega
      unfold resultant
      rw [hz]
      simp only [↓reduceIte]
      rw [if_neg hgsmall, HexPolyMathlib.toPolynomial_zero, hzdeg,
        Polynomial.resultant_zero_left]
      simp [hgdeg.ne']
  · by_cases hg : g = 0
    · subst g
      have hz : (0 : DensePoly R).isZero = true :=
        (isZero_eq_true_iff (0 : DensePoly R)).2 rfl
      have hzdeg : (0 : DensePoly R).degree?.getD 0 = 0 := by simp
      have hfpos : 0 < f.size := by
        by_contra h
        apply hf
        exact (size_eq_zero_iff f).mp (by omega)
      have hfz : f.isZero = false := (isZero_eq_false_iff f).2 hfpos
      by_cases hfsmall : f.size ≤ 1
      · have hfdeg : f.degree?.getD 0 = 0 := by
          rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
          omega
        unfold resultant
        rw [hfz, hz]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_pos hfsmall, HexPolyMathlib.toPolynomial_zero, hzdeg, hfdeg]
        simp [Polynomial.resultant]
      · have hfdeg : 0 < f.degree?.getD 0 := by
          rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
          omega
        unfold resultant
        rw [hfz, hz]
        simp only [Bool.false_eq_true, ↓reduceIte]
        rw [if_neg hfsmall, HexPolyMathlib.toPolynomial_zero, hzdeg,
          Polynomial.resultant_zero_right]
        simp [hfdeg.ne']
    · have hfpos : 0 < f.size := by
        by_contra h
        apply hf
        exact (size_eq_zero_iff f).mp (by omega)
      have hgpos : 0 < g.size := by
        by_contra h
        apply hg
        exact (size_eq_zero_iff g).mp (by omega)
      have hfz : f.isZero = false := (isZero_eq_false_iff f).2 hfpos
      have hgz : g.isZero = false := (isZero_eq_false_iff g).2 hgpos
      have hdf : f.degree?.getD 0 = Subresultant.formalDegree f := by
        rw [degree?_eq_some_of_pos_size f hfpos, Option.getD_some]
        rfl
      have hdg : g.degree?.getD 0 = Subresultant.formalDegree g := by
        rw [degree?_eq_some_of_pos_size g hgpos, Option.getD_some]
        rfl
      unfold resultant
      simp only [hfz, hgz, Bool.false_eq_true, ↓reduceIte]
      by_cases hfg : f.size < g.size
      · rw [if_pos hfg]
        rw [resultantOrdered_eq_coeffMinor g f hg hf (by omega)]
        rw [Subresultant.coeffMinor_zero_eq_resultant]
        rw [hdf, hdg]
        rw [negOnePow_eq_sign,
          Hex.SubresultantMinor.sign_eq_pow]
        exact (Polynomial.resultant_comm
          (HexPolyMathlib.toPolynomial f) (HexPolyMathlib.toPolynomial g)
          (Subresultant.formalDegree f) (Subresultant.formalDegree g)).symm
      · rw [if_neg hfg]
        rw [resultantOrdered_eq_coeffMinor f g hf hg (by omega)]
        rw [Subresultant.coeffMinor_zero_eq_resultant, hdf, hdg]

end DensePoly
end Hex
