/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexCharPoly
public import HexDeterminantMathlib
public import HexMatrixMathlib
public import HexPolyMathlib
public import Mathlib.Data.List.GetD
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.Polynomial

public section

/-!
Correctness of the executable Samuelson--Berkowitz characteristic polynomial.
-/

open Matrix Polynomial
open scoped BigOperators

namespace HexCharPolyMathlib

open HexMatrixMathlib HexPolyMathlib

universe u

variable {R : Type u} [CommRing R] [DecidableEq R]

omit [DecidableEq R] in
private theorem adjugateCharmatrix_coeff_card {k : Nat}
    (B : Matrix (Fin k) (Fin k) R) :
    (matPolyEquiv (Matrix.adjugate (Matrix.charmatrix B))).coeff k = 0 := by
  ext i j
  change _ = (0 : R)
  rw [matPolyEquiv_coeff_apply, Matrix.adjugate_apply]
  let L : Matrix (Fin k) (Fin k) R := (1 : Matrix (Fin k) (Fin k) R).updateRow j 0
  let D : Matrix (Fin k) (Fin k) R := (-B).updateRow j (Pi.single i 1)
  have hmatrix :
      (Matrix.charmatrix B).updateRow j (Pi.single i 1 : Fin k -> R[X]) =
        (X : R[X]) • L.map C + D.map C := by
    apply Matrix.ext
    intro r c
    by_cases hr : r = j
    · subst r
      by_cases hc : c = i
      · subst c
        simp [L, D, Matrix.updateRow_apply]
      · simp [L, D, Matrix.updateRow_apply, hc]
    · by_cases hrc : r = c
      · subst c
        simp [L, D, Matrix.updateRow_apply, hr, Matrix.charmatrix, Matrix.scalar_apply,
          sub_eq_add_neg]
      · simp [L, D, Matrix.updateRow_apply, hr, hrc, Matrix.charmatrix,
          Matrix.scalar_apply, sub_eq_add_neg]
  rw [hmatrix]
  calc
    (det ((X : R[X]) • L.map C + D.map C)).coeff k = det L := by
      simpa using Polynomial.coeff_det_X_add_C_card L D
    _ = 0 := by
      apply Matrix.det_eq_zero_of_row_eq_zero j
      intro c
      simp [L]

omit [DecidableEq R] in
private theorem adjugateCharmatrix_coeff_rec {k d : Nat}
    (B : Matrix (Fin k) (Fin k) R) :
    (matPolyEquiv (Matrix.adjugate (Matrix.charmatrix B))).coeff d =
      (B.charpoly.coeff (d + 1)) • (1 : Matrix (Fin k) (Fin k) R) +
        (matPolyEquiv (Matrix.adjugate (Matrix.charmatrix B))).coeff (d + 1) * B := by
  let Q : (Matrix (Fin k) (Fin k) R)[X] :=
    matPolyEquiv (Matrix.adjugate (Matrix.charmatrix B))
  have heq : Q * (X - C B) =
      B.charpoly.map (algebraMap R (Matrix (Fin k) (Fin k) R)) := by
    calc
      Q * (X - C B) =
          matPolyEquiv (Matrix.adjugate (Matrix.charmatrix B)) *
            matPolyEquiv (Matrix.charmatrix B) := by
              rw [Matrix.matPolyEquiv_charmatrix]
      _ = matPolyEquiv
          (Matrix.adjugate (Matrix.charmatrix B) * Matrix.charmatrix B) := by
            rw [map_mul]
      _ = matPolyEquiv (B.charpoly • (1 : Matrix (Fin k) (Fin k) R[X])) := by
            rw [Matrix.adjugate_mul, Matrix.charpoly]
      _ = B.charpoly.map (algebraMap R (Matrix (Fin k) (Fin k) R)) :=
            matPolyEquiv_smul_one B.charpoly
  have hcoeff := congrArg (fun p : (Matrix (Fin k) (Fin k) R)[X] => p.coeff (d + 1)) heq
  simp only [mul_sub, coeff_sub, coeff_mul_X, coeff_mul_C, coeff_map] at hcoeff
  rw [sub_eq_iff_eq_add] at hcoeff
  simpa only [Q, Algebra.algebraMap_eq_smul_one] using hcoeff

omit [DecidableEq R] in
private theorem adjugateCharmatrix_coeff {k j : Nat}
    (B : Matrix (Fin k) (Fin k) R) (hj : j < k) :
    (matPolyEquiv (Matrix.adjugate (Matrix.charmatrix B))).coeff (k - 1 - j) =
      ∑ i ∈ Finset.range (j + 1),
        (B.charpoly.coeff (k - i)) • B ^ (j - i) := by
  induction j with
  | zero =>
      rw [adjugateCharmatrix_coeff_rec B]
      simp only [Nat.sub_zero, Nat.zero_add]
      have hindex : k - 1 + 1 = k := by omega
      rw [hindex, adjugateCharmatrix_coeff_card B]
      simp
  | succ j ih =>
      have hj' : j < k := by omega
      rw [adjugateCharmatrix_coeff_rec B]
      have hnext : k - 1 - (j + 1) + 1 = k - 1 - j := by omega
      rw [hnext, ih hj']
      have hmul :
          (∑ i ∈ Finset.range (j + 1),
              (B.charpoly.coeff (k - i)) • B ^ (j - i)) * B =
            ∑ i ∈ Finset.range (j + 1),
              (B.charpoly.coeff (k - i)) • B ^ (j + 1 - i) := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [smul_mul_assoc, ← pow_succ]
        congr 2
        have hi' := Finset.mem_range.mp hi
        omega
      rw [hmul]
      have hcoeffIndex : k - 1 - j = k - (j + 1) := by omega
      calc
        (B.charpoly.coeff (k - 1 - j)) • (1 : Matrix (Fin k) (Fin k) R) +
              ∑ i ∈ Finset.range (j + 1),
                (B.charpoly.coeff (k - i)) • B ^ (j + 1 - i) =
            (∑ i ∈ Finset.range (j + 1),
                (B.charpoly.coeff (k - i)) • B ^ (j + 1 - i)) +
              (B.charpoly.coeff (k - 1 - j)) • 1 := add_comm _ _
        _ = ∑ i ∈ Finset.range (j + 2),
              (B.charpoly.coeff (k - i)) • B ^ (j + 1 - i) := by
          have hsum := (Finset.sum_range_succ
            (f := fun i => (B.charpoly.coeff (k - i)) • B ^ (j + 1 - i))
            (n := j + 1)).symm
          simpa [hcoeffIndex, show j + 2 = (j + 1) + 1 by omega] using hsum

private theorem det_border_of_regular {S : Type*} [CommRing S] {k : Nat}
    (q : S) (r c : Fin k -> S) (B : Matrix (Fin k) (Fin k) S)
    (hB : IsRegular B.det) :
    (Matrix.fromBlocks ((fun _ _ => q) : Matrix Unit Unit S)
      ((fun _ j => r j) : Matrix Unit (Fin k) S)
      ((fun i _ => c i) : Matrix (Fin k) Unit S) B).det =
      q * B.det - ∑ i, r i * ∑ j, Matrix.adjugate B i j * c j := by
  let qM : Matrix Unit Unit S := fun _ _ => q
  let rM : Matrix Unit (Fin k) S := fun _ j => r j
  let cM : Matrix (Fin k) Unit S := fun i _ => c i
  let dM : Matrix Unit Unit S := fun _ _ => B.det
  let s : S := q * B.det - (rM * Matrix.adjugate B * cM) () ()
  let sM : Matrix Unit Unit S := fun _ _ => s
  let E : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) S :=
    Matrix.fromBlocks qM rM cM B
  let L : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) S :=
    Matrix.fromBlocks dM (-(rM * Matrix.adjugate B)) 0 1
  have hdrow : dM * rM = B.det • rM := by
    ext i j
    cases i
    rw [Matrix.mul_apply, Fintype.sum_unique]
    rfl
  have htopRight : dM * rM + (-(rM * Matrix.adjugate B)) * B = 0 := by
    rw [hdrow, Matrix.neg_mul, Matrix.mul_assoc, Matrix.adjugate_mul,
      Matrix.mul_smul, Matrix.mul_one]
    simp
  have htopLeft : dM * qM + (-(rM * Matrix.adjugate B)) * cM = sM := by
    rw [Matrix.neg_mul]
    ext i j
    cases i
    cases j
    rw [Matrix.add_apply, Matrix.mul_apply, Fintype.sum_unique]
    change B.det * q + -(rM * Matrix.adjugate B * cM) () () =
      q * B.det - (rM * Matrix.adjugate B * cM) () ()
    rw [mul_comm, sub_eq_add_neg]
  have hmul : L * E = Matrix.fromBlocks sM 0 cM B := by
    change Matrix.fromBlocks dM (-(rM * Matrix.adjugate B)) 0 1 *
      Matrix.fromBlocks qM rM cM B = Matrix.fromBlocks sM 0 cM B
    rw [Matrix.fromBlocks_multiply, htopLeft, htopRight]
    simp
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_fromBlocks_zero₂₁,
    Matrix.det_fromBlocks_zero₁₂] at hdet
  have hdetd : dM.det = B.det := by
    rw [Matrix.det_unique]
  have hdets : sM.det = s := by
    rw [Matrix.det_unique]
  have hcancel : B.det * E.det = B.det * s := by
    simpa [L, hdetd, hdets, mul_comm] using hdet
  have heq : E.det = s := hB.left.eq_iff.mp hcancel
  have hscalar : (rM * Matrix.adjugate B * cM) () () =
      ∑ i, r i * ∑ j, Matrix.adjugate B i j * c j := by
    change (∑ j, (∑ i, r i * Matrix.adjugate B i j) * c j) = _
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
  simpa [E, s, qM, hscalar] using heq

omit [DecidableEq R] in
private theorem charpoly_border {k : Nat}
    (a : R) (r c : Fin k -> R) (B : Matrix (Fin k) (Fin k) R) :
    (Matrix.fromBlocks ((fun _ _ => a) : Matrix Unit Unit R)
      ((fun _ j => r j) : Matrix Unit (Fin k) R)
      ((fun i _ => c i) : Matrix (Fin k) Unit R) B).charpoly =
      (X - C a) * B.charpoly -
        ∑ i, C (r i) * ∑ j,
          Matrix.adjugate (Matrix.charmatrix B) i j * C (c j) := by
  let aM : Matrix Unit Unit R := fun _ _ => a
  let rM : Matrix Unit (Fin k) R := fun _ j => r j
  let cM : Matrix (Fin k) Unit R := fun i _ => c i
  change (Matrix.fromBlocks aM rM cM B).charpoly = _
  have ha : Matrix.charmatrix aM =
      ((fun _ _ => X - C a) : Matrix Unit Unit R[X]) := by
    apply Matrix.ext
    intro i j
    cases i
    cases j
    rw [Matrix.charmatrix_apply_eq]
  have hr : -rM.map C =
      ((fun _ j => -C (r j)) : Matrix Unit (Fin k) R[X]) := by
    apply Matrix.ext
    intro i j
    rfl
  have hc : -cM.map C =
      ((fun i _ => -C (c i)) : Matrix (Fin k) Unit R[X]) := by
    apply Matrix.ext
    intro i j
    rfl
  have h := det_border_of_regular (S := R[X]) (q := X - C a)
    (r := fun i => -C (r i)) (c := fun i => -C (c i))
    (B := Matrix.charmatrix B) B.charpoly_monic.isRegular
  rw [Matrix.charpoly, Matrix.charmatrix_fromBlocks, Matrix.charpoly]
  rw [ha, hr, hc]
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

private theorem berkowitzMoments_get {k count : Nat}
    (B : Hex.Matrix R k k) (row w : Vector R k) (j : Nat) (hj : j < count) :
    (Hex.Matrix.berkowitzMoments B row count w).getD j 0 =
      -dotProduct (vectorEquiv row)
        (((matrixEquiv B) ^ j).mulVec (vectorEquiv w)) := by
  induction count generalizing w j with
  | zero => omega
  | succ count ih =>
      cases count with
      | zero =>
          have hj0 : j = 0 := by omega
          subst j
          rw [Hex.Matrix.berkowitzMoments.eq_def, List.getD_cons_zero, dotProduct_eq]
          simp
      | succ count =>
          cases j with
          | zero =>
              rw [Hex.Matrix.berkowitzMoments.eq_def, List.getD_cons_zero, dotProduct_eq]
              simp
          | succ j =>
              rw [Hex.Matrix.berkowitzMoments.eq_def, List.getD_cons_succ,
                ih (B * w) j (by omega), vectorEquiv_mulVec]
              rw [pow_succ, Matrix.mulVec_mulVec]

omit [DecidableEq R] in
private theorem coeff_charpoly_border {k j : Nat}
    (a : R) (r c : Fin k -> R) (B : Matrix (Fin k) (Fin k) R) (hj : j < k) :
    (Matrix.fromBlocks ((fun _ _ => a) : Matrix Unit Unit R)
      ((fun _ q => r q) : Matrix Unit (Fin k) R)
      ((fun p _ => c p) : Matrix (Fin k) Unit R) B).charpoly.coeff (k - 1 - j) =
      (if k - 1 - j = 0 then 0 else B.charpoly.coeff (k - 1 - j - 1)) -
        a * B.charpoly.coeff (k - 1 - j) -
          ∑ i ∈ Finset.range (j + 1), B.charpoly.coeff (k - i) *
            dotProduct r ((B ^ (j - i)).mulVec c) := by
  let d := k - 1 - j
  have hborder := charpoly_border a r c B
  rw [sub_mul] at hborder
  have hcoeff := congrArg (fun p : R[X] => p.coeff d) hborder
  simp only [coeff_sub, finsetSum_coeff, coeff_C_mul, coeff_mul_C] at hcoeff
  have hadj := adjugateCharmatrix_coeff B hj
  have hscalar :
      ∑ p, r p * ∑ q, (Matrix.adjugate (Matrix.charmatrix B) p q).coeff d * c q =
        ∑ i ∈ Finset.range (j + 1), B.charpoly.coeff (k - i) *
          dotProduct r ((B ^ (j - i)).mulVec c) := by
    have hentry (p q : Fin k) :
        (Matrix.adjugate (Matrix.charmatrix B) p q).coeff d =
          ∑ i ∈ Finset.range (j + 1),
            B.charpoly.coeff (k - i) * (B ^ (j - i)) p q := by
      calc
        (Matrix.adjugate (Matrix.charmatrix B) p q).coeff d =
            ((matPolyEquiv (Matrix.adjugate (Matrix.charmatrix B))).coeff d) p q := by
              rw [matPolyEquiv_coeff_apply]
        _ = (∑ i ∈ Finset.range (j + 1),
              (B.charpoly.coeff (k - i)) • B ^ (j - i)) p q := by
              simpa only [d] using congrArg
                (fun M : Matrix (Fin k) (Fin k) R => M p q) hadj
        _ = ∑ i ∈ Finset.range (j + 1),
              B.charpoly.coeff (k - i) * (B ^ (j - i)) p q := by
              rw [Matrix.sum_apply]
              simp only [Matrix.smul_apply, smul_eq_mul]
    simp_rw [hentry]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, Finset.sum_mul]
    conv_lhs =>
      enter [2, p]
      rw [Finset.sum_comm]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    ring
  rw [hscalar] at hcoeff
  dsimp only [d] at hcoeff ⊢
  by_cases hd : k - 1 - j = 0
  · rw [hd, coeff_X_mul_zero] at hcoeff
    simpa [hd] using hcoeff
  · obtain ⟨d, hd'⟩ : ∃ d, k - 1 - j = d + 1 := by
      refine ⟨k - 1 - j - 1, ?_⟩
      exact (Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hd)).symm
    rw [hd'] at hcoeff ⊢
    rw [coeff_X_mul] at hcoeff
    simpa using hcoeff

omit [DecidableEq R] in
private theorem sum_le_add_two {k j : Nat} (hj : j < k) (f : Nat -> R) :
    ∑ l : Fin (k + 1), (if l.val ≤ j + 2 then f l.val else 0) =
      (∑ l ∈ Finset.range (j + 1), f l) + f (j + 1) +
        if j + 2 < k + 1 then f (j + 2) else 0 := by
  rw [Finset.sum_fin_eq_sum_range]
  have hnormalize :
      (∑ i ∈ Finset.range (k + 1),
        if h : i < k + 1 then
          if (⟨i, h⟩ : Fin (k + 1)).val ≤ j + 2 then
            f (⟨i, h⟩ : Fin (k + 1)).val else 0
        else 0) =
        ∑ i ∈ Finset.range (k + 1), if i ≤ j + 2 then f i else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hi' := Finset.mem_range.mp hi
    simp [hi']
  rw [hnormalize]
  by_cases hlast : j + 2 < k + 1
  · have hsub : Finset.range (j + 3) ⊆ Finset.range (k + 1) := by
      intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    calc
      ∑ l ∈ Finset.range (k + 1), (if l ≤ j + 2 then f l else 0) =
          ∑ l ∈ Finset.range (j + 3), (if l ≤ j + 2 then f l else 0) := by
            symm
            apply Finset.sum_subset hsub
            intro x hx hnot
            simp only [Finset.mem_range] at hx hnot
            simp [show ¬x ≤ j + 2 by omega]
      _ = ∑ l ∈ Finset.range (j + 3), f l := by
            apply Finset.sum_congr rfl
            intro x hx
            simp only [Finset.mem_range] at hx
            simp [show x ≤ j + 2 by omega]
      _ = (∑ l ∈ Finset.range (j + 1), f l) + f (j + 1) + f (j + 2) := by
            rw [show j + 3 = (j + 2) + 1 by omega, Finset.sum_range_succ,
              show j + 2 = (j + 1) + 1 by omega, Finset.sum_range_succ]
      _ = _ := by simp [hlast]
  · have heq : k + 1 = j + 2 := by omega
    rw [heq, Finset.sum_range_succ]
    have hlower :
        (∑ x ∈ Finset.range (j + 1), if x ≤ j + 2 then f x else 0) =
          ∑ x ∈ Finset.range (j + 1), f x := by
      apply Finset.sum_congr rfl
      intro x hx
      simp only [Finset.mem_range] at hx
      simp [show x ≤ j + 2 by omega]
    rw [hlower]
    simp

omit [DecidableEq R] in
private theorem toeplitz_add_two {k : Nat} (t : Vector R (k + 2))
    (v : Vector R (k + 1)) (j : Fin k) :
    (Hex.Matrix.toeplitzMulVec t v)[(⟨j.val + 2, by omega⟩ : Fin (k + 2))] =
      (∑ i ∈ Finset.range (j.val + 1),
        t.toArray.getD (j.val + 2 - i) 0 * v.toArray.getD i 0) +
        t[(1 : Fin (k + 2))] * v[(⟨j.val + 1, by omega⟩ : Fin (k + 1))] +
          if h : j.val + 2 < k + 1 then
            t[(0 : Fin (k + 2))] * v[(⟨j.val + 2, h⟩ : Fin (k + 1))]
          else 0 := by
  rw [Hex.Matrix.getElem_toeplitzMulVec]
  have hstep :
      (fun (acc : R) (l : Fin (k + 1)) =>
        if h : l.val ≤ j.val + 2 then
          acc + t[(⟨j.val + 2 - l.val, by omega⟩ : Fin (k + 2))] * v[l]
        else acc) =
      (fun (acc : R) (l : Fin (k + 1)) =>
        acc + if l.val ≤ j.val + 2 then
          t[(⟨j.val + 2 - l.val, by omega⟩ : Fin (k + 2))] * v[l]
        else 0) := by
    funext acc l
    split <;> simp_all
  rw [hstep, foldl_finRange_eq_sum]
  let f : Nat -> R := fun i =>
    t.toArray.getD (j.val + 2 - i) 0 * v.toArray.getD i 0
  have hsum := sum_le_add_two (R := R) j.isLt f
  calc
    ∑ l : Fin (k + 1), (if l.val ≤ j.val + 2 then
        t[(⟨j.val + 2 - l.val, by omega⟩ : Fin (k + 2))] * v[l] else 0) =
        ∑ l : Fin (k + 1), (if l.val ≤ j.val + 2 then f l.val else 0) := by
          apply Finset.sum_congr rfl
          intro l hl
          by_cases hle : l.val ≤ j.val + 2
          · simp only [ite_eq_left hle, f]
            rw [← Array.getElem_eq_getD (xs := t.toArray) (i := j.val + 2 - l.val)
              (h := by simp; omega) (fallback := (0 : R)),
              ← Array.getElem_eq_getD (xs := v.toArray) (i := l.val)
                (h := by simpa using l.isLt) (fallback := (0 : R))]
            simp
          · simp [hle]
    _ = (∑ i ∈ Finset.range (j.val + 1), f i) + f (j.val + 1) +
        if j.val + 2 < k + 1 then f (j.val + 2) else 0 := hsum
    _ = _ := by
      simp only [f]
      have hsub1 : j.val + 2 - (j.val + 1) = 1 := by omega
      have hsub0 : j.val + 2 - (j.val + 2) = 0 := by omega
      rw [hsub1, hsub0]
      split_ifs with hlast
      · rw [← Array.getElem_eq_getD (xs := t.toArray) (i := 1)
            (h := by simp) (fallback := (0 : R)),
          ← Array.getElem_eq_getD (xs := v.toArray) (i := j.val + 1)
            (h := by simp) (fallback := (0 : R)),
          ← Array.getElem_eq_getD (xs := t.toArray) (i := 0)
            (h := by simp) (fallback := (0 : R)),
          ← Array.getElem_eq_getD (xs := v.toArray) (i := j.val + 2)
            (h := by simpa using hlast) (fallback := (0 : R))]
        simp
      · rw [← Array.getElem_eq_getD (xs := t.toArray) (i := 1)
            (h := by simp) (fallback := (0 : R)),
          ← Array.getElem_eq_getD (xs := v.toArray) (i := j.val + 1)
            (h := by simp) (fallback := (0 : R))]
        simp

/-- Split `Fin (k+1)` into its first coordinate and the remaining `k`. -/
private def finSuccSumEquiv (k : Nat) : Fin (k + 1) ≃ Unit ⊕ Fin k :=
  (finSuccEquiv k).trans
    ((Equiv.optionEquivSumPUnit (Fin k)).trans (Equiv.sumComm (Fin k) Unit))

@[simp]
private theorem finSuccSumEquiv_zero (k : Nat) :
    finSuccSumEquiv k 0 = Sum.inl () := by
  simp [finSuccSumEquiv]

@[simp]
private theorem finSuccSumEquiv_succ {k : Nat} (i : Fin k) :
    finSuccSumEquiv k i.succ = Sum.inr i := by
  simp [finSuccSumEquiv]

@[simp]
private theorem finSuccSumEquiv_symm_inl (k : Nat) :
    (finSuccSumEquiv k).symm (Sum.inl ()) = 0 := by
  apply (finSuccSumEquiv k).injective
  simp

@[simp]
private theorem finSuccSumEquiv_symm_inr {k : Nat} (i : Fin k) :
    (finSuccSumEquiv k).symm (Sum.inr i) = i.succ := by
  apply (finSuccSumEquiv k).injective
  simp

omit [CommRing R] [DecidableEq R] in
private theorem trailingBlock_succ_reindex {n k : Nat} (A : Hex.Matrix R n n)
    (hk : k + 1 ≤ n) :
    Matrix.reindex (finSuccSumEquiv k) (finSuccSumEquiv k)
        (matrixEquiv (Hex.Matrix.trailingBlock A (k + 1) hk)) =
      Matrix.fromBlocks
        ((fun _ _ => A[(n - k - 1, n - k - 1)]'(by omega)) :
          Matrix Unit Unit R)
        ((fun _ q => A[(n - k - 1, n - k + q.val)]'(by omega)) :
          Matrix Unit (Fin k) R)
        ((fun p _ => A[(n - k + p.val, n - k - 1)]'(by omega)) :
          Matrix (Fin k) Unit R)
        (matrixEquiv (Hex.Matrix.trailingBlock A k (by omega))) := by
  let N : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
    matrixEquiv (Hex.Matrix.trailingBlock A (k + 1) hk)
  let aM : Matrix Unit Unit R := fun _ _ =>
    A[(n - k - 1, n - k - 1)]'(by omega)
  let rM : Matrix Unit (Fin k) R := fun _ q =>
    A[(n - k - 1, n - k + q.val)]'(by omega)
  let cM : Matrix (Fin k) Unit R := fun p _ =>
    A[(n - k + p.val, n - k - 1)]'(by omega)
  let B : Matrix (Fin k) (Fin k) R :=
    matrixEquiv (Hex.Matrix.trailingBlock A k (by omega))
  have hpos : 0 < n - k := Nat.sub_pos_of_lt (by omega)
  have hshift : n - (k + 1) + 1 = n - k := by
    rw [← Nat.sub_sub]
    exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))
  change Matrix.reindex (finSuccSumEquiv k) (finSuccSumEquiv k) N =
    Matrix.fromBlocks aM rM cM B
  apply Matrix.ext
  intro i j
  rcases i with i | i <;> rcases j with j | j
  · cases i
    cases j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply,
      finSuccSumEquiv_symm_inl, Matrix.fromBlocks_apply₁₁]
    dsimp only [N, aM]
    rw [matrixEquiv_apply, Hex.Matrix.getElem_trailingBlock]
    simp only [Nat.sub_sub]
    congr 1
  · cases i
    rw [Matrix.reindex_apply, Matrix.submatrix_apply,
      finSuccSumEquiv_symm_inl, finSuccSumEquiv_symm_inr,
      Matrix.fromBlocks_apply₁₂]
    dsimp only [N, rM]
    rw [matrixEquiv_apply, Hex.Matrix.getElem_trailingBlock]
    simp only [Nat.sub_sub, Fin.val_succ, Nat.add_comm, Nat.add_assoc]
    congr 1
    apply Prod.ext
    · simp
    · rw [Nat.add_comm 1 (n - (k + 1)), hshift]
  · cases j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply,
      finSuccSumEquiv_symm_inr, finSuccSumEquiv_symm_inl,
      Matrix.fromBlocks_apply₂₁]
    dsimp only [N, cM]
    rw [matrixEquiv_apply, Hex.Matrix.getElem_trailingBlock]
    simp only [Nat.sub_sub, Fin.val_succ, Nat.add_comm, Nat.add_assoc]
    congr 1
    apply Prod.ext
    · rw [Nat.add_comm 1 (n - (k + 1)), hshift]
    · simp
  · rw [Matrix.reindex_apply, Matrix.submatrix_apply,
      finSuccSumEquiv_symm_inr i, finSuccSumEquiv_symm_inr j,
      Matrix.fromBlocks_apply₂₂]
    dsimp only [N, B]
    rw [matrixEquiv_apply, Hex.Matrix.getElem_trailingBlock,
      matrixEquiv_apply, Hex.Matrix.getElem_trailingBlock]
    simp only [Fin.val_succ, Nat.add_comm, Nat.add_assoc]
    congr 1
    apply Prod.ext <;> rw [Nat.add_comm 1 (n - (k + 1)), hshift]

omit [DecidableEq R] in
private theorem charpoly_coeff_card {m : Type*} [Fintype m] [DecidableEq m]
    (B : Matrix m m R) : B.charpoly.coeff (Fintype.card m) = 1 := by
  simpa using Matrix.charpoly_coeff_eq_sum_minors B 0 (by simp)

omit [DecidableEq R] in
private theorem coeff_charpoly_border_one {k : Nat}
    (a : R) (r c : Fin k → R) (B : Matrix (Fin k) (Fin k) R) :
    (Matrix.fromBlocks ((fun _ _ => a) : Matrix Unit Unit R)
      ((fun _ q => r q) : Matrix Unit (Fin k) R)
      ((fun p _ => c p) : Matrix (Fin k) Unit R) B).charpoly.coeff k =
      (if k = 0 then 0 else B.charpoly.coeff (k - 1)) - a := by
  cases k with
  | zero =>
      have h := congrArg (fun p : R[X] => p.coeff 0) (charpoly_border a r c B)
      simpa using h
  | succ k =>
      let M := Matrix.fromBlocks ((fun _ _ => a) : Matrix Unit Unit R)
        ((fun _ q => r q) : Matrix Unit (Fin (k + 1)) R)
        ((fun p _ => c p) : Matrix (Fin (k + 1)) Unit R) B
      have hM := Matrix.trace_eq_neg_charpoly_coeff M
      have hB := Matrix.trace_eq_neg_charpoly_coeff B
      have htrace : M.trace = a + B.trace := by
        dsimp only [M]
        rw [Matrix.trace, Fintype.sum_sum_type, Fintype.sum_unique]
        rfl
      simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_fin] at hM
      simp only [Fintype.card_fin] at hB
      dsimp only [M] at hM
      rw [htrace] at hM
      simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
      rw [show k + 1 - 1 = k by omega] at hB
      rw [show 1 + (k + 1) - 1 = k + 1 by omega] at hM
      rw [hB] at hM
      have hneg := congrArg Neg.neg hM
      calc
        (Matrix.fromBlocks ((fun _ _ => a) : Matrix Unit Unit R)
            ((fun _ q => r q) : Matrix Unit (Fin (k + 1)) R)
            ((fun p _ => c p) : Matrix (Fin (k + 1)) Unit R) B).charpoly.coeff
              (k + 1) = -(a + -B.charpoly.coeff k) := by
                simpa only [neg_neg] using hneg.symm
        _ = B.charpoly.coeff k - a := by ring

private theorem berkowitzStep_correct {n k : Nat} (A : Hex.Matrix R n n)
    (hk : k + 1 ≤ n) (v : Vector R (k + 1))
    (hv : ∀ i : Fin (k + 1), v[i] =
      (matrixEquiv (Hex.Matrix.trailingBlock A k (by omega))).charpoly.coeff
        (k - i.val)) (i : Fin (k + 2)) :
    (Hex.Matrix.berkowitzStep A k hk v)[i] =
      (matrixEquiv (Hex.Matrix.trailingBlock A (k + 1) hk)).charpoly.coeff
        (k + 1 - i.val) := by
  let N : Matrix (Fin (k + 1)) (Fin (k + 1)) R :=
    matrixEquiv (Hex.Matrix.trailingBlock A (k + 1) hk)
  let a : R := A[(n - k - 1, n - k - 1)]'(by omega)
  let r : Fin k → R := fun q => A[(n - k - 1, n - k + q.val)]'(by omega)
  let c : Fin k → R := fun p => A[(n - k + p.val, n - k - 1)]'(by omega)
  let B : Matrix (Fin k) (Fin k) R :=
    matrixEquiv (Hex.Matrix.trailingBlock A k (by omega))
  let M : Matrix (Unit ⊕ Fin k) (Unit ⊕ Fin k) R :=
    Matrix.fromBlocks ((fun _ _ => a) : Matrix Unit Unit R)
      ((fun _ q => r q) : Matrix Unit (Fin k) R)
      ((fun p _ => c p) : Matrix (Fin k) Unit R) B
  have hchar : N.charpoly = M.charpoly := by
    calc
      N.charpoly =
          (Matrix.reindex (finSuccSumEquiv k) (finSuccSumEquiv k) N).charpoly := by
            symm
            exact Matrix.charpoly_reindex (finSuccSumEquiv k) N
      _ = M.charpoly := by
        congr 1
        simpa only [N, M, a, r, c, B] using trailingBlock_succ_reindex A hk
  have hcolumn (j : Fin k) :
      (Hex.Matrix.berkowitzColumn A k hk)[
        (⟨j.val + 2, by omega⟩ : Fin (k + 2))] =
        -dotProduct r ((B ^ j.val).mulVec c) := by
    rw [Hex.Matrix.getElem_berkowitzColumn_add_two]
    rw [← List.getD_eq_getElem _ 0 (by
      rw [Hex.Matrix.length_berkowitzMoments]
      exact j.isLt)]
    have hrow : vectorEquiv
        (Hex.Matrix.berkowitzRow A k hk) = r := by
      funext q
      simp [Hex.Matrix.berkowitzRow, r]
    have hcol : vectorEquiv
        (Hex.Matrix.berkowitzCol A k hk) = c := by
      funext p
      simp [Hex.Matrix.berkowitzCol, c]
    have hmoment := berkowitzMoments_get
        (Hex.Matrix.trailingBlock A k (by omega))
        (Hex.Matrix.berkowitzRow A k hk)
        (Hex.Matrix.berkowitzCol A k hk)
        j.val j.isLt
    rw [hrow, hcol] at hmoment
    simpa only [B] using hmoment
  change (Hex.Matrix.berkowitzStep A k hk v)[i] = N.charpoly.coeff (k + 1 - i.val)
  change ∀ i : Fin (k + 1), v[i] = B.charpoly.coeff (k - i.val) at hv
  refine Fin.cases ?_ (fun i' => ?_) i
  · rw [Hex.Matrix.berkowitzStep, Hex.Matrix.getElem_toeplitzMulVec_zero,
      Hex.Matrix.getElem_berkowitzColumn_zero, hv 0]
    rw [hchar]
    simp only [Fin.val_zero, Nat.sub_zero]
    have hBtop : B.charpoly.coeff k = 1 := by
      simpa using charpoly_coeff_card B
    have hMtop : M.charpoly.coeff (k + 1) = 1 := by
      simpa [Nat.add_comm] using charpoly_coeff_card M
    rw [hBtop, hMtop, mul_one]
  · refine Fin.cases ?_ (fun j => ?_) i'
    · cases k with
      | zero =>
          change (Hex.Matrix.toeplitzMulVec
            (Hex.Matrix.berkowitzColumn A 0 hk) v)[(1 : Fin 2)] = N.charpoly.coeff 0
          rw [Hex.Matrix.getElem_toeplitzMulVec_one_base,
            Hex.Matrix.getElem_berkowitzColumn_one, hv 0]
          simp only [Fin.val_zero, Nat.sub_zero]
          have hBtop := charpoly_coeff_card B
          rw [Fintype.card_fin] at hBtop
          rw [hBtop, mul_one, hchar, coeff_charpoly_border_one]
          simp [a]
      | succ k =>
          change (Hex.Matrix.toeplitzMulVec
            (Hex.Matrix.berkowitzColumn A (k + 1) hk) v)[(1 : Fin (k + 3))] =
              N.charpoly.coeff (k + 1)
          rw [Hex.Matrix.getElem_toeplitzMulVec_one_succ,
            Hex.Matrix.getElem_berkowitzColumn_one,
            Hex.Matrix.getElem_berkowitzColumn_zero, hv 0, hv 1]
          simp only [Fin.val_zero, Nat.sub_zero]
          have hBtop : B.charpoly.coeff (k + 1) = 1 := by
            simpa using charpoly_coeff_card B
          rw [hBtop, mul_one, one_mul, hchar, coeff_charpoly_border_one]
          simp only [Nat.succ_ne_zero, ite_false, Nat.succ_sub_one]
          dsimp only [M, a, r, c, B]
          have hone : (1 : Fin (k + 2)).val = 1 := rfl
          rw [hone, Nat.succ_sub_one]
          ring
    · have hi : Fin.succ (Fin.succ j) =
          (⟨j.val + 2, by omega⟩ : Fin (k + 2)) := Fin.ext (by rfl)
      rw [hi]
      have hdegree : k + 1 - (j.val + 2) = k - 1 - j.val := by omega
      rw [hdegree, Hex.Matrix.berkowitzStep, toeplitz_add_two]
      have ht (l : Nat) (hl : l < j.val + 1) :
          (Hex.Matrix.berkowitzColumn A k hk).toArray.getD (j.val + 2 - l) 0 =
            -dotProduct r ((B ^ (j.val - l)).mulVec c) := by
        let q : Fin k := ⟨j.val - l, by omega⟩
        have hindex : j.val + 2 - l = q.val + 2 := by
          dsimp only [q]
          omega
        calc
          (Hex.Matrix.berkowitzColumn A k hk).toArray.getD (j.val + 2 - l) 0 =
              (Hex.Matrix.berkowitzColumn A k hk).toArray.getD (q.val + 2) 0 :=
                congrArg (fun x =>
                  (Hex.Matrix.berkowitzColumn A k hk).toArray.getD x 0) hindex
          _ = (Hex.Matrix.berkowitzColumn A k hk)[
              (⟨q.val + 2, by omega⟩ : Fin (k + 2))] := by
                rw [← Array.getElem_eq_getD
                  (xs := (Hex.Matrix.berkowitzColumn A k hk).toArray)
                  (i := q.val + 2) (h := by simp) (fallback := (0 : R))]
                rw [Vector.getElem_toArray]
                rfl
          _ = -dotProduct r ((B ^ (j.val - l)).mulVec c) := by
                simpa only [q] using hcolumn q
      have hvD (l : Nat) (hl : l < j.val + 1) :
          v.toArray.getD l 0 = B.charpoly.coeff (k - l) := by
        rw [← Array.getElem_eq_getD (xs := v.toArray) (i := l)
          (h := by simp; omega) (fallback := (0 : R))]
        rw [Vector.getElem_toArray]
        simpa using hv (⟨l, by omega⟩ : Fin (k + 1))
      have hprefix :
          (∑ l ∈ Finset.range (j.val + 1),
            (Hex.Matrix.berkowitzColumn A k hk).toArray.getD (j.val + 2 - l) 0 *
              v.toArray.getD l 0) =
            -∑ l ∈ Finset.range (j.val + 1), B.charpoly.coeff (k - l) *
              dotProduct r ((B ^ (j.val - l)).mulVec c) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro l hl
        have hl' := Finset.mem_range.mp hl
        rw [ht l hl', hvD l hl']
        ring
      have hvOne :
          v[(⟨j.val + 1, by omega⟩ : Fin (k + 1))] =
            B.charpoly.coeff (k - 1 - j.val) := by
        have hsub : k - (j.val + 1) = k - 1 - j.val := by omega
        exact (hv (⟨j.val + 1, by omega⟩ : Fin (k + 1))).trans
          (congrArg B.charpoly.coeff hsub)
      have hvTwo (hlast : j.val + 2 < k + 1) :
          v[(⟨j.val + 2, hlast⟩ : Fin (k + 1))] =
            B.charpoly.coeff (k - 1 - j.val - 1) := by
        have hsub : k - (j.val + 2) = k - 1 - j.val - 1 := by omega
        exact (hv (⟨j.val + 2, hlast⟩ : Fin (k + 1))).trans
          (congrArg B.charpoly.coeff hsub)
      rw [hchar]
      dsimp only [M]
      rw [coeff_charpoly_border a r c B j.isLt, hprefix,
        Hex.Matrix.getElem_berkowitzColumn_one, hvOne,
        Hex.Matrix.getElem_berkowitzColumn_zero]
      dsimp only [a]
      by_cases hlast : j.val + 2 < k + 1
      · rw [dite_eq_left hlast, hvTwo hlast, ite_eq_right (by omega)]
        ring
      · rw [dite_eq_right hlast, ite_eq_left (by omega)]
        ring

private theorem berkowitzAux_correct {n : Nat} (A : Hex.Matrix R n n)
    (k : Nat) (hk : k ≤ n) (i : Fin (k + 1)) :
    (Hex.Matrix.berkowitzAux A k hk)[i] =
      (matrixEquiv (Hex.Matrix.trailingBlock A k hk)).charpoly.coeff
        (k - i.val) := by
  induction k with
  | zero =>
      have hi : i = 0 := Fin.ext (by omega)
      subst i
      rw [Hex.Matrix.berkowitzAux]
      have htop := charpoly_coeff_card
        (matrixEquiv (Hex.Matrix.trailingBlock A 0 hk))
      rw [Fintype.card_fin] at htop
      exact htop.symm
  | succ k ih =>
      rw [Hex.Matrix.berkowitzAux]
      apply berkowitzStep_correct A hk
      intro j
      exact ih (by omega) j

private theorem berkowitz_correct {n : Nat} (A : Hex.Matrix R n n)
    (i : Fin (n + 1)) :
    (Hex.Matrix.berkowitz A)[i] =
      (matrixEquiv A).charpoly.coeff (n - i.val) := by
  rw [Hex.Matrix.berkowitz]
  simpa using berkowitzAux_correct A n (Nat.le_refl n) i

/-- The executable characteristic polynomial agrees with Mathlib's characteristic
polynomial under the dense-polynomial equivalence. -/
theorem equiv_charPoly {n : Nat} (A : Hex.Matrix R n n) :
    HexPolyMathlib.equiv (Hex.Matrix.charPoly A) =
      Matrix.charpoly (matrixEquiv A) := by
  rw [HexPolyMathlib.equiv_apply]
  apply Polynomial.ext
  intro k
  rw [HexPolyMathlib.coeff_toPolynomial]
  by_cases hk : k ≤ n
  · rw [Hex.Matrix.coeff_charPoly A hk]
    have hcoeff := berkowitz_correct A (⟨n - k, by omega⟩ : Fin (n + 1))
    simp only [Fin.getElem_fin] at hcoeff
    calc
      (Hex.Matrix.berkowitz A)[n - k] =
          (matrixEquiv A).charpoly.coeff (n - (n - k)) := by
            simpa only using hcoeff
      _ = (matrixEquiv A).charpoly.coeff k := by
            congr 1
            omega
  · have hhex : (Hex.Matrix.charPoly A).coeff k = 0 := by
      rw [Hex.Matrix.charPoly]
      apply Hex.DensePoly.coeff_eq_zero_of_size_le
      apply le_trans (Hex.DensePoly.size_ofCoeffs_le
        (R := R) (Hex.Matrix.berkowitz A).reverse.toArray)
      simpa using (show n + 1 ≤ k by omega)
    rw [hhex]
    by_cases hR : Nontrivial R
    · letI : Nontrivial R := hR
      symm
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [Matrix.charpoly_natDegree_eq_dim]
      simpa only [Fintype.card_fin] using Nat.lt_of_not_ge hk
    · haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
      exact Subsingleton.elim _ _

end HexCharPolyMathlib
