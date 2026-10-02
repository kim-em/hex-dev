/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.Lift
public import HexModularMatrix.Normalise
public import HexModularMatrix.Numerator

public section

namespace Hex.Matrix
namespace Dixon

theorem smul_mulVec (c : Int) (A : Matrix Int n m) (v : Vector Int m) :
    (c • A) * v = c • (A * v) := by
  apply Vector.ext
  intro i hi
  change ((c • A) * v)[(⟨i, hi⟩ : Fin n)] = (c • (A * v))[(⟨i, hi⟩ : Fin n)]
  rw [getElem_mulVec, row_smul, Vector.dotProduct_smul_left]
  simp only [Fin.getElem_fin, Vector.getElem_smul]
  change c * (A.row ⟨i, hi⟩).dotProduct v = c * (A * v)[(⟨i, hi⟩ : Fin n)]
  rw [getElem_mulVec]

theorem cancel_mulVec {A : Matrix Int n n} {x y : Vector Int n}
    (hA : det A ≠ 0) (h : A * x = A * y) : x = y := by
  cases n with
  | zero => exact Vector.ext (fun i hi => by omega)
  | succ n =>
    have h' := congrArg (fun v : Vector Int (n + 1) => (adjugate A) * v) h
    rw [← mul_assoc_vec, ← mul_assoc_vec, adjugate_mul,
      smul_mulVec, smul_mulVec, identity_mulVec, identity_mulVec] at h'
    apply Vector.ext
    intro i hi
    have he := congrArg (fun v : Vector Int (n + 1) => v[i]) h'
    simp only [Vector.getElem_smul] at he
    exact Int.eq_of_mul_eq_mul_left hA he

theorem solution_unique {A : Matrix Int n n} {b y z : Vector Int n} {d e : Int}
    (hA : det A ≠ 0) (hy : A * y = d • b) (hz : A * z = e • b) :
    e • y = d • z := by
  apply cancel_mulVec hA
  rw [mulVec_smul, mulVec_smul, hy, hz]
  apply Vector.ext
  intro i hi
  simp only [Vector.getElem_smul]
  change e * (d * b[i]) = d * (e * b[i])
  grind only

theorem common_mul (y : Vector Int n) (d t : Int) :
    common (y.map (fun v => t * v)) (t * d) = t.natAbs * common y d := by
  simp only [common, Vector.foldl_map, Int.natAbs_mul]
  rw [← Vector.foldl_toList, ← Vector.foldl_toList]
  apply List.foldl_hom (fun g => t.natAbs * g)
  intro a b
  exact Nat.gcd_mul_left t.natAbs a b.natAbs

theorem common_eq_one {y : Vector Int n} {d : Int} (_hd : 0 < d)
    (hred : ∀ g : Int, (∀ i : Fin n, g ∣ y[i]) → g ∣ d → g ∣ 1) :
    common y d = 1 := by
  obtain ⟨hdvd, hy⟩ := (common_dvd y d (common y d)).mp (Int.dvd_refl _)
  have h := hred (common y d) hy hdvd
  exact Nat.eq_one_of_dvd_one (Int.ofNat_dvd.mp h)

/-- Cramer's numerator is the corresponding adjugate product entry. -/
theorem cramer (A : Matrix Int (n + 1) (n + 1)) (b : Vector Int (n + 1))
    (j : Fin (n + 1)) : det (replaceCol A b j) = (adjugate A * b)[j] := by
  have h : replaceCol A b j = (setRow A.transpose j b).transpose := by
    rw [transpose_setRow, transpose_transpose]
    apply ext_getElem
    intro i k
    simp only [replaceCol, getElem_ofFn, getElem_setCol, getElem_pair_eq_nested]
  rw [h, det_transpose, det_setRow_eq_cofactorRowPairing]
  simp only [cofactorRowPairing, Fin.foldl_eq_finRange_foldl, getElem_mulVec,
    Vector.dotProduct, getElem_row, adjugate_get, cofactor_transpose]
  apply List.foldl_congr
  intro a k _
  congr 1
  exact Int.mul_comm _ _

end Dixon

/-- A reduced common denominator of an integer linear solve divides the determinant. -/
theorem dvd_det_of_mulVec {A : Matrix Int n n} {y b : Vector Int n} {d : Int}
    (hA : det A ≠ 0) (h : A.mulVec y = d • b) (hd : 0 < d)
    (hred : ∀ g : Int, (∀ i : Fin n, g ∣ y[i]) → g ∣ d → g ∣ 1) :
    d ∣ det A := by
  have hentries : ∀ i : Fin n, d ∣ det A * y[i] := by
    cases n with
    | zero => intro i; exact i.elim0
    | succ n =>
      change A * y = d • b at h
      have heq := congrArg (fun v : Vector Int (n + 1) => adjugate A * v) h
      rw [← mul_assoc_vec, adjugate_mul, Dixon.smul_mulVec,
        identity_mulVec, mulVec_smul] at heq
      intro i
      have hi := congrArg (fun v : Vector Int (n + 1) => v[i]) heq
      simp only [Fin.getElem_fin, Vector.getElem_smul] at hi
      exact ⟨(adjugate A * b)[i], hi⟩
  have hc : d ∣ (Dixon.common (y.map fun v => det A * v) (det A * d) : Int) := by
    apply (Dixon.common_dvd _ _ d).mpr
    refine ⟨Int.dvd_mul_left _ _, ?_⟩
    intro i
    simpa only [Fin.getElem_fin, Vector.getElem_map] using hentries i
  rw [Dixon.common_mul, Dixon.common_eq_one hd hred, Nat.mul_one] at hc
  exact Int.dvd_natAbs.mp hc

end Hex.Matrix
