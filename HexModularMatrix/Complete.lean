/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexModularMatrix.SolveMat
import all HexModularMatrix.Solve
import all HexModularMatrix.SolveMat
import all HexModularMatrix.Lift

public section

namespace Hex.Matrix
namespace Dixon

/-- Cramer's rule supplies a bounded positive-denominator matrix solution. -/
theorem cramer_exists [LawfulDetBound] (A : Matrix Int n n) (C : Matrix Int n m)
    (hA : det A ≠ 0) (P : Nat)
    (hP : ∀ j : Fin m, numeratorBound A (C.col j) ≤ P) :
    ∃ Y : Matrix Int n m, ∃ d : Int, 0 < d ∧ d ≤ hadamardBound A ∧
      A * Y = d • C ∧ ∀ (i : Fin n) (j : Fin m), Y[i][j].natAbs ≤ P := by
  cases n with
  | zero =>
    refine ⟨0, 1, by decide, ?_, ?_, fun i => i.elim0⟩
    · simp [hadamardBound, DetBound.prod]
    · apply ext_getElem; intro i; exact i.elim0
  | succ n =>
    refine ⟨(det A).sign • (adjugate A * C), (det A).natAbs, ?_, ?_, ?_, ?_⟩
    · have := Int.natAbs_pos.mpr hA; omega
    · exact_mod_cast LawfulDetBound.natAbs_det_le A
    · rw [mul_scale, ← mul_assoc, mul_adjugate, smul_mul, identity_mul]
      apply ext_getElem
      intro i j
      simp only [smul_getElem]
      change (det A).sign * (det A * C[i][j]) = (det A).natAbs * C[i][j]
      rw [← Int.mul_assoc, Int.sign_mul_self]
    · intro i j
      rw [smul_getElem]
      change ((det A).sign * (adjugate A * C)[i][j]).natAbs ≤ P
      rw [Int.natAbs_mul, Int.natAbs_sign_of_ne_zero hA, Nat.one_mul]
      have hc := Nat.le_trans (numeratorBound_spec A (C.col j) i) (hP j)
      rw [cramer] at hc
      simpa only [getElem_mul, getElem_mulVec] using hc

/-- Reduce the Cramer solution as a whole without increasing either bound. -/
theorem reduced_exists [LawfulDetBound] (A : Matrix Int n n) (C : Matrix Int n m)
    (hA : det A ≠ 0) (P : Nat)
    (hP : ∀ j : Fin m, numeratorBound A (C.col j) ≤ P) :
    ∃ y : Vector Int (n * m), ∃ d : Int, 0 < d ∧ d ≤ hadamardBound A ∧
      A * unflatten y = d • C ∧ (∀ i : Fin (n * m), y[i].natAbs ≤ P) ∧
      (∀ g : Int, (∀ i : Fin (n * m), g ∣ y[i]) → g ∣ d → g ∣ 1) := by
  obtain ⟨Y, d, hd, hQ, heq, hY⟩ := cramer_exists A C hA P hP
  let y := flatten Y
  let z := normalise y d
  let c : Int := common y d
  have hc : c ≠ 0 := by have := common_pos y d hd; dsimp [c]; omega
  obtain ⟨hs, hv⟩ := normalise_scale y d
  have hz : c • unflatten z.1 = Y := by
    apply ext_getElem
    intro i j
    rw [smul_getElem, unflatten_get]
    change c * z.1[i.val * m + j.val]'(flatIdx_lt i.isLt j.isLt) = Y[i][j]
    have h := hv ⟨i.val * m + j.val, flatIdx_lt i.isLt j.isLt⟩
    simpa only [Fin.getElem_fin, y, flatten_get, c, z] using h
  refine ⟨z.1, z.2, normalise_pos y d hd,
    Int.le_trans (normalise_den_le y d hd) hQ, ?_, ?_, normalise_reduced y d hd⟩
  · have he := congrArg (fun M : Matrix Int n m => M) heq
    rw [← hz, mul_scale] at he
    apply ext_getElem
    intro i j
    apply Int.eq_of_mul_eq_mul_left hc
    have hij := congrArg (fun M : Matrix Int n m => M[i][j]) he
    simp only [smul_getElem] at hij ⊢
    change c * (A * unflatten z.1)[i][j] = c * (z.2 * C[i][j])
    change c * (A * unflatten z.1)[i][j] = d * C[i][j] at hij
    rw [hij]
    change c * z.2 = d at hs
    grind only
  · intro i
    apply Nat.le_trans (normalise_num_le y d i)
    have h := hY ⟨i.val / m, row_of_lt i⟩ ⟨i.val % m, col_of_lt i⟩
    simpa only [y, flatten, Fin.getElem_fin, Vector.getElem_ofFn, getElem_pair_eq_nested] using h

/-- Every exact solution is congruent to the lifted solution after multiplication
by its denominator. No primality hypothesis is needed. -/
theorem lift_congr (D : Decomp n) (C Y : Matrix Int n m) (d : Int) (k : Nat)
    (h : D.A * Y = d • C) (i : Fin n) (j : Fin m) :
    (d * (liftMat D C k)[i][j] - Y[i][j]) % ((D.p : Int) ^ k) = 0 := by
  have hc : ∀ (i : Fin n) (j : Fin m),
      (D.p : Int) ^ k ∣ (D.A * (d • liftMat D C k - Y))[i][j] := by
    intro i j
    rw [mul_sub, mul_scale, h, getElem_sub, smul_getElem, smul_getElem]
    change (D.p : Int) ^ k ∣ d * (D.A * liftMat D C k)[i][j] - d * C[i][j]
    rw [← Int.mul_sub]
    exact Int.dvd_mul_of_dvd_right (Int.dvd_of_emod_eq_zero (liftMat_spec D C k i j))
  have hz := cancel_power D (d • liftMat D C k - Y) k hc i j
  simp only [getElem_sub, smul_getElem] at hz
  exact Int.emod_eq_zero_of_dvd hz

theorem matrixBound_ge (A : Matrix Int n n) (C : Matrix Int n m) (j : Fin m) :
    numeratorBound A (C.col j) ≤ matrixBound A C := by
  unfold matrixBound
  rw [Fin.foldl_eq_finRange_foldl]
  have go (xs : List (Fin m)) (s : Nat) :
      (∀ j ∈ xs, numeratorBound A (C.col j) ≤ xs.foldl
        (fun P j => max P (numeratorBound A (C.col j))) s) ∧
      s ≤ xs.foldl (fun P j => max P (numeratorBound A (C.col j))) s := by
    induction xs generalizing s with
    | nil => simp
    | cons i xs ih =>
      obtain ⟨hxs, hs⟩ := ih (max s (numeratorBound A (C.col i)))
      refine ⟨?_, Nat.le_trans (Nat.le_max_left _ _) hs⟩
      intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · exact Nat.le_trans (Nat.le_max_right _ _) hs
      · exact hxs j hj
  exact (go _ 0).1 j (List.mem_finRange j)

theorem reconstruct_exists [LawfulDetBound] (D : Decomp n) (C : Matrix Int n m) :
    ∃ y d, Modular.ratReconVec?
      (flatten (liftMat D C (digits D (matrixBound D.A C) (hadamardBound D.A))))
      (D.p ^ digits D (matrixBound D.A C) (hadamardBound D.A))
      (matrixBound D.A C) (hadamardBound D.A) = some (y, d) ∧
      checkMat D.A C y d = some (unflatten y, d) := by
  let P := matrixBound D.A C
  let Q := hadamardBound D.A
  let k := digits D P Q
  obtain ⟨y, d, hd, hQ, heq, hy, hred⟩ := reduced_exists D.A C D.det_ne_zero P (matrixBound_ge _ _)
  have hcong (i : Fin (n * m)) :
      (d * (flatten (liftMat D C k))[i] - y[i]) % ((D.p ^ k : Nat) : Int) = 0 := by
    have h := lift_congr D C (unflatten y) d k heq
      ⟨i.val / m, row_of_lt i⟩ ⟨i.val % m, col_of_lt i⟩
    rw [unflatten_get] at h
    simpa only [flatten, Fin.getElem_fin, Vector.getElem_ofFn, getElem_pair_eq_nested,
      Nat.mul_comm (i.val / m) m, Nat.div_add_mod, Int.natCast_pow] using h
  have hr := Modular.ratReconVec?_complete (a := flatten (liftMat D C k))
    (P := (P : Int)) (Q := (Q : Int)) (m := D.p ^ k)
    (by exact_mod_cast digits_spec D P Q) (by omega) hd hQ
    (fun i => ⟨hcong i, by exact_mod_cast hy i⟩) hred
  refine ⟨y, d, hr, ?_⟩
  simp only [checkMat, hd, ↓reduceIte, normalise_eq hred, heq]

end Dixon

theorem solveMatWith_isSome [LawfulDetBound] (D : Decomp n) (C : Matrix Int n m) :
    (solveMatWith D C).isSome := by
  obtain ⟨y, d, hr, hc⟩ := Dixon.reconstruct_exists D C
  simp only [solveMatWith, hr, Option.bind_eq_bind, Option.bind_some, hc, Option.isSome_some]

theorem solveWith_isSome [LawfulDetBound] (D : Decomp n) (b : Vector Int n) :
    (solveWith D b).isSome := by
  let C : Matrix Int n 1 := Matrix.ofFn fun i _ => b[i]
  let P := numeratorBound D.A b
  let Q := hadamardBound D.A
  let k := Dixon.digits D P Q
  have hcol (j : Fin 1) : C.col j = b := by
    apply Vector.ext
    intro i hi
    change (C.col j)[(⟨i, hi⟩ : Fin n)] = b[(⟨i, hi⟩ : Fin n)]
    rw [getElem_col]
    simp only [C, getElem_ofFn]
  obtain ⟨y, d, hd, hQ, heq, hy, hred⟩ := Dixon.reduced_exists D.A C D.det_ne_zero P
    (fun j => by rw [hcol]; exact Nat.le_refl _)
  let v : Vector Int n := Vector.ofFn fun i => y[i.val]'(by simp)
  have hv (i : Fin n) : (Dixon.unflatten y : Matrix Int n 1)[i][(0 : Fin 1)] = v[i] := by
    rw [Dixon.unflatten_get]
    simp only [Fin.val_zero, Nat.mul_one, Nat.add_zero,
      v, Fin.getElem_fin, Vector.getElem_ofFn]
  have hc : (Dixon.unflatten y : Matrix Int n 1).col 0 = v := by
    apply Vector.ext
    intro i hi
    change ((Dixon.unflatten y : Matrix Int n 1).col 0)[(⟨i, hi⟩ : Fin n)] = v[(⟨i, hi⟩ : Fin n)]
    rw [getElem_col, hv]
  have he : D.A * v = d • b := by
    apply Vector.ext
    intro i hi
    have h := congrArg (fun M : Matrix Int n 1 => M[(⟨i, hi⟩ : Fin n)][(0 : Fin 1)]) heq
    rw [getElem_mul, hc, smul_getElem] at h
    simp only [C, getElem_ofFn] at h
    change (D.A * v)[(⟨i, hi⟩ : Fin n)] = (d • b)[(⟨i, hi⟩ : Fin n)]
    rw [getElem_mulVec]
    simpa only [Fin.getElem_fin, Vector.getElem_smul] using h
  have hredv : ∀ g : Int, (∀ i : Fin n, g ∣ v[i]) → g ∣ d → g ∣ 1 := by
    intro g hg hg'
    apply hred g ?_ hg'
    intro i
    have h := hg ⟨i.val, by simpa using i.isLt⟩
    simpa only [v, Fin.getElem_fin, Vector.getElem_ofFn] using h
  have hcong (i : Fin n) : (d * (D.lift b k)[i] - v[i]) % ((D.p ^ k : Nat) : Int) = 0 := by
    have h := Dixon.lift_congr D C (Dixon.unflatten y) d k heq i 0
    rw [hv] at h
    simpa only [Decomp.lift, getElem_col, Int.natCast_pow, C] using h
  have hr := Modular.ratReconVec?_complete (a := D.lift b k)
    (P := (P : Int)) (Q := (Q : Int)) (m := D.p ^ k)
    (by exact_mod_cast Dixon.digits_spec D P Q) (by omega) hd hQ
    (fun i => ⟨hcong i, by
      have h := hy ⟨i.val, by simp⟩
      have hvb : v[i].natAbs ≤ P := by simpa only [v, Fin.getElem_fin, Vector.getElem_ofFn] using h
      exact_mod_cast hvb⟩) hredv
  have hcheck : Dixon.check D.A b v d = some (v, d) := by
    simp only [Dixon.check, hd, ↓reduceIte, Dixon.normalise_eq hredv, he]
  dsimp [P, Q, k] at hr
  simp only [solveWith, hr, Option.bind_eq_bind, Option.bind_some, hcheck, Option.isSome_some]

end Hex.Matrix
