/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexPosDefTheory.Producer
public import HexPosDefTheory.Lists
import all HexPosDef.Producer

public section

/-! Acceptance of the certificates extracted from native elimination states. -/

open Matrix

namespace Hex.PosDefTheory.Producer

open Hex.PosDef
open Hex.Matrix.Lists (entry all_iff entry_eq_getD)
open HexMatrixTheory (matrixEquiv)

variable {R : Type} [CommRing R]

def triangle (s : PosDef.Producer.State R n) : List (List R) :=
  (List.finRange n).map fun i => (s.right.getRow i).toList.take (i.val + 1)

omit [CommRing R] in
theorem rows_shape (M : Hex.Matrix R n n) : PosDef.Lists.shape n n M.rowLists = true := by
  simp [PosDef.Lists.shape, Hex.Matrix.rowLists]

theorem rows_get (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (M : Hex.Matrix R n n) (i j : Fin n) :
    PosDef.Lists.get a.toArithmetic M.rowLists i j = M[i][j] := by
  change entry a.zero (entry [] M.rowLists i) j = _
  rw [hz]
  exact Hex.Matrix.get_rowLists M i j

theorem vector_entry (M : Hex.Matrix R n n) (i j : Fin n) :
    entry 0 (M.getRow i).toList j = M[i][j] := by
  simp [entry_eq_getD, List.getD_eq_getElem?_getD, j.isLt]

omit [CommRing R] in
theorem triangle_row (s : PosDef.Producer.State R n) (i : Fin n) :
    entry [] (triangle s) i = (s.right.getRow i).toList.take (i.val + 1) := by
  simp [triangle, entry_eq_getD, List.getD_eq_getElem?_getD, i.isLt]

omit [CommRing R] in
theorem triangularShape_of_rows (k : Nat) (rows : List (List R))
    (h : ∀ i, i < rows.length → (entry [] rows i).length = k + i + 1) :
    PosDef.Lists.triangularShape k rows = true := by
  induction rows generalizing k with
  | nil => rfl
  | cons row rows ih =>
    apply Bool.and_eq_true_iff.mpr
    refine ⟨?_, ih (k + 1) ?_⟩
    · simpa [entry] using h 0 (by simp)
    · intro i hi
      simpa [entry, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i + 1) (by simpa using hi)

omit [CommRing R] in
theorem triangle_shape (s : PosDef.Producer.State R n) :
    PosDef.Lists.triangularShape 0 (triangle s) = true := by
  apply triangularShape_of_rows
  intro i hi
  have hin : i < n := by simpa [triangle] using hi
  rw [triangle_row s ⟨i, hin⟩]
  simp [Nat.min_eq_left (by omega : i + 1 ≤ n)]

theorem triangle_entry (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (s : PosDef.Producer.State R n) (hlower : (matrixEquiv s.right).IsLowerTriangular)
    (i j : Fin n) : entry a.zero (entry [] (triangle s) i) j = s.right[i][j] := by
  rw [triangle_row, hz]
  by_cases hj : j.val < i.val + 1
  · simp [entry_eq_getD, List.getD_eq_getElem?_getD, hj]
  · rw [entry_eq_getD, HexMatrixTheory.getD_eq_default' _ _ _ (by simp; omega)]
    have he := hlower (show i < j by omega)
    simpa only [entry_eq] using he.symm

theorem dot_sum (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (n : Nat) (xs ys : List R) (hx : xs.length ≤ n) :
    PosDef.Lists.dot a.toArithmetic xs ys =
      ∑ i : Fin n, entry a.zero xs i * entry a.zero ys i := by
  induction n generalizing xs ys with
  | zero =>
    have he : xs = [] := List.length_eq_zero_iff.mp (by omega)
    simp [he, PosDef.Lists.dot, hz]
  | succ n ih =>
    cases xs with
    | nil => simp [PosDef.Lists.dot, entry, hz]
    | cons x xs =>
      cases ys with
      | nil => simp [PosDef.Lists.dot, entry, hz]
      | cons y ys =>
        simpa [PosDef.Lists.dot, hadd, hmul, Fin.sum_univ_succ, entry] using
          congrArg (fun z => x * y + z) (ih xs ys (by simpa using hx))

theorem dot_triangle (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (B : Hex.Matrix R n n) (s : PosDef.Producer.State R n)
    (hlower : (matrixEquiv s.right).IsLowerTriangular) (i j : Fin n) :
    PosDef.Lists.dot a.toArithmetic (entry [] (triangle s) i)
      (PosDef.Lists.column a.toArithmetic j B.rowLists) =
        (matrixEquiv s.right * matrixEquiv B) i j := by
  rw [dot_sum a hz hadd hmul n _ _ (by rw [triangle_row]; simp), Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [triangle_entry a hz s hlower,
    Lists.column_entry, rows_get a hz, entry_eq, entry_eq]

theorem hermitian_true [StarRing R] (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hconj : ∀ x, a.conj x = star x) (heq : ∀ x y, a.eq x y = true ↔ x = y)
    (B : Hex.Matrix R n n) (hB : (matrixEquiv B).IsHermitian) :
    PosDef.Lists.hermitian a.toArithmetic n B.rowLists = true := by
  apply (all_iff _ n).mpr
  intro i hi
  apply (all_iff _ n).mpr
  intro j hj
  apply (heq _ _).mpr
  rw [rows_get a hz B ⟨i, hi⟩ ⟨j, hj⟩, rows_get a hz B ⟨j, hj⟩ ⟨i, hi⟩, hconj]
  have he := congrFun (congrFun hB (⟨i, hi⟩ : Fin n)) (⟨j, hj⟩ : Fin n)
  simpa only [Matrix.conjTranspose_apply, entry_eq] using he.symm

theorem positive_check [StarRing R] (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (hconj : ∀ x, a.conj x = star x) (heq : ∀ x y, a.eq x y = true ↔ x = y)
    (hpos : ∀ z : Int, 0 < z → a.positive (z : R) = true)
    (B : Hex.Matrix R n n) (s : PosDef.Producer.State R n)
    (h : Invariant B n s) (hB : (matrixEquiv B).IsHermitian) :
    PosDef.Lists.triangular a.toArithmetic n B.rowLists (triangle s) = true := by
  simp only [PosDef.Lists.triangular, Bool.and_eq_true_iff]
  refine ⟨⟨⟨by simp [triangle], triangle_shape s⟩,
    hermitian_true a hz hconj heq B hB⟩, ?_⟩
  have hd (i j : Fin n) :
      PosDef.Lists.dot a.toArithmetic (entry [] (triangle s) i)
        (PosDef.Lists.column a.toArithmetic j B.rowLists) = s.left[i][j] := by
    rw [dot_triangle a hz hadd hmul B s h.lower]
    simpa only [entry_eq] using congrFun (congrFun h.product.symm i) j
  apply (all_iff _ n).mpr
  intro i hi
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · apply (all_iff _ i).mpr
    intro j hj
    rw [hd ⟨i, hi⟩ ⟨j, by omega⟩, h.zeros ⟨i, hi⟩ ⟨j, by omega⟩ (by omega) hj, hz]
    exact (heq 0 0).mpr rfl
  · obtain ⟨p, l, hp, hl, hli, hri⟩ := h.frozen ⟨i, hi⟩ hi
    rw [hd ⟨i, hi⟩ ⟨i, hi⟩, triangle_entry a hz s h.lower ⟨i, hi⟩ ⟨i, hi⟩,
      hmul, hconj, hli, hri, star_intCast, ← Int.cast_mul]
    exact hpos (p * l) (mul_pos hp hl)

theorem diagonal_check [StarRing R] [Nontrivial R]
    (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0) (ho : a.one = 1)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (hconj : ∀ x, a.conj x = star x) (heq : ∀ x y, a.eq x y = true ↔ x = y)
    (B : Hex.Matrix R n n) (hB : (matrixEquiv B).IsHermitian)
    (hdiag : ∀ i : Fin n, a.positive B[i][i] = true)
    (hoff : ∀ i j : Fin n, i ≠ j → B[i][j] = 0) :
    PosDef.Lists.triangular a.toArithmetic n B.rowLists
      (triangle (PosDef.Producer.initial a B)) = true := by
  let s := PosDef.Producer.initial a B
  have h0 := initial_invariant a hz ho B
  have hd (i j : Fin n) :
      PosDef.Lists.dot a.toArithmetic (entry [] (triangle s) i)
        (PosDef.Lists.column a.toArithmetic j B.rowLists) = B[i][j] := by
    rw [dot_triangle a hz hadd hmul B s h0.lower]
    simpa only [entry_eq, PosDef.Producer.initial, s] using
      congrFun (congrFun h0.product.symm i) j
  have hii (i : Fin n) : s.right[i][i] = 1 := by
    change (Hex.Matrix.ofFn (fun i j : Fin n => if i = j then a.one else a.zero))[i][i] = 1
    rw [Hex.Matrix.getElem_ofFn]
    simp [ho]
  simp only [PosDef.Lists.triangular, Bool.and_eq_true_iff]
  refine ⟨⟨⟨by simp [triangle], triangle_shape s⟩,
    hermitian_true a hz hconj heq B hB⟩, ?_⟩
  apply (all_iff _ n).mpr
  intro i hi
  apply Bool.and_eq_true_iff.mpr
  refine ⟨?_, ?_⟩
  · apply (all_iff _ i).mpr
    intro j hj
    have hne : (⟨i, hi⟩ : Fin n) ≠ ⟨j, by omega⟩ := by
      intro he
      exact (Nat.ne_of_gt hj) (Fin.mk.inj he)
    rw [hd ⟨i, hi⟩ ⟨j, by omega⟩, hoff _ _ hne, hz]
    exact (heq 0 0).mpr rfl
  · rw [hd ⟨i, hi⟩ ⟨i, hi⟩, triangle_entry a hz s h0.lower ⟨i, hi⟩ ⟨i, hi⟩,
      hii, hmul, hconj, star_one, mul_one]
    exact hdiag ⟨i, hi⟩

theorem conj_entry [StarRing R] (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hconj : ∀ x, a.conj x = star x) (xs : List R) (i : Nat) :
    entry a.zero (xs.map a.conj) i = star (entry a.zero xs i) := by
  have hzero : a.conj a.zero = a.zero := by rw [hconj, hz, star_zero]
  rw [Lists.entry_map a.conj hzero, hconj]

theorem mulVec_entry (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (B : Hex.Matrix R n n) (v : List R) (i : Fin n) :
    entry a.zero (PosDef.Lists.mulVec a.toArithmetic B.rowLists v) i =
      ∑ j : Fin n, B[i][j] * entry a.zero v j := by
  have hlen := Hex.Matrix.length_rowLists B
  simp only [PosDef.Lists.mulVec, entry_eq_getD]
  rw [HexMatrixTheory.getD_eq_getElem' _ _ _ (by simp [hlen]), List.getElem_map]
  have hr := Hex.Matrix.entry_rowLists B i
  rw [entry_eq_getD, HexMatrixTheory.getD_eq_getElem' _ _ _ (by simp [hlen])] at hr
  rw [hr]
  simp only [Hex.Matrix.getElem_eq_getRow]
  rw [dot_sum a hz hadd hmul n (B.getRow i).toList v (by simp)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hz, vector_entry B i j]
  simp only [entry_eq_getD, Hex.Matrix.getElem_eq_getRow]

theorem quadratic_row [StarRing R] (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (hconj : ∀ x, a.conj x = star x)
    (B : Hex.Matrix R n n) (s : PosDef.Producer.State R n) (k : Fin n)
    (hprod : matrixEquiv s.left = matrixEquiv s.right * matrixEquiv B) :
    let v := (s.right.getRow k).toList.map a.conj
    PosDef.Lists.dot a.toArithmetic (v.map a.conj) (PosDef.Lists.mulVec a.toArithmetic B.rowLists v) =
      ∑ j : Fin n, s.left[k][j] * star (s.right[k][j]) := by
  let v := (s.right.getRow k).toList.map a.conj
  have hv (i : Fin n) : entry a.zero v i = star (s.right[k][i]) := by
    rw [conj_entry a hz hconj, hz, vector_entry]
  have hvv (i : Fin n) : entry a.zero (v.map a.conj) i = s.right[k][i] := by
    rw [conj_entry a hz hconj, hv, star_star]
  change PosDef.Lists.dot a.toArithmetic (v.map a.conj) _ = _
  rw [dot_sum a hz hadd hmul n _ _ (by simp [v])]
  simp only [hvv, mulVec_entry a hz hadd hmul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have he : (∑ i : Fin n, s.right[k][i] * B[i][j]) = s.left[k][j] := by
    simpa only [Matrix.mul_apply, entry_eq] using congrFun (congrFun hprod.symm k) j
  rw [← he, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_assoc, hv j]

theorem negative_check [StarRing R] [CharZero R]
    (a : PosDef.Producer.Arithmetic R) (hz : a.zero = 0)
    (hadd : ∀ x y, a.add x y = x + y) (hmul : ∀ x y, a.mul x y = x * y)
    (hconj : ∀ x, a.conj x = star x) (heq : ∀ x y, a.eq x y = true ↔ x = y)
    (hneg : ∀ z : Int, z ≤ 0 → a.nonpositive (z : R) = true)
    (B : Hex.Matrix R n n) (s : PosDef.Producer.State R n) (k : Fin n)
    (h : Invariant B k.val s) (p : Int) (hp : p ≤ 0) (hpivot : s.left[k][k] = (p : R)) :
    PosDef.Lists.negative a.toArithmetic n B.rowLists
      (.nonpositive ((s.right.getRow k).toList.map a.conj)) = true := by
  let v := (s.right.getRow k).toList.map a.conj
  have hv (i : Fin n) : entry a.zero v i = star (s.right[k][i]) := by
    rw [conj_entry a hz hconj, hz, vector_entry]
  have hlen : v.length = n := by simp [v]
  have hnonzero : entry a.zero v k ≠ a.zero := by
    rw [hv, h.diagonal k (by omega), hz]
    exact star_ne_zero.mpr (Int.cast_ne_zero.mpr h.previous_pos.ne')
  simp only [PosDef.Lists.negative, Bool.and_eq_true_iff, Nat.beq_eq]
  refine ⟨⟨hlen, ?_⟩, ?_⟩
  · apply List.any_eq_true.mpr
    have hmem : entry a.zero v k ∈ v := by
      rw [entry_eq_getD, HexMatrixTheory.getD_eq_getElem' _ _ _ (by omega)]
      exact List.getElem_mem _
    refine ⟨_, hmem, ?_⟩
    cases he : a.eq (entry a.zero v k) a.zero with
    | false => rfl
    | true => exact (hnonzero ((heq _ _).mp he)).elim
  · rw [quadratic_row a hz hadd hmul hconj B s k h.product, Finset.sum_eq_single k]
    · rw [hpivot, h.diagonal k (by omega), star_intCast, ← Int.cast_mul]
      exact hneg (p * s.previous) (mul_nonpos_of_nonpos_of_nonneg hp h.previous_pos.le)
    · intro j _ hjk
      rcases lt_or_gt_of_ne hjk with hjk | hjk
      · rw [h.zeros k j hjk hjk, zero_mul]
      · have he : s.right[k][j] = 0 := by simpa only [entry_eq] using h.lower hjk
        rw [he, star_zero, mul_zero]
    · simp

end Hex.PosDefTheory.Producer
