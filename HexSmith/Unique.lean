/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexSmith.Correct
public import HexSmith.Divisor

public section

/-! Uniqueness of Smith rank and invariant factors. -/

namespace Hex.Matrix

private theorem foldl_mul_pos {R : Type} (xs : List R) (f : R → Int)
    (acc : Int) (hacc : 0 < acc) (hall : ∀ x ∈ xs, 0 < f x) :
    0 < xs.foldl (fun product x => product * f x) acc := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x xs ih =>
      apply ih (acc * f x) (Int.mul_pos hacc (hall x (by simp)))
      intro y hy
      exact hall y (List.mem_cons_of_mem x hy)

private theorem IsSNF.prefix_pos {A : Matrix Int n m} {S : SmithData n m}
    (h : IsSNF A S) (k : Nat) (hk : k ≤ S.rank) :
    0 < (S.diag.take k).foldl (· * ·) 1 := by
  rw [foldl_take_eq_finFoldl S.diag k hk, Fin.foldl_eq_finRange_foldl]
  apply foldl_mul_pos (List.finRange k)
    (fun i => S.diag[(⟨i.val, by omega⟩ : Fin S.rank)]) 1 (by omega)
  intro i _hi
  exact h.diag_pos (⟨i.val, by omega⟩ : Fin S.rank)

/-- Any two Smith witnesses for the same matrix have the same rank. -/
theorem IsSNF.rank_eq {A : Matrix Int n m} {S S' : SmithData n m}
    (h : IsSNF A S) (h' : IsSNF A S') : S.rank = S'.rank := by
  apply Nat.le_antisymm
  · apply Nat.le_of_not_gt
    intro hlt
    let k := S'.rank + 1
    have heq := h.detDivisor_eq k
    rw [if_pos (by simp [k]; omega)] at heq
    have heq' := h'.detDivisor_eq k
    rw [if_neg (by simp [k])] at heq'
    rw [heq] at heq'
    have hpos := h.prefix_pos k (by simp [k]; omega)
    exact (Int.natAbs_ne_zero.mpr (Int.ne_of_gt hpos)) heq'
  · apply Nat.le_of_not_gt
    intro hlt
    let k := S.rank + 1
    have heq := h.detDivisor_eq k
    rw [if_neg (by simp [k])] at heq
    have heq' := h'.detDivisor_eq k
    rw [if_pos (by simp [k]; omega)] at heq'
    rw [heq'] at heq
    have hpos := h'.prefix_pos k (by simp [k]; omega)
    exact (Int.natAbs_ne_zero.mpr (Int.ne_of_gt hpos)) heq

private theorem IsSNF.prefix_eq {A : Matrix Int n m} {S S' : SmithData n m}
    (h : IsSNF A S) (h' : IsSNF A S') (hrank : S.rank = S'.rank)
    (k : Nat) (hk : k ≤ S.rank) :
    (S.diag.take k).foldl (· * ·) 1 =
      (S'.diag.take k).foldl (· * ·) 1 := by
  have heq := h.detDivisor_eq k
  rw [if_pos hk] at heq
  have heq' := h'.detDivisor_eq k
  rw [if_pos (by omega)] at heq'
  have habs : ((S.diag.take k).foldl (· * ·) 1).natAbs =
      ((S'.diag.take k).foldl (· * ·) 1).natAbs := heq.symm.trans heq'
  have hnonneg : 0 ≤ (S.diag.take k).foldl (· * ·) 1 :=
    Int.le_of_lt (h.prefix_pos k hk)
  have hnonneg' : 0 ≤ (S'.diag.take k).foldl (· * ·) 1 :=
    Int.le_of_lt (h'.prefix_pos k (by omega))
  calc
    (S.diag.take k).foldl (· * ·) 1 =
        (((S.diag.take k).foldl (· * ·) 1).natAbs : Int) :=
      (Int.ofNat_natAbs_of_nonneg hnonneg).symm
    _ = (((S'.diag.take k).foldl (· * ·) 1).natAbs : Int) :=
      congrArg Int.ofNat habs
    _ = (S'.diag.take k).foldl (· * ·) 1 :=
      Int.ofNat_natAbs_of_nonneg hnonneg'

private theorem foldl_take_succ (d : Vector Int r) (i : Nat) (hi : i < r) :
    (d.take (i + 1)).foldl (· * ·) 1 =
      (d.take i).foldl (· * ·) 1 * d[i] := by
  rw [foldl_take_eq_finFoldl d (i + 1) (by omega), Fin.foldl_succ_last]
  have hfun :
      (fun acc (j : Fin i) => acc * d[(⟨j.castSucc.val, by omega⟩ : Fin r)]) =
        (fun acc (j : Fin i) => acc * d[(⟨j.val, by omega⟩ : Fin r)]) := by
    funext acc j
    rfl
  rw [hfun, ← foldl_take_eq_finFoldl d i (by omega)]
  rfl

/-- Any two Smith witnesses have the same invariant factor at every valid
index. The two bounds are kept explicit so callers do not need to transport
dependent `Fin` values across `rank_eq`. -/
theorem IsSNF.diag_eq {A : Matrix Int n m} {S S' : SmithData n m}
    (h : IsSNF A S) (h' : IsSNF A S') (i : Nat)
    (hi : i < S.rank) (hi' : i < S'.rank) : S.diag[i] = S'.diag[i] := by
  have hrank := h.rank_eq h'
  have hprefix := h.prefix_eq h' hrank i (by omega)
  have hnext := h.prefix_eq h' hrank (i + 1) (by omega)
  rw [foldl_take_succ S.diag i hi, foldl_take_succ S'.diag i hi'] at hnext
  rw [hprefix] at hnext
  have hnonzero : (S'.diag.take i).foldl (· * ·) 1 ≠ 0 :=
    Int.ne_of_gt (h'.prefix_pos i (by omega))
  have hcancel := congrArg
    (fun z : Int => z / (S'.diag.take i).foldl (· * ·) 1) hnext
  rw [Int.mul_ediv_cancel_left _ hnonzero,
    Int.mul_ediv_cancel_left _ hnonzero] at hcancel
  exact hcancel

/-- The canonical diagonal matrix is independent of the Smith witness. -/
theorem IsSNF.form_eq {A : Matrix Int n m} {S S' : SmithData n m}
    (h : IsSNF A S) (h' : IsSNF A S') :
    diagMatrix S.diag n m = diagMatrix S'.diag n m := by
  have hrank := h.rank_eq h'
  apply Matrix.ext_getElem
  intro i j
  rw [getElem_diagMatrix, getElem_diagMatrix]
  split
  next hentry =>
    split
    next hentry' =>
      exact h.diag_eq h' i.val hentry.2 hentry'.2
    next hentry' => exact False.elim (hentry' ⟨hentry.1, by omega⟩)
  next hentry =>
    split
    next hentry' => exact False.elim (hentry ⟨hentry'.1, by omega⟩)
    next _ => rfl

/-- The fixed diagonal path agrees with the general Smith form. -/
theorem snfDiagonal_eq_snf {r : Nat} (d : Vector Int r) :
    snfDiagonal d = snf (diagMatrix d r r) := by
  rw [snfDiagonal_eq_data, snf_eq_data]
  exact (snfDiagonalData_isSNF d).form_eq
    (snfData_isSNF (diagMatrix d r r))

private def identitySmithData (S : SmithData n m) : SmithData n m where
  rank := S.rank
  diag := S.diag
  left := Matrix.identity n
  leftInv := Matrix.identity n
  right := Matrix.identity m
  rightInv := Matrix.identity m

private theorem IsSNF.diagonal {A : Matrix Int n m} {S : SmithData n m}
    (h : IsSNF A S) :
    IsSNF (diagMatrix S.diag n m) (identitySmithData S) := by
  refine
    { left_inv := Matrix.identity_mul _
      right_inv := Matrix.identity_mul _
      mul_eq := ?_
      rank_le_n := h.rank_le_n
      rank_le_m := h.rank_le_m
      diag_pos := h.diag_pos
      chain := h.chain }
  simp only [identitySmithData, Matrix.identity_mul, Matrix.mul_identity]

/-- Applying Smith normal form twice does not change the result. -/
theorem snf_idem (A : Matrix Int n m) : snf (snf A) = snf A := by
  let S := snfData A
  have hS : IsSNF A S := snfData_isSNF A
  have hdiag : IsSNF (diagMatrix S.diag n m) (identitySmithData S) := hS.diagonal
  have hrun := snfData_isSNF (diagMatrix S.diag n m)
  calc
    snf (snf A) = snf (diagMatrix S.diag n m) := by rw [snf_eq_data A]
    _ = diagMatrix (snfData (diagMatrix S.diag n m)).diag n m :=
      snf_eq_data (diagMatrix S.diag n m)
    _ = diagMatrix (identitySmithData S).diag n m := hrun.form_eq hdiag
    _ = snf A := by simp only [identitySmithData, S]; exact (snf_eq_data A).symm

end Hex.Matrix
