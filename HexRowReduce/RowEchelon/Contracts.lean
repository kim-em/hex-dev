/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRowReduce.RowEchelon.Elementary
import all HexRowReduce.RowEchelon.Elementary

public section

/-!
Echelon-form data and contracts.

`RowEchelonData` is the pure result of an echelon-form algorithm (rank, echelon
matrix, accumulated transform, pivot columns). `IsEchelonForm` is the shared
contract for any echelon form; `IsRowReduced` extends it with the
reduced-row-echelon conditions (pivots are one, entries above pivots vanish).
The `IsEchelonForm` namespace lemmas develop the pivot/free-column partition
used by the span and nullspace APIs.
-/

namespace Hex

universe u

namespace Matrix

/-- Pure data produced by an echelon-form algorithm. -/
structure RowEchelonData (R : Type u) (n m : Nat) where
  /-- Number of pivots, i.e. the rank of the original matrix. -/
  rank : Nat
  /-- The matrix reduced to row-echelon form. -/
  echelon : Matrix R n m
  /-- The accumulated row-operation transform `T` with `T * original = echelon`. -/
  transform : Matrix R n n
  /-- Column index of each pivot, in increasing order. -/
  pivotCols : Vector (Fin m) rank

/-- Shared conditions for any echelon form. -/
structure IsEchelonForm [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (M : Matrix R n m) (D : RowEchelonData R n m) : Prop where
  transform_mul : D.transform * M = D.echelon
  transform_inv : ∃ Tinv : Matrix R n n, Tinv * D.transform = (Matrix.identity (R := R) n)
  transform_right_inv : ∃ Tinv : Matrix R n n, D.transform * Tinv = (Matrix.identity (R := R) n)
  rank_le_n : D.rank ≤ n
  rank_le_m : D.rank ≤ m
  pivotCols_sorted : ∀ i j, i < j → D.pivotCols.get i < D.pivotCols.get j
  below_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      i.val < j.val → D.echelon[j][D.pivotCols.get i] = 0
  zero_row : ∀ (i : Fin n), D.rank ≤ i.val → D.echelon[i] = 0

/-- RREF-specific conditions on top of `IsEchelonForm`. -/
structure IsRowReduced [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
    (M : Matrix R n m) (D : RowEchelonData R n m)
    : Prop extends IsEchelonForm M D where
  pivot_one : ∀ (i : Fin D.rank), D.echelon[i][D.pivotCols.get i] = 1
  above_pivot_zero : ∀ (i : Fin D.rank) (j : Fin n),
      j.val < i.val → D.echelon[j][D.pivotCols.get i] = 0

namespace IsEchelonForm

variable [Mul R] [Add R] [OfNat R 0] [OfNat R 1]
variable {M : Matrix R n m} {D : RowEchelonData R n m}

/-- View a pivot-row index as a row index of the ambient matrix. -/
@[expose]
def pivotRow (E : IsEchelonForm M D) (i : Fin D.rank) : Fin n :=
  ⟨i.val, Nat.lt_of_lt_of_le i.isLt E.rank_le_n⟩

/-- The pivot entries named by `pivotCols` are nonzero. This is the extra
proof-facing contract needed by span solving: without it, the pivot-column
division in `spanCoeffs` can divide by zero. -/
@[expose]
def HasNonzeroPivots (E : IsEchelonForm M D) : Prop :=
  ∀ i : Fin D.rank, D.echelon[E.pivotRow i][D.pivotCols.get i] ≠ 0

/-- The square row-transform has a right inverse. -/
theorem transform_mul_inv (E : IsEchelonForm M D) :
    ∃ Tinv : Matrix R n n, D.transform * Tinv = (Matrix.identity (R := R) n) := by
  exact E.transform_right_inv

private theorem pivotCols_pairwise (E : IsEchelonForm M D) :
    List.Pairwise (fun a b : Fin m => a < b) D.pivotCols.toList := by
  rw [List.pairwise_iff_getElem]
  intro i j hi hj hij
  have hi' : i < D.rank := by simpa [Vector.length_toList] using hi
  have hj' : j < D.rank := by simpa [Vector.length_toList] using hj
  have h := E.pivotCols_sorted ⟨i, hi'⟩ ⟨j, hj'⟩ hij
  exact h

private theorem pivotCols_nodup (E : IsEchelonForm M D) :
    D.pivotCols.toList.Nodup := by
  rw [List.nodup_iff_pairwise_ne]
  exact E.pivotCols_pairwise.imp (fun hlt heq => by subst heq; omega)

/-- The pivot columns are injective because they are strictly increasing. -/
theorem pivotCols_injective (E : IsEchelonForm M D) :
    Function.Injective fun i : Fin D.rank => D.pivotCols.get i := by
  intro i j h
  by_cases hne : i = j
  · exact hne
  have hval : i.val ≠ j.val := by
    intro hval
    exact hne (Fin.ext hval)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hp := E.pivotCols_sorted i j hij
      have h' : D.pivotCols.get i = D.pivotCols.get j := h
      rw [h'] at hp
      exact False.elim (by omega)
  | inr hji =>
      have hp := E.pivotCols_sorted j i hji
      have h' : D.pivotCols.get i = D.pivotCols.get j := h
      rw [h'] at hp
      exact False.elim (by omega)

/-- The non-pivot columns, enumerated in increasing order.

The echelon-form witness `_E` is a phantom argument: it carries no runtime
data but enables dot-notation (`E.freeColsList`) and fixes the implicit
matrix/data parameters. This intentionally triggers the `unusedArguments`
linter; the binder is kept deliberately (no `@[nolint]` exists in the
Mathlib-free layer). -/
@[expose]
def freeColsList (_E : IsEchelonForm M D) : List (Fin m) :=
  (List.finRange m).filter fun j => j ∉ D.pivotCols.toList

/-- Linear merge used by the compiled implementation of `freeColsList`.

The second list is a sorted sublist of the first.  Matching heads are
discarded; otherwise the first head belongs to the complement.  Both recursive
calls consume a column, and a matching call also consumes a pivot, so the loop
is linear in the two input lengths. -/
@[expose]
def sortedComplement [DecidableEq α] : List α → List α → List α
  | xs, [] => xs
  | [], _ => []
  | x :: xs, y :: ys =>
      if x = y then
        sortedComplement xs ys
      else
        x :: sortedComplement xs (y :: ys)

private theorem sortedComplement_eq_filter [DecidableEq α]
    {pivots cols : List α} (hsub : pivots.Sublist cols) (hnodup : cols.Nodup) :
    sortedComplement cols pivots = cols.filter fun x => x ∉ pivots := by
  induction hsub with
  | slnil => simp [sortedComplement]
  | @cons pivots cols x hsub ih =>
      have hnot : x ∉ pivots := by
        intro hx
        exact (List.nodup_cons.mp hnodup).1 (hsub.subset hx)
      cases pivots with
      | nil =>
          rw [sortedComplement]
          symm
          apply List.filter_eq_self.mpr
          intro z hz
          simp
      | cons y ys =>
          have hxy : x ≠ y := by
            intro h
            subst y
            exact hnot (by simp)
          rw [sortedComplement, if_neg hxy]
          rw [ih (List.nodup_cons.mp hnodup).2]
          rw [List.filter_cons]
          have hp : (decide (x ∉ y :: ys) : Bool) = true := decide_eq_true hnot
          rw [hp]
          simp
  | @cons_cons pivots cols x hsub ih =>
      rw [sortedComplement, if_pos rfl, List.filter_cons_of_neg (by simp)]
      rw [ih (List.nodup_cons.mp hnodup).2]
      apply List.filter_congr
      intro z hz
      have hzx : z ≠ x := by
        intro h
        subst z
        exact (List.nodup_cons.mp hnodup).1 hz
      simp [hzx]

private theorem pairwise_perm_eq {xs ys : List (Fin m)}
    (hxs : List.Pairwise (fun a b : Fin m => a < b) xs)
    (hys : List.Pairwise (fun a b : Fin m => a < b) ys)
    (hperm : xs.Perm ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => exact hperm.symm.eq_nil.symm
  | cons x xs ih =>
      cases ys with
      | nil =>
          have hlen := hperm.length_eq
          simp at hlen
      | cons y ys =>
          have hxmem : x ∈ y :: ys := hperm.subset (by simp)
          have hymem : y ∈ x :: xs := hperm.symm.subset (by simp)
          have hxy : x = y := by
            rcases List.mem_cons.mp hxmem with h | hx
            · exact h
            · rcases List.mem_cons.mp hymem with h | hy
              · exact h.symm
              · have hyx : y < x := (List.pairwise_cons.mp hys).1 x hx
                have hxy : x < y := (List.pairwise_cons.mp hxs).1 y hy
                omega
          subst y
          simp only [List.cons.injEq, true_and]
          exact ih (List.pairwise_cons.mp hxs).2 (List.pairwise_cons.mp hys).2
            hperm.cons_inv

/-- Runtime implementation of `freeColsList`, merging the sorted pivot columns
with the complete sorted column range. -/
@[expose]
def freeColsListImpl (_E : IsEchelonForm M D) : List (Fin m) :=
  sortedComplement (List.finRange m) D.pivotCols.toList

private theorem pivotCols_sublist_finRange (E : IsEchelonForm M D) :
    D.pivotCols.toList.Sublist (List.finRange m) := by
  let p : Fin m → Bool := fun j => decide (j ∈ D.pivotCols.toList)
  have hfilterPairs : List.Pairwise (fun a b : Fin m => a < b)
      ((List.finRange m).filter p) := by
    exact List.Pairwise.filter p (List.pairwise_lt_finRange m)
  have hfilterNodup : ((List.finRange m).filter p).Nodup := by
    rw [List.nodup_iff_pairwise_ne]
    exact hfilterPairs.imp (fun hlt heq => by subst heq; omega)
  have hperm : D.pivotCols.toList.Perm ((List.finRange m).filter p) := by
    rw [List.perm_ext_iff_of_nodup E.pivotCols_nodup hfilterNodup]
    intro a
    constructor
    · intro ha
      rw [List.mem_filter]
      exact ⟨List.mem_finRange a, show p a = true from by exact decide_eq_true ha⟩
    · intro ha
      rw [List.mem_filter] at ha
      exact of_decide_eq_true ha.2
  have heq : D.pivotCols.toList = (List.finRange m).filter p :=
    pairwise_perm_eq E.pivotCols_pairwise hfilterPairs hperm
  rw [heq]
  exact List.filter_sublist

/-- Register the linear merge as the compiled implementation of
`freeColsList`.  The proof keeps the specification and all theorem-facing
unfolding unchanged. -/
@[csimp]
theorem freeColsList_eq_impl : @freeColsList = @freeColsListImpl := by
  funext R n m _ _ _ _ M D E
  unfold freeColsList freeColsListImpl
  exact (sortedComplement_eq_filter (E.pivotCols_sublist_finRange)
    (List.nodup_finRange m)).symm

/-- The number of free columns is the ambient column count minus the rank. -/
theorem freeColsList_length (E : IsEchelonForm M D) :
    E.freeColsList.length = m - D.rank := by
  let p : Fin m → Bool := fun j => decide (j ∈ D.pivotCols.toList)
  have hpivotFilterLen : ((List.finRange m).filter p).length = D.rank := by
    have hfilterPairs : List.Pairwise (fun a b : Fin m => a < b)
        ((List.finRange m).filter p) := by
      exact List.Pairwise.filter p (List.pairwise_lt_finRange m)
    have hfilterNodup : ((List.finRange m).filter p).Nodup := by
      rw [List.nodup_iff_pairwise_ne]
      exact hfilterPairs.imp (fun hlt heq => by subst heq; omega)
    have hperm : D.pivotCols.toList.Perm ((List.finRange m).filter p) := by
      rw [List.perm_ext_iff_of_nodup E.pivotCols_nodup hfilterNodup]
      intro a
      constructor
      · intro ha
        rw [List.mem_filter]
        exact ⟨List.mem_finRange a, show p a = true from by exact decide_eq_true ha⟩
      · intro ha
        rw [List.mem_filter] at ha
        exact of_decide_eq_true ha.2
    have hlen := hperm.length_eq
    simpa [p, Vector.length_toList] using hlen.symm
  have hsum : ((List.finRange m).filter p).length + E.freeColsList.length = m := by
    have hlen := (List.filter_append_perm p (List.finRange m)).length_eq
    simpa [p, freeColsList, List.length_finRange] using hlen
  omega

/-- Sorted complement of the pivot columns. -/
@[expose]
def freeCols (E : IsEchelonForm M D) : Vector (Fin m) (m - D.rank) :=
  ⟨E.freeColsList.toArray, by simpa using E.freeColsList_length⟩

private theorem freeCols_get_eq (E : IsEchelonForm M D) (i : Fin (m - D.rank)) :
    E.freeCols.get i =
      E.freeColsList[i.val]'(by rw [freeColsList_length]; exact i.isLt) := by
  unfold freeCols
  simp [Vector.get, List.getElem_toArray]

private theorem freeColsList_pairwise (E : IsEchelonForm M D) :
    List.Pairwise (fun a b : Fin m => a < b) E.freeColsList := by
  unfold freeColsList
  exact List.Pairwise.filter (fun j => j ∉ D.pivotCols.toList) (List.pairwise_lt_finRange m)

/-- The free-column complement is strictly increasing. -/
theorem freeCols_sorted (E : IsEchelonForm M D) :
    ∀ i j, i < j → E.freeCols.get i < E.freeCols.get j := by
  intro i j hij
  have hpair := E.freeColsList_pairwise
  rw [List.pairwise_iff_getElem] at hpair
  have hi : i.val < E.freeColsList.length := by
    rw [freeColsList_length]
    exact i.isLt
  have hj : j.val < E.freeColsList.length := by
    rw [freeColsList_length]
    exact j.isLt
  simpa [E.freeCols_get_eq i, E.freeCols_get_eq j] using hpair i.val j.val hi hj hij

/-- The free columns are injective because they are strictly increasing. -/
theorem freeCols_injective (E : IsEchelonForm M D) :
    Function.Injective fun i : Fin (m - D.rank) => E.freeCols.get i := by
  intro i j h
  by_cases hne : i = j
  · exact hne
  have hval : i.val ≠ j.val := by
    intro hval
    exact hne (Fin.ext hval)
  cases Nat.lt_or_gt_of_ne hval with
  | inl hij =>
      have hp := E.freeCols_sorted i j hij
      have h' : E.freeCols.get i = E.freeCols.get j := h
      rw [h'] at hp
      exact False.elim (by omega)
  | inr hji =>
      have hp := E.freeCols_sorted j i hji
      have h' : E.freeCols.get i = E.freeCols.get j := h
      rw [h'] at hp
      exact False.elim (by omega)

/-- Every column is either a pivot column or a free column. -/
theorem colPartition (E : IsEchelonForm M D) (j : Fin m) :
    (∃ i : Fin D.rank, D.pivotCols.get i = j) ∨
    (∃ k : Fin (m - D.rank), E.freeCols.get k = j) := by
  by_cases hp : j ∈ D.pivotCols.toList
  · left
    rw [List.mem_iff_getElem] at hp
    rcases hp with ⟨i, hi, hget⟩
    have hi' : i < D.rank := by simpa [Vector.length_toList] using hi
    exact ⟨⟨i, hi'⟩, by simp only [Vector.getElem_toList] at hget; exact hget⟩
  · right
    have hfreeMem : j ∈ E.freeColsList := by
      unfold freeColsList
      rw [List.mem_filter]
      exact ⟨List.mem_finRange j, by simpa using decide_eq_true hp⟩
    rw [List.mem_iff_getElem] at hfreeMem
    rcases hfreeMem with ⟨k, hk, hget⟩
    have hk' : k < m - D.rank := by simpa [freeColsList_length] using hk
    refine ⟨⟨k, hk'⟩, ?_⟩
    simpa [E.freeCols_get_eq ⟨k, hk'⟩] using hget

/-- No column can simultaneously occur in the pivot list and the free-column
complement. -/
theorem colPartition_exclusive (E : IsEchelonForm M D) (j : Fin m) :
    ¬((∃ i : Fin D.rank, D.pivotCols.get i = j) ∧
      (∃ k : Fin (m - D.rank), E.freeCols.get k = j)) := by
  rintro ⟨⟨i, hpivot⟩, ⟨k, hfree⟩⟩
  have hpivotMem : j ∈ D.pivotCols.toList := by
    rw [List.mem_iff_getElem]
    refine ⟨i.val, by simp [Vector.length_toList], ?_⟩
    simpa [Vector.getElem_toList, hpivot]
  have hfreeMem : j ∈ E.freeColsList := by
    rw [List.mem_iff_getElem]
    refine ⟨k.val, by rw [freeColsList_length]; exact k.isLt, ?_⟩
    simpa [E.freeCols_get_eq k, hfree]
  unfold freeColsList at hfreeMem
  rw [List.mem_filter] at hfreeMem
  exact (of_decide_eq_true hfreeMem.2) hpivotMem

/-- No column can be both pivot and free. -/
theorem pivotCols_disjoint_freeCols (E : IsEchelonForm M D) :
    ∀ (i : Fin D.rank) (k : Fin (m - D.rank)),
      D.pivotCols.get i ≠ E.freeCols.get k := by
  intro i k h
  exact E.colPartition_exclusive (D.pivotCols.get i)
    ⟨⟨i, rfl⟩, ⟨k, h.symm⟩⟩

end IsEchelonForm

end Matrix
end Hex
