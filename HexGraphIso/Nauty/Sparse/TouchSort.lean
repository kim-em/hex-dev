/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Touched
public import HexGraphIso.Nauty.Sparse.Cells

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Touched-cell sorting retains all recorded cells and their multiplicities. -/
theorem sortCells_perm (xs : Array Nat) : (sortCells xs).toList.Perm xs.toList := by
  simpa only [sortCells, Hex.List.sort_eq, List.toList_toArray] using
    List.mergeSort_perm xs.toList (fun a b => a ≤ b)

/-- The executed tiny-sort specialization shares this ascending order contract. -/
theorem sortCells_order (xs : Array Nat) : (sortCells xs).toList.Pairwise (· ≤ ·) := by
  simpa only [sortCells, Hex.List.sort_eq, List.toList_toArray, decide_eq_true_eq] using
    List.pairwise_mergeSort (le := fun a b : Nat => a ≤ b)
      (by intro a b c; simp only [decide_eq_true_eq]; exact Nat.le_trans)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) xs.toList

/-- Sorting preserves first-touch coverage and uniqueness. -/
theorem Touched.sorted (h : Touched n stamp before marks touched seen) :
    Touched n stamp before marks (sortCells touched) seen := by
  have hp := sortCells_perm touched
  exact ⟨h.initial, h.writes, hp.nodup_iff.mpr h.nodup,
    fun k => hp.mem_iff.trans (h.members k)⟩

end Hex.GraphIso.Nauty.Sparse
