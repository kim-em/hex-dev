/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Minima
public import HexGraphIso.Nauty.Sparse.SortSorted

public section

namespace Hex.GraphIso.Nauty.Sparse.Minima

theorem constant_sorted {lab hits : Array Nat} {first upto value : Nat}
    (hc : ∀ q, first ≤ q → q < upto → hits[lab[q]!]! = value) :
    Sort.Sorted lab hits first (upto - first) := by
  intro i j hij hj
  rw [hc (first + i) (by omega) (by omega), hc (first + j) (by omega) (by omega)]
  exact Nat.le_refl _

theorem before_le {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) (hq : first ≤ q) (hqt : q < v3) :
    hits[lab[q]!]! ≤ w2 := by
  by_cases hqv : q < v2
  · rw [h.minimum q hq hqv]; exact Nat.le_of_lt h.keys
  · rw [h.second q (by omega) hqt]
    exact Nat.le_refl _

theorem before_sorted {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) :
    Sort.Sorted lab hits first (v3 - first) := by
  intro i j hij hj
  have hb := h.bounds
  by_cases hjv : first + j < v2
  · rw [h.minimum (first + i) (by omega) (by omega), h.minimum (first + j) (by omega) hjv]
    exact Nat.le_refl _
  · rw [h.second (first + j) (by omega) (by omega)]
    exact h.before_le (q := first + i) (by omega) (by omega)

theorem done_sorted {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) (he : upto = v2 ∨ upto = v3) :
    Sort.Sorted lab hits first (upto - first) := by
  have hb := h.bounds
  have hv : v3 = upto := by omega
  simpa only [hv] using h.before_sorted

/-- Sorting the larger-count tail completes the ordering of the whole cell.
The proof uses the exact sort's executed permutation, exterior, and ordering
contracts; tied labels may be rearranged. -/
theorem sort_tail {lab hits : Array Nat} {first v2 v3 upto w1 w2 : Nat}
    (h : Minima lab hits first v2 v3 upto w1 w2) (hb : upto ≤ lab.size) :
    Sort.Sorted (Sort.indirect lab hits v3 (upto - v3)) hits first (upto - first) := by
  have bounds := h.bounds
  have he : v3 + (upto - v3) = upto := by omega
  have size := Sort.indirect_size lab hits v3 (upto - v3)
  have outside (q : Nat) (hq : q < v3) :
      (Sort.indirect lab hits v3 (upto - v3))[q]! = lab[q]! :=
    Sort.indirect_outside lab hits v3 (upto - v3) q (by omega) (Or.inl hq)
  have tail := Sort.indirect_sorted lab hits v3 (upto - v3) (by omega)
  have perm := Sort.indirect_segment lab hits v3 (upto - v3) (by omega)
  rw [he] at perm
  have larger (q : Nat) (hql : v3 ≤ q) (hqu : q < upto) :
      w2 < hits[(Sort.indirect lab hits v3 (upto - v3))[q]!]! := by
    obtain ⟨r, hrl, hru, hr⟩ := Sort.segment_mem (by omega) perm ⟨hql, hqu⟩
    rw [hr]
    exact h.larger r hrl hru
  intro i j hij hj
  by_cases hji : first + j < v3
  · rw [outside _ (by omega), outside _ hji]
    exact h.before_sorted i j hij (by omega)
  · by_cases hii : first + i < v3
    · rw [outside _ hii]
      have hle := h.before_le (q := first + i) (by omega) hii
      have hlt := larger (first + j) (by omega) (by omega)
      omega
    · have ht := tail (first + i - v3) (first + j - v3) (by omega) (by omega)
      simpa only [show v3 + (first + i - v3) = first + i by omega,
        show v3 + (first + j - v3) = first + j by omega] using ht

end Hex.GraphIso.Nauty.Sparse.Minima
