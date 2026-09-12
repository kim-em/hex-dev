/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexProps

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- Nontrivial cell starts, in the partition's order. -/
@[expose] def nontrivial (cs : List (Nat × Nat)) : List Nat :=
  (cs.filter fun p => p.1 < p.2).map Prod.fst

@[simp] theorem nontrivial_append (cs ds : List (Nat × Nat)) :
    nontrivial (cs ++ ds) = nontrivial cs ++ nontrivial ds := by
  simp [nontrivial]

/-- Cursor invariant for the executed cell enumeration. The remaining
recursive cell list is tied to the loop's actual remaining iteration count. -/
structure Scan (n : Nat) (ptn : Array Nat) (level used first : Nat) (out : List Nat) : Prop where
  used_le : used ≤ first
  first_le : first ≤ n
  boundary : first = 0 ∨ ptn[first - 1]! ≤ level
  before : ∀ a ∈ out, a < first
  remaining : ∃ seen, cells ptn level n = seen ++ cells.go ptn level n (n - used) first ∧
    out = nontrivial seen

namespace Scan

theorem initial (n : Nat) (ptn : Array Nat) (level : Nat) : Scan n ptn level 0 0 [] :=
  ⟨Nat.le_refl _, Nat.zero_le _, Or.inl rfl, by simp, ⟨[], by simp [cells], rfl⟩⟩

theorem step {n level used first : Nat} {ptn : Array Nat} {out : List Nat}
    (h : Scan n ptn level used first out) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hu : used < n) (hf : first < n) :
    Scan n ptn level (used + 1) (cellEnd ptn level first + 1)
      (if first < cellEnd ptn level first then out ++ [first] else out) := by
  have hg : first ≤ cellEnd ptn level first := cellEnd_ge
  have hb : cellEnd ptn level first < n := by
    simpa [hs] using cellEnd_lt (ptn := ptn) (level := level) (i := first)
      (by omega) (by simpa [hs] using hend)
  have hc := isCell_cellEnd (ptn := ptn) (level := level) (a := first)
    (by omega) h.boundary (by simpa [hs] using hend)
  refine ⟨by have := h.used_le; omega, by omega, Or.inr ?_, ?_, ?_⟩
  · have he : first + (cellEnd ptn level first + 1 - first) - 1 =
        cellEnd ptn level first := by omega
    simpa only [Nat.add_sub_cancel, he] using hc.2.2.2
  · intro a ha
    split at ha
    · rcases List.mem_append.mp ha with ha | ha
      · have := h.before a ha; omega
      · simp only [List.mem_singleton] at ha; omega
    · have := h.before a ha; omega
  · obtain ⟨seen, heq, hout⟩ := h.remaining
    refine ⟨seen ++ [(first, cellEnd ptn level first)], ?_, ?_⟩
    · rw [show n - used = n - (used + 1) + 1 by omega, cells.go, ite_eq_left hf] at heq
      simpa only [List.append_assoc, List.singleton_append] using heq
    · rw [nontrivial_append, hout]
      simp only [nontrivial, List.filter_cons, List.filter_nil]
      split <;> simp_all

theorem finish {n level used first : Nat} {ptn : Array Nat} {out : List Nat}
    (h : Scan n ptn level used first out) (he : used = n ∨ first = n) :
    out = nontrivial (cells ptn level n) := by
  obtain ⟨seen, hcs, hout⟩ := h.remaining
  have ht : cells.go ptn level n (n - used) first = [] := by
    rcases he with he | he
    · rw [he, Nat.sub_self, cells.go]
    · rw [he]
      cases n - used with
      | zero => rfl
      | succ fuel => simp [cells.go]
  rw [ht, List.append_nil] at hcs
  rwa [hcs]

end Scan

end Hex.GraphIso.Nauty.Sparse.Target
