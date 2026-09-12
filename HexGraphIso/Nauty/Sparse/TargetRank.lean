/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetCache

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- The next nontrivial cell follows exactly the already enumerated starts. -/
theorem Scan.next {n level used first : Nat} {ptn : Array Nat} {out : List Nat}
    (h : Scan n ptn level used first out) (hu : used < n) (hf : first < n)
    (ht : first < cellEnd ptn level first) :
    ∃ rest, nontrivial (cells ptn level n) = out ++ first :: rest := by
  obtain ⟨seen, heq, hout⟩ := h.remaining
  rw [show n - used = n - (used + 1) + 1 by omega, cells.go, ite_eq_left hf] at heq
  refine ⟨nontrivial (cells.go ptn level n (n - (used + 1)) (cellEnd ptn level first + 1)), ?_⟩
  rw [heq, nontrivial_append, hout]
  simp [nontrivial, ht]

/-- A newly enumerated cell's compact index is its rank in the complete list. -/
theorem Scan.rank {n level used first : Nat} {ptn : Array Nat} {out : List Nat}
    (h : Scan n ptn level used first out) (hu : used < n) (hf : first < n)
    (ht : first < cellEnd ptn level first) :
    (nontrivial (cells ptn level n)).idxOf first = out.length := by
  obtain ⟨rest, he⟩ := h.next hu hf ht
  have hn : first ∉ out := fun hm => Nat.lt_irrefl first (h.before first hm)
  rw [he, List.idxOf_append, ite_eq_right hn, List.idxOf_cons_self, Nat.zero_add]

/-- Compact cell indices fit in the same `n`-entry allocation as vertex indices. -/
theorem length_le {ptn : Array Nat} {n level : Nat}
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level) :
    (nontrivial (cells ptn level n)).length ≤ n := by
  have h := (nodup ptn level n).length_le_of_subset (l₂ := List.range n)
    (fun k hk => List.mem_range.mpr (bound hs hend hk))
  simpa using h

/-- Index lookup recovers each listed key, also when other entries repeat. -/
theorem get_rank {keys : List Nat} {k : Nat} (h : k ∈ keys) : keys[keys.idxOf k]! = k := by
  induction keys with
  | nil => simp at h
  | cons a keys ih =>
    by_cases he : a = k
    · subst a
      simp
    · have hk : k ∈ keys := by simpa [Ne.symm he] using h
      simpa [List.idxOf_cons, he] using ih hk

/-- Ranks distinguish listed cell starts. -/
theorem rank_inj {keys : List Nat} {a b : Nat} (ha : a ∈ keys) (hb : b ∈ keys)
    (he : keys.idxOf a = keys.idxOf b) : a = b := by
  have h := congrArg (fun i => keys[i]!) he
  simpa only [get_rank ha, get_rank hb] using h

theorem rank_get {keys : List Nat} (hn : keys.Nodup) {i : Nat} (hi : i < keys.length) :
    keys.idxOf keys[i]! = i := by
  have hm : keys[i]! ∈ keys := by rw [getElem!_pos _ i hi]; exact List.getElem_mem hi
  have hr := List.idxOf_lt_length_of_mem hm
  exact (List.Nodup.getElem!_inj hr hi hn).mp (get_rank hm)

end Hex.GraphIso.Nauty.Sparse.Target
