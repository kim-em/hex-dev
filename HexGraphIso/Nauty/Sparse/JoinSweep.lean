/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.JoinCount

public section

namespace Hex.GraphIso.Nauty.Sparse.Join

/-- A join meets a cell but does not meet all of its vertices. -/
@[expose] def qualifies (full : List Nat) (size : Nat → Nat) (k : Nat) : Bool :=
  decide (0 < full.count k ∧ full.count k < size k)

/-- The second neighbour scan clears each cell after its first occurrence
and accumulates one contribution per qualifying cell. -/
structure Sweep (keys full done : List Nat) (size : Nat → Nat)
    (hits : Array Nat) (count : Nat) : Prop where
  bound : ∀ k ∈ keys, k < hits.size
  get : ∀ k ∈ keys, hits[k]! = if k ∈ done then 0 else full.count k
  total : count = marked keys done (qualifies full size)

namespace Sweep

theorem initial {keys full : List Nat} {hits : Array Nat} (size : Nat → Nat)
    (h : Counts keys full hits) : Sweep keys full [] size hits 0 :=
  ⟨h.bound, by simpa using h.get, by simp [marked]⟩

/-- The actual test-and-clear operation counts only the first occurrence,
including when a cell occurs several times in the adjacency row. -/
theorem clear {keys full done : List Nat} {size : Nat → Nat}
    {hits : Array Nat} {count k : Nat} (h : Sweep keys full done size hits count)
    (hn : keys.Nodup) (hk : k ∈ keys) (hf : k ∈ full) :
    Sweep keys full (done ++ [k]) size (hits.set! k 0)
      (count + if 0 < hits[k]! ∧ hits[k]! < size k then 1 else 0) := by
  refine ⟨by simpa using h.bound, ?_, ?_⟩
  · intro j hj
    by_cases he : k = j
    · subst j
      rw [Array.getElem!_set!_self _ _ _ (h.bound k hk)]
      simp
    · rw [Array.getElem!_set!_ne _ _ _ _ he, h.get j hj]
      simp only [List.mem_append, List.mem_singleton, Ne.symm he, or_false]
  · rw [h.total, marked_add hn hk, h.get k hk]
    have hp : 0 < full.count k := List.count_pos_iff.mpr hf
    by_cases hm : k ∈ done
    · simp [hm]
    · simp [hm, qualifies, hp]

theorem skip {keys full done : List Nat} {size : Nat → Nat}
    {hits : Array Nat} {count k : Nat} (h : Sweep keys full done size hits count)
    (hk : k ∉ keys) : Sweep keys full (done ++ [k]) size hits count := by
  refine ⟨h.bound, ?_, ?_⟩
  · intro j hj
    have hn : j ≠ k := by intro he; subst j; exact hk hj
    rw [h.get j hj]
    simp only [List.mem_append, List.mem_singleton, hn, or_false]
  · rw [marked_absent hk]
    exact h.total

/-- At completion the result is the number of nontrivial joins, and all
used count entries are zero for the next representative vertex. -/
theorem finish {keys full : List Nat} {size : Nat → Nat}
    {hits : Array Nat} {count : Nat} (h : Sweep keys full full size hits count) :
    count = keys.countP (qualifies full size) ∧ ∀ k ∈ keys, hits[k]! = 0 := by
  refine ⟨?_, ?_⟩
  · rw [h.total]
    apply List.countP_congr
    intro k hk
    simp [qualifies, List.count_pos_iff]
  · intro k hk
    rw [h.get k hk]
    by_cases hm : k ∈ full
    · simp [hm]
    · simp [hm, List.count_eq_zero_of_not_mem hm]

end Sweep

end Hex.GraphIso.Nauty.Sparse.Join
