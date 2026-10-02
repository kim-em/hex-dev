/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Scratch

public section

namespace Hex.GraphIso.Nauty.Sparse.Join

/-- Count qualifying cells that have already occurred in a neighbour scan. -/
@[expose] def marked (keys seen : List Nat) (p : Nat → Bool) : Nat :=
  keys.countP fun k => decide (k ∈ seen) && p k

theorem marked_congr {keys seen seen' : List Nat} {p : Nat → Bool}
    (h : ∀ k ∈ keys, k ∈ seen ↔ k ∈ seen') : marked keys seen p = marked keys seen' p := by
  apply List.countP_congr
  intro k hk
  simp only [Bool.and_eq_true, decide_eq_true_eq, h k hk]

theorem marked_absent {keys seen : List Nat} {k : Nat} {p : Nat → Bool}
    (h : k ∉ keys) : marked keys (seen ++ [k]) p = marked keys seen p := by
  apply marked_congr
  intro j hj
  simp only [List.mem_append, List.mem_singleton]
  have hn : j ≠ k := by intro he; subst j; exact h hj
  simp [hn]

/-- Clearing a cell after its first occurrence counts it exactly once. -/
theorem marked_add {keys seen : List Nat} {k : Nat} {p : Nat → Bool}
    (hn : keys.Nodup) (hk : k ∈ keys) :
    marked keys (seen ++ [k]) p = marked keys seen p +
      (if k ∈ seen then 0 else if p k then 1 else 0) := by
  induction keys with
  | nil => simp at hk
  | cons a keys ih =>
    simp only [List.nodup_cons] at hn
    by_cases he : a = k
    · subst a
      have ht := marked_absent (seen := seen) (p := p) hn.1
      simp only [marked, List.countP_cons] at ht ⊢
      rw [ht]
      by_cases hm : k ∈ seen <;> cases p k <;> simp [hm, Nat.add_comm]
    · have ht := ih hn.2 (by simpa [Ne.symm he] using hk)
      simp only [marked, List.countP_cons] at ht ⊢
      rw [ht]
      have hm : (a ∈ seen ++ [k]) ↔ a ∈ seen := by simp [he]
      simp only [hm]
      omega

/-- Hit counts after the first edge pass, on the keys the pass can touch. -/
structure Counts (keys : List Nat) (seen : List Nat) (hits : Array Nat) : Prop where
  bound : ∀ k ∈ keys, k < hits.size
  get : ∀ k ∈ keys, hits[k]! = seen.count k

namespace Counts

theorem initial {keys : List Nat} {hits : Array Nat}
    (hb : ∀ k ∈ keys, k < hits.size) (hz : ∀ k ∈ keys, hits[k]! = 0) :
    Counts keys [] hits := ⟨hb, by simpa using hz⟩

theorem add {keys seen : List Nat} {hits : Array Nat} {k : Nat}
    (h : Counts keys seen hits) (hk : k ∈ keys) :
    Counts keys (seen ++ [k]) (hits.set! k (hits[k]! + 1)) := by
  refine ⟨by simpa using h.bound, ?_⟩
  intro j hj
  by_cases he : k = j
  · subst j
    rw [Array.getElem!_set!_self _ _ _ (h.bound k hk), h.get k hk]
    simp
  · rw [Array.getElem!_set!_ne _ _ _ _ he, h.get j hj]
    simp [he]

theorem skip {keys seen : List Nat} {hits : Array Nat} {k : Nat}
    (h : Counts keys seen hits) (hk : k ∉ keys) : Counts keys (seen ++ [k]) hits := by
  refine ⟨h.bound, ?_⟩
  intro j hj
  rw [h.get j hj]
  have he : j ≠ k := by intro he; subst j; exact hk hj
  simp [Ne.symm he]

end Counts

end Hex.GraphIso.Nauty.Sparse.Join
