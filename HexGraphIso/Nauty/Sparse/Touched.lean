/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexWrites
public import HexGraphIso.Nauty.Sparse.Marks

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A generation-marked scan records each nonsentinel cell exactly once.
`seen` includes all observed keys, including the singleton sentinel. -/
structure Touched (n stamp : Nat) (before marks touched : Array Nat) (seen : List Nat) : Prop where
  initial : Scratch.Marks n stamp before
  writes : Index.Writes n before marks seen (stamp + 1)
  nodup : touched.toList.Nodup
  members : ∀ k, k ∈ touched.toList ↔ k < n ∧ k ∈ seen

namespace Touched

theorem empty (h : Scratch.Marks n stamp before) : Touched n stamp before before #[] [] :=
  ⟨h, Index.Writes.initial h.size, by simp, by simp⟩

/-- A current-generation mark is equivalent to prior occurrence in the scan. -/
theorem marked (h : Touched n stamp before marks touched seen) (hk : k < n) :
    marks[k]! = stamp + 1 ↔ k ∈ seen := by
  rw [h.writes.get k hk]
  by_cases hm : k ∈ seen
  · simp [hm]
  · have hh := h.initial.fresh hk
    simp [hm, hh]

theorem present (h : Touched n stamp before marks touched seen) (hk : k < n) :
    marks[k]! = stamp + 1 ↔ k ∈ touched.toList := by
  rw [h.members k, h.marked hk]
  simp [hk]

/-- Singleton cells are skipped without touching generation marks. -/
theorem sentinel (h : Touched n stamp before marks touched seen) :
    Touched n stamp before marks touched (seen ++ [n]) := by
  refine ⟨h.initial, h.writes.skip (Nat.le_refl _), h.nodup, ?_⟩
  intro k
  rw [h.members k]
  simp only [List.mem_append, List.mem_singleton]
  by_cases he : k = n <;> simp [he]

/-- Repeated neighbours of the same cell do not add duplicate work. -/
theorem repeated (h : Touched n stamp before marks touched seen)
    (hk : k < n) (hm : marks[k]! = stamp + 1) :
    Touched n stamp before marks touched (seen ++ [k]) := by
  have hs := (h.marked hk).mp hm
  refine ⟨h.initial, h.writes.repeated hs, h.nodup, ?_⟩
  intro j
  rw [h.members j]
  simp only [List.mem_append, List.mem_singleton]
  by_cases he : j = k
  · simp [he, hs]
  · simp [he]

/-- First touch marks the cell and appends it exactly once. -/
theorem fresh (h : Touched n stamp before marks touched seen)
    (hk : k < n) (hm : marks[k]! ≠ stamp + 1) :
    Touched n stamp before (marks.setIfInBounds k (stamp + 1)) (touched.push k) (seen ++ [k]) := by
  have hn : k ∉ touched.toList := by simpa only [← h.present hk] using hm
  refine ⟨h.initial, h.writes.step hk, ?_, ?_⟩
  · simp only [Array.toList_push, List.nodup_append, h.nodup,
      true_and]
    refine ⟨by simp, ?_⟩
    intro a ha b hb he
    have hb : b = k := by simpa using hb
    exact hn ((he.trans hb) ▸ ha)
  · intro j
    simp only [Array.toList_push, List.mem_append, List.mem_singleton, h.members]
    constructor
    · rintro (⟨hb, hs⟩ | rfl)
      · exact ⟨hb, Or.inl hs⟩
      · exact ⟨hk, Or.inr rfl⟩
    · rintro ⟨hb, hs | rfl⟩
      · exact Or.inl ⟨hb, hs⟩
      · exact Or.inr rfl

end Touched

end Hex.GraphIso.Nauty.Sparse
