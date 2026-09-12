/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Index

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- Vertex-index writes assign one value precisely to the vertices traversed.
Repeated occurrences are harmless because the assigned value is fixed. -/
structure Writes (n : Nat) (before after : Array Nat) (vertices : List Nat) (value : Nat) : Prop where
  size : after.size = n
  get : ∀ v, v < n → after[v]! = if v ∈ vertices then value else before[v]!

namespace Writes

theorem initial (h : before.size = n) : Writes n before before [] value :=
  ⟨h, fun _ _ => by simp⟩

theorem step (h : Writes n before after vertices value) (hv : v < n) :
    Writes n before (after.setIfInBounds v value) (vertices ++ [v]) value := by
  refine ⟨by simpa using h.size, ?_⟩
  intro j hj
  by_cases he : v = j
  · subst j
    rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hv)]
    simp
  · rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_ne _ _ _ _ he, h.get j hj]
    simp only [List.mem_append, List.mem_singleton, Ne.symm he, or_false]

/-- An out-of-range sentinel adds no writable vertex. -/
theorem skip (h : Writes n before after vertices value) (hv : n ≤ v) :
    Writes n before after (vertices ++ [v]) value := by
  refine ⟨h.size, ?_⟩
  intro j hj
  rw [h.get j hj]
  simp only [List.mem_append, List.mem_singleton, show j ≠ v by omega, or_false]

/-- Repeating a vertex already written does not change the scatter. -/
theorem repeated (h : Writes n before after vertices value) (hv : v ∈ vertices) :
    Writes n before after (vertices ++ [v]) value := by
  refine ⟨h.size, ?_⟩
  intro j hj
  rw [h.get j hj]
  by_cases he : j = v
  · simp [he, hv]
  · simp [he]

end Writes

end Hex.GraphIso.Nauty.Sparse.Index
