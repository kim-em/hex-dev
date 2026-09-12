/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CellClear

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Counts are exact on every touched nontrivial cell. Untouched scratch
entries remain unrestricted; every observed nonsentinel vertex is covered. -/
structure Counts (n : Nat) (starts hits : Array Nat) (cells seen : List Nat) : Prop where
  size : hits.size = n
  covered : ∀ v ∈ seen, starts[v]! < n → starts[v]! ∈ cells
  get : ∀ v, v < n → starts[v]! < n → starts[v]! ∈ cells → hits[v]! = seen.count v

namespace Counts

variable {n k j : Nat} {starts hits cleared : Array Nat} {cells seen : List Nat}

theorem initial (hs : hits.size = n) : Counts n starts hits [] [] :=
  ⟨hs, by simp, by simp⟩

/-- Recording an already touched key leaves every count invariant intact. -/
theorem repeated (h : Counts n starts hits cells seen) (hk : k ∈ cells) :
    Counts n starts hits (cells ++ [k]) seen := by
  refine ⟨h.size, ?_, ?_⟩
  · intro v hv hb
    exact List.mem_append_left _ (h.covered v hv hb)
  · intro v hv hb hm
    have hm' : starts[v]! ∈ cells := by
      rcases List.mem_append.mp hm with hm | hm
      · exact hm
      · have he : starts[v]! = k := by simpa using hm
        simpa only [he] using hk
    exact h.get v hv hb hm'

/-- First-touch clearing initializes the new cell to its exact zero count;
previously touched cells retain all accumulated counts. -/
theorem reset (h : Counts n starts hits cells seen) (hk : k ∉ cells)
    (hs : cleared.size = n)
    (hc : ∀ v, v < n → cleared[v]! = if starts[v]! = k then 0 else hits[v]!) :
    Counts n starts cleared (cells ++ [k]) seen := by
  refine ⟨hs, ?_, ?_⟩
  · intro v hv hb
    exact List.mem_append_left _ (h.covered v hv hb)
  · intro v hv hb hm
    rw [hc v hv]
    by_cases he : starts[v]! = k
    · rw [ite_eq_left he]
      apply Eq.symm
      apply List.count_eq_zero.mpr
      intro hmem
      exact hk (he ▸ h.covered v hmem hb)
    · rw [ite_eq_right he]
      apply h.get v hv hb
      simpa only [List.mem_append, List.mem_singleton, he, or_false] using hm

/-- The actual count increment accounts for precisely one observed vertex. -/
theorem increment (h : Counts n starts hits cells seen) (hj : j < n)
    (hk : starts[j]! < n) (hm : starts[j]! ∈ cells) :
    Counts n starts (hits.setIfInBounds j (hits[j]! + 1)) cells (seen ++ [j]) := by
  refine ⟨by simpa using h.size, ?_, ?_⟩
  · intro v hv hb
    rcases List.mem_append.mp hv with hv | hv
    · exact h.covered v hv hb
    · have he : v = j := by simpa using hv
      simpa only [he] using hm
  · intro v hv hb hc
    by_cases he : j = v
    · subst v
      rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hj),
        h.get j hj hk hm]
      simp
    · rw [← Array.set!_eq_setIfInBounds, Array.getElem!_set!_ne _ _ _ _ he, h.get v hv hb hc]
      rw [List.count_append, List.count_eq_zero.mpr (show v ∉ [j] by simpa using Ne.symm he), Nat.add_zero]

/-- Singleton neighbours add no count work and cannot affect a nontrivial
cell's multiplicities. -/
theorem sentinel (h : Counts n starts hits cells seen) (hj : starts[j]! = n) :
    Counts n starts hits (cells ++ [n]) (seen ++ [j]) := by
  refine ⟨h.size, ?_, ?_⟩
  · intro v hv hb
    rcases List.mem_append.mp hv with hv | hv
    · exact List.mem_append_left _ (h.covered v hv hb)
    · have he : v = j := by simpa using hv
      subst v
      omega
  · intro v hv hb hm
    have hm' : starts[v]! ∈ cells := by
      simpa only [List.mem_append, List.mem_singleton, show starts[v]! ≠ n by omega, or_false] using hm
    rw [h.get v hv hb hm']
    have he : v ≠ j := by intro he; subst v; omega
    rw [List.count_append, List.count_eq_zero.mpr (show v ∉ [j] by simpa using he), Nat.add_zero]

end Counts

end Hex.GraphIso.Nauty.Sparse
