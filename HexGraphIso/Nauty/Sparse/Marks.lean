/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Scratch

public section

namespace Hex.GraphIso.Nauty.Sparse.Scratch

/-- Allocated generation marks never exceed the current generation. -/
structure Marks (n stamp : Nat) (a : Array Nat) : Prop where
  size : a.size = n
  bound : ∀ i, i < n → a[i]! ≤ stamp

namespace Marks

variable {n stamp next i : Nat} {a : Array Nat}

theorem raise (h : Marks n stamp a) (hs : stamp ≤ next) : Marks n next a :=
  ⟨h.size, fun i hi => Nat.le_trans (h.bound i hi) hs⟩

theorem set (h : Marks n stamp a) (i : Nat) : Marks n stamp (a.setIfInBounds i stamp) := by
  refine ⟨by simpa using h.size, ?_⟩
  intro q hq
  change (a.set! i stamp)[q]! ≤ stamp
  by_cases he : i = q
  · subst i
    rw [Array.getElem!_set!_self _ _ _ (by rw [h.size]; exact hq)] <;> omega
  · rw [Array.getElem!_set!_ne _ _ _ _ he]
    exact h.bound q hq

/-- Advancing the generation makes every retained mark stale. -/
theorem fresh (h : Marks n stamp a) (hi : i < n) : a[i]! ≠ stamp + 1 := by
  have := h.bound i hi
  omega

end Marks
end Hex.GraphIso.Nauty.Sparse.Scratch
