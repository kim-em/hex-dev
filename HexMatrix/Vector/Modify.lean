/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexMatrix.Basic

public section

/-!
Low-level vector update helper used for efficient code generation.
-/

namespace Vector

/--
In-place update of the element at index `i` via `f`, wrapping `Array.modify`
so the underlying swap-with-placeholder ownership transfer survives codegen.
Calling `xs.set i (f xs[i])` forces a `lean_inc` on the borrowed entry and
loses uniqueness on nested-array shapes (e.g. matrix rows); `modify` avoids
that copy when `xs` is uniquely owned.
-/
@[expose, inline] def modify (xs : Vector α n) (i : Nat) (f : α → α) : Vector α n :=
  ⟨xs.toArray.modify i f, by simp⟩

/-- Entrywise read of `modify`: the modified index gets `f` applied, every other
index is unchanged. -/
@[grind =] theorem getElem_modify {xs : Vector α n} {i : Nat} {f : α → α}
    {j : Nat} (hj : j < n) :
    (xs.modify i f)[j] = if i = j then f xs[j] else xs[j] := by
  rcases xs with ⟨a, rfl⟩
  simp only [modify, Vector.getElem_mk]
  rw [Array.getElem_modify]

/-- The modified index of `modify` reads back `f` applied to the old value. -/
theorem getElem_modify_self {xs : Vector α n} {i : Nat} {f : α → α} (hi : i < n) :
    (xs.modify i f)[i] = f xs[i] := by
  rw [getElem_modify hi, if_pos rfl]

/-- Any index other than the modified one is unchanged by `modify`. -/
theorem getElem_modify_of_ne {xs : Vector α n} {i j : Nat} {f : α → α}
    (hj : j < n) (h : i ≠ j) :
    (xs.modify i f)[j] = xs[j] := by
  rw [getElem_modify hj, if_neg h]

end Vector
