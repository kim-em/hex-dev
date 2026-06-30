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

/-- `modify` agrees with the read-then-`set` form (value-level; `modify` avoids
the copy this form would force). -/
theorem modify_eq_set (xs : Vector α n) (i : Nat) (f : α → α) (h : i < n) :
    xs.modify i f = xs.set i (f xs[i]) := by
  apply Vector.ext
  intro j hj
  rw [getElem_modify hj, Vector.getElem_set]
  grind

end Vector

namespace Hex.Matrix

universe u
variable {R : Type u} {n m : Nat}

/-- In-place modification of row `i`. Linear in `M`: destructuring consumes `M`,
so when `M` is uniquely referenced the row is owned and `Vector.modify` updates
the backing store without copying. -/
@[expose, inline]
def modify (M : Matrix R n m) (i : Nat) (f : Vector R m → Vector R m) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨d.modify i f⟩

/-- Swap rows `i` and `j`, in place when `M` is uniquely referenced. -/
@[expose, inline]
def swap (M : Matrix R n m) (i j : Nat) (hi : i < n := by get_elem_tactic)
    (hj : j < n := by get_elem_tactic) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨d.swap i j hi hj⟩

/-- Map a function over every row, in place when `M` is uniquely referenced. -/
@[expose, inline]
def mapRows (M : Matrix R n m) (f : Vector R m → Vector R m') : Matrix R n m' :=
  match M with
  | ⟨d⟩ => ⟨d.map f⟩

@[simp, grind =] theorem rows_modify (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) : (modify M i f).rows = M.rows.modify i f := by
  cases M; rfl

@[simp, grind =] theorem rows_swap (M : Matrix R n m) (i j : Nat) (hi : i < n) (hj : j < n) :
    (M.swap i j hi hj).rows = M.rows.swap i j hi hj := by cases M; rfl

@[simp, grind =] theorem rows_mapRows (M : Matrix R n m) (f : Vector R m → Vector R m') :
    (M.mapRows f).rows = M.rows.map f := by cases M; rfl

end Hex.Matrix
