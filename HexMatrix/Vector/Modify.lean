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

/-- `modify` agrees with the read-then-`set` form (value-level; the point of
`modify` is that it avoids the copy that this form would force). -/
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

/-- In-place modification of row `i` via `f`. Linear in `M`: the matrix is
destructured (consuming `M`), so when `M` is uniquely referenced the row vector
is owned and `Vector.modify` updates the backing store without copying. -/
@[expose, inline]
def modify (M : Matrix R n m) (i : Nat) (f : Vector R m → Vector R m) : Matrix R n m :=
  match M with
  | ⟨d⟩ => ⟨d.modify i f⟩

/-- `Vector.get`-style row accessor; definitionally `getRow`. Provided so code
written against the nested-`Vector` representation keeps reading rows with
`M.get i`. -/
@[expose, inline] def get (M : Matrix R n m) (i : Fin n) : Vector R m := getRow M i

@[simp, grind =] theorem get_eq_getRow (M : Matrix R n m) (i : Fin n) :
    M.get i = getRow M i := rfl

@[simp, grind =] theorem rows_modify (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) : (modify M i f).rows = M.rows.modify i f := by
  cases M; rfl

/-- Row `i` of `modify M i f` is `f` applied to the old row `i`. -/
@[simp, grind =] theorem getRow_modify_self (M : Matrix R n m) (i : Fin n)
    (f : Vector R m → Vector R m) : getRow (modify M i.val f) i = f (getRow M i) := by
  simp only [getRow, rows_modify, Fin.getElem_fin]
  rw [Vector.getElem_modify_self i.isLt]

/-- Rows other than `i` are unchanged by `modify M i f`. -/
@[simp, grind =] theorem getRow_modify_ne (M : Matrix R n m) (i : Nat)
    (f : Vector R m → Vector R m) (j : Fin n) (h : i ≠ j.val) :
    getRow (modify M i f) j = getRow M j := by
  simp only [getRow, rows_modify, Fin.getElem_fin]
  rw [Vector.getElem_modify_of_ne j.isLt h]

end Hex.Matrix
