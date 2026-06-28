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

end Vector
