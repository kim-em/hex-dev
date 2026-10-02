/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Init.Data.Range.Lemmas

public section

namespace Hex.GraphIso.Nauty.Sparse.Literal

/-- The same bounded traversal as the production range. Its list recursor
has an exported body, so it also computes in an importing module's kernel. -/
@[expose] def range (first last : Nat) : List Nat := List.range' first (last - first)

theorem range_forIn [Monad m] (first last : Nat) (a : α)
    (f : Nat → α → m (ForInStep α)) :
    forIn (range first last) a f = forIn [first:last] a f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [range, Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]

end Hex.GraphIso.Nauty.Sparse.Literal
