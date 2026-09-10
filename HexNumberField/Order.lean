/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.Nearest
public section

/-! The complex partial order: only values with equal imaginary parts are comparable. -/
namespace Hex.AlgebraicNumber

/-- Compare values on the same horizontal line; `none` means incomparable.
Real inputs reuse `realCompare`, and differing half planes are rejected without arithmetic. -/
@[expose] def partialCompare (a b : AlgebraicNumber) : Option Ordering :=
  if a == b then some .eq
  else if a.isReal && b.isReal then some (realCompare a b)
  else if a.side ≠ b.side then none
  else
    let d := b - a
    if d.isReal then some (realCompare 0 d) else none

instance : LT AlgebraicNumber := ⟨fun a b => partialCompare a b = some .lt⟩
instance : LE AlgebraicNumber :=
  ⟨fun a b => (partialCompare a b).any (fun o => o != .gt) = true⟩

instance (a b : AlgebraicNumber) : Decidable (a < b) :=
  inferInstanceAs (Decidable (partialCompare a b = some .lt))
instance (a b : AlgebraicNumber) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable ((partialCompare a b).any (fun o => o != .gt) = true))

end Hex.AlgebraicNumber
