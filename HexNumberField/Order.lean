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
@[expose] def partialCompareExact (a b : AlgebraicNumber) : Option Ordering :=
  if a == b then some .eq
  else if a.isReal && b.isReal then some (realCompare a b)
  else if a.side ≠ b.side then none
  else
    let d := b - a
    if d.isReal then some (realCompare 0 d) else none

/-- A successful probe certifies unequal imaginary coordinates. -/
@[expose] def apartProbe (a b : DyadicSquare) : Option Unit :=
  if Interval.imagApart a b then some () else none

/-- Partial comparison with bounded imaginary-interval rejection. -/
@[expose] def partialCompare (a b : AlgebraicNumber) : Option Ordering :=
  if a == b || (a.isReal && b.isReal) || decide (a.side ≠ b.side) then
    partialCompareExact a b
  else
    match Interval.search apartProbe (Interval.extra a.rep.1.square b.rep.1.square) a.rep b.rep with
    | some _ => none
    | none => partialCompareExact a b

/-- A successful probe rules out the requested complex-order predicate. -/
@[expose] def rejectProbe (strict : Bool) (a b : DyadicSquare) : Option Unit :=
  if Interval.imagApart a b || (if strict then Interval.notLt a b else Interval.notLe a b)
  then some () else none

/-- Read a strict or non-strict predicate from a partial comparison. -/
@[expose] def ordered (strict : Bool) (result : Option Ordering) : Bool :=
  result.any fun o => if strict then o == .lt else o != .gt

/-- Decide one predicate, rejecting impossible real inequalities without testing equality
of imaginary coordinates. Neither a positive answer nor incomparability is guessed. -/
@[expose] def orderBool (strict : Bool) (a b : AlgebraicNumber) : Bool :=
  if a == b || (a.isReal && b.isReal) || decide (a.side ≠ b.side) then
    ordered strict (partialCompareExact a b)
  else
    match Interval.search (rejectProbe strict)
        (Interval.extra a.rep.1.square b.rep.1.square) a.rep b.rep with
    | some _ => false
    | none => ordered strict (partialCompareExact a b)

instance : LT AlgebraicNumber := ⟨fun a b => orderBool true a b = true⟩
instance : LE AlgebraicNumber := ⟨fun a b => orderBool false a b = true⟩

instance (a b : AlgebraicNumber) : Decidable (a < b) :=
  inferInstanceAs (Decidable (orderBool true a b = true))

instance (a b : AlgebraicNumber) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (orderBool false a b = true))

end Hex.AlgebraicNumber
