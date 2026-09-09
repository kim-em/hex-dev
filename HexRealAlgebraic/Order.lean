/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRealAlgebraic.Basic
public import Init.Data.Order

public section

/-! Exact comparison and rounding of canonical real algebraic numbers. -/

namespace Hex.RealAlgebraicNumber

/-- Exact comparison, using the separation precision of the product polynomial. -/
@[expose] def compare (a b : RealAlgebraicNumber) : Ordering :=
  a.toAlgebraic.realCompare b.toAlgebraic

instance : Ord RealAlgebraicNumber := ⟨compare⟩
instance : LT RealAlgebraicNumber := ⟨fun a b => compare a b = .lt⟩
instance : LE RealAlgebraicNumber := ⟨fun a b => compare a b ≠ .gt⟩
instance : DecidableLT RealAlgebraicNumber := fun a b =>
  inferInstanceAs (Decidable (compare a b = .lt))
instance : DecidableLE RealAlgebraicNumber := fun a b =>
  inferInstanceAs (Decidable (compare a b ≠ .gt))

/-- Minimum, returning the left argument on a tie. -/
@[expose] def min (a b : RealAlgebraicNumber) : RealAlgebraicNumber :=
  if a ≤ b then a else b
/-- Maximum, returning the left argument on a tie. -/
@[expose] def max (a b : RealAlgebraicNumber) : RealAlgebraicNumber :=
  if b ≤ a then a else b

instance : Min RealAlgebraicNumber := ⟨min⟩
instance : Max RealAlgebraicNumber := ⟨max⟩

/-- The exact sign, valued in minus one, zero, and one. -/
@[expose] def sign (a : RealAlgebraicNumber) : Int :=
  match compare a 0 with
  | .lt => -1
  | .eq => 0
  | .gt => 1

/-- Absolute value computed by exact sign comparison. -/
@[expose] def abs (a : RealAlgebraicNumber) : RealAlgebraicNumber :=
  if a < 0 then -a else a

/-- Recognize a rational by its linear canonical minimal polynomial. -/
@[expose] def toRat? (a : RealAlgebraicNumber) : Option Rat :=
  let p := a.toAlgebraic.p
  if p.natDegree = 1 then
    some (-(p.coeff 0 : Rat) / (p.coeff 1 : Rat))
  else none

/-- The floor of the lower endpoint of the precision-two enclosure. -/
@[expose] def floorLower (a : RealAlgebraicNumber) : Int :=
  let b := a.approxBall 2
  (b.re.toRat - b.radius.toRat).floor

/-- The floor of the upper endpoint of the precision-two enclosure. -/
@[expose] def floorUpper (a : RealAlgebraicNumber) : Int :=
  let b := a.approxBall 2
  (b.re.toRat + b.radius.toRat).floor

/-- Exact floor: the enclosure supplies at most two consecutive candidates,
with one comparison at the intervening integer when necessary. -/
@[expose] def floor (a : RealAlgebraicNumber) : Int :=
  match a.toRat? with
  | some q => q.floor
  | none =>
    let b := a.approxBall 2
    let lo := (b.re.toRat - b.radius.toRat).floor
    let hi := (b.re.toRat + b.radius.toRat).floor
    if lo = hi then lo
    else if a < (hi : RealAlgebraicNumber) then lo else hi

/-- Exact ceiling, obtained from floor by negation. -/
@[expose] def ceil (a : RealAlgebraicNumber) : Int := -(-a).floor

/-- Ceiling and floor obey their defining negation relation. -/
theorem ceil_eq (a : RealAlgebraicNumber) : a.ceil = -(-a).floor := rfl

end Hex.RealAlgebraicNumber
