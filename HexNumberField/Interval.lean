/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberField.IntegerRoots
public section

/-! Certified coordinate probes and bounded refinement of selected roots. -/
namespace Hex.Interval

/-- Strict ordering certified by disjoint real-coordinate intervals. -/
@[expose] def realOrder? (a b : DyadicSquare) : Option Ordering :=
  if a.re + a.radiusHi < b.re - b.radiusHi then some .lt
  else if b.re + b.radiusHi < a.re - a.radiusHi then some .gt
  else none

/-- Disjoint imaginary-coordinate intervals certify incomparability. -/
@[expose] def imagApart (a b : DyadicSquare) : Bool :=
  decide (a.im + a.radiusHi < b.im - b.radiusHi) ||
    decide (b.im + b.radiusHi < a.im - a.radiusHi)

/-- A sound rejection of strict real-coordinate order, including touching endpoints. -/
@[expose] def notLt (a b : DyadicSquare) : Bool :=
  decide (b.re + b.radiusHi ≤ a.re - a.radiusHi)

/-- A sound rejection of non-strict real-coordinate order. -/
@[expose] def notLe (a b : DyadicSquare) : Bool :=
  decide (b.re + b.radiusHi < a.re - a.radiusHi)

/-- Probe stored squares first, then thread both representatives through a finite schedule.
`none` means inconclusive or failed refinement, never mathematical incomparability. -/
@[expose] def search {α : Type} {p q : ZPoly}
    (probe : DyadicSquare → DyadicSquare → Option α) :
    List (Int × Int) → RefinedIsolation p → RefinedIsolation q → Option α
  | targets, a, b =>
    match probe a.1.square b.1.square with
    | some result => some result
    | none => match targets with
      | [] => none
      | (pa, pb) :: rest => do
        let a' ← a.refineTo? pa
        let b' ← b.refineTo? pb
        search probe rest a'.1 b'.1

/-- Geometrically increasing targets, capped and structurally fueled. -/
@[expose] def targets (cap : Int) : Nat → Int → List (Int × Int)
  | 0, _ => []
  | fuel + 1, start =>
    let next := min cap (max (start + 1) (2 * start))
    (next, next) :: if next < cap then targets cap fuel next else []

/-- Two modest extra-precision rounds for an otherwise exact fallback. -/
@[expose] def extra (a b : DyadicSquare) : List (Int × Int) :=
  [(a.prec + 16, b.prec + 16), (a.prec + 64, b.prec + 64)]

end Hex.Interval
