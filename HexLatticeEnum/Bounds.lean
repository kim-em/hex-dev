/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexBasic
public import Init.Data.Rat.Lemmas
public import Init.Data.Nat.Sqrt

@[expose] public section

namespace Hex.LatticeEnum

/-- A closed integer interval; reversed endpoints represent the empty set. -/
structure Interval where
  /-- Inclusive lower endpoint. -/
  lo : Int
  /-- Inclusive upper endpoint. -/
  hi : Int
  deriving DecidableEq, Repr

/-- The exact number of integers in an interval. -/
def Interval.size (s : Interval) : Nat := (s.hi - s.lo + 1).toNat

/-- Exact interval for a positive quadratic weight and residual squared radius.
Nonpositive weights are rejected by returning an empty interval. -/
def bounds (c d r : Rat) : Interval :=
  if d ≤ 0 ∨ r < 0 then ⟨1, 0⟩ else
    let q := r / d
    let v : Int := c.den
    let t : Int := Nat.sqrt ((q.num * v * v / q.den).toNat)
    ⟨-((-(c.num - t)) / v), (c.num + t) / v⟩

/-- Two disjoint streams for Schnorr–Euchner coefficient ordering. -/
structure Coefficients where
  /-- The interval being traversed. -/
  interval : Interval
  /-- Rational centre, used only for exact integer distance comparisons. -/
  centre : Rat
  /-- Next value in the descending stream. -/
  left : Int
  /-- Next value in the ascending stream. -/
  right : Int
  deriving DecidableEq, Repr

/-- Initialize both streams without materializing the integer interval. -/
def coefficients (s : Interval) (c : Rat) : Coefficients :=
  ⟨s, c, min s.hi c.floor, max s.lo (c.floor + 1)⟩

/-- Visit the nearest remaining coefficient; smaller integers win ties. -/
def Coefficients.next? (s : Coefficients) : Option (Int × Coefficients) :=
  let hasLeft := s.interval.lo ≤ s.left
  let hasRight := s.right ≤ s.interval.hi
  if hasLeft && (!hasRight ||
      (s.left * (s.centre.den : Int) - s.centre.num).natAbs ≤
        (s.right * (s.centre.den : Int) - s.centre.num).natAbs) then
    some (s.left, { s with left := s.left - 1 })
  else if hasRight then
    some (s.right, { s with right := s.right + 1 })
  else none

/-- Consume at most the exact interval size, producing coefficients on demand. -/
def Coefficients.toList (s : Coefficients) : List Int :=
  go s.interval.size s
where
  go : Nat → Coefficients → List Int
    | 0, _ => []
    | k + 1, s => match s.next? with
      | none => []
      | some (z, s') => z :: go k s'

/-- Nearest integer with the smaller integer chosen on a half-integer tie. -/
def nearest (c : Rat) : Int :=
  let z := c.floor
  if 2 * (c.num - z * (c.den : Int)) ≤ (c.den : Int) then z else z + 1

end Hex.LatticeEnum
