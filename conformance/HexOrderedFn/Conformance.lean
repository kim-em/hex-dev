/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Tests
public meta import HexOrderedFn.Tests
public meta import HexOrderedFn

public section

/-!
Oracle: direct exact rational evaluation and literal expected bounds.
Mode: always; deterministic regression checks for the bounds/search foundation.
Covered operations: bound multiplication/division, finite signs and total refinement.
Covered properties: finite signs agree with rational evaluation; bounds contain
endpoint and midpoint results; erased success witnesses do not bypass refinement.
Covered edge cases: zero, negative and zero-crossing bounds, nonpositive width
requests, earlier failed trials and nonmonotone success.

Full Z3 and external exact conformance for ordered extensions remains a separate
phase obligation.
-/

open Hex Hex.OrderedFn Hex.OrderedFn.Oracle Hex.OrderedFn.Tests

-- The sign needs five attempts; the approximation needs five refinements.
#guard totalSign == 1
#guard totalApprox = ⟨31/32, 33/32, by decide +kernel⟩
#guard coarseApprox = ⟨1/2, 3/2, by decide +kernel⟩
-- A later successful witness does not bypass an earlier successful attempt.
#guard first == -1

private def signsAgree : Bool := Id.run do
  for qi in List.range 9 do
    for ci in List.range 9 do
      let q : Rat := (qi : Int) - 4
      let c : Rat := ((ci : Int) - 4) / 3
      let value := q - c
      let s : Int := if 0 < value then 1 else if value < 0 then -1 else 0
      if Real.sign? (exact q) (linear c) 1 != some s then return false
  return true

#guard signsAgree

-- All four sign combinations of numerator and denominator endpoints, as well
-- as zero-crossing numerator bounds, are exercised against rational samples.
private def productsAgree : Bool := Id.run do
  for ai in List.range 5 do
    for bi in List.range 5 do
      let lo : Rat := (ai : Int) - 2
      let hi := lo + 1
      let a : Bounds := ⟨lo, hi, by dsimp [hi]; grind⟩
      let low : Rat := (bi : Int) - 2
      let high := low + 1
      let b : Bounds := ⟨low, high, by dsimp [high]; grind⟩
      let x := (lo + hi) / 2
      let y := (low + high) / 2
      for s in [lo, x, hi] do
        for t in [low, y, high] do
          let product := a.mul b
          if !(product.lower ≤ s * t && s * t ≤ product.upper) then return false
          if let some quotient := a.div? b then
            if t == 0 then return false
            if !(quotient.lower ≤ s / t && s / t ≤ quotient.upper) then return false
  return true

#guard productsAgree
