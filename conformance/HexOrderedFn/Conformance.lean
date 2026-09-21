/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexOrderedFn.Tests
meta import HexOrderedFn.Tests
meta import HexOrderedFn

/-!
Exact rational regression checks for the bounds/search foundation.
These compare finite signs with direct rational evaluation and exercise the
total searches with erased finite-success proofs. Full Z3 and external exact
conformance for ordered extensions remains a separate phase obligation.
-/

open Hex Hex.OrderedFn Hex.OrderedFn.Oracle Hex.OrderedFn.Tests

-- The sign needs five attempts; the approximation needs five refinements.
#guard totalSign == 1
#guard totalApprox = ⟨31/32, 33/32, by decide +kernel⟩
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
      let product := a.mul b
      if !(product.lower ≤ x * y && x * y ≤ product.upper) then return false
      if let some quotient := a.div? b then
        if y == 0 then return false
        if !(quotient.lower ≤ x / y && x / y ≤ quotient.upper) then return false
  return true

#guard productsAgree
