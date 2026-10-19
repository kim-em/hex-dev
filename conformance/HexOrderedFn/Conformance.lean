/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Tests
public import HexOrderedFn.InfinitesimalTests
public meta import HexOrderedFn.InfinitesimalTests
public meta import HexOrderedFn.Tests
public meta import HexOrderedFn

public section

/-!
Oracle: direct exact rational evaluation, literal expected bounds, Z3 RCF,
and python-flint canonical fractions (the emitted fixtures use pinned versions).
Mode: always; deterministic bounds, search and infinitesimal regression checks.
Covered operations: bounds construction, dyadic conversion, width, negation,
addition, multiplication, intersection, division and strict/exact signs; Horner
enclosure, finite signs, total sign and approximation, and first-success search;
lowest-index/coefficient scans, infinitesimal sign, comparison and successive levels.
Covered properties: finite signs agree with rational evaluation; bounds contain
endpoint and midpoint results; erased success witnesses do not bypass refinement;
double negation, addition commutativity/zero identity, widths of sums and negations,
and intersection idempotence, commutativity and membership.
Covered edge cases: zero, negative and zero-crossing bounds, nonpositive width
requests, earlier failed trials and nonmonotone success.

The imported core tests supply small ordinary-kernel checks alongside these
compiled checks. Horner and scan checks reach degree 12, coefficient heights reach 129 bits,
and infinitesimal depth reaches 3. Rational real subjects exercise finite queries
without asserting transcendence; semantic sqrt(2) cases live in the companion.

The provider-indexed `Extension` operations need a genuine universal progress
proof for executable coverage. The SPEC-required companion integration test
`HexOrderedFnTheory.LiouvilleTests` / `hexorderedfn_liouville_test` supplies it:
ordinary field arithmetic, sign, approximation, comparisons, provider transport
and derived coefficient approximation are checked on the same core definitions.
This test remains separate from Mathlib-free conformance. Algebraic tower
integration measurements belong to hex-real-closure under #10378.
Serialized source/context/version validation belongs to the consuming tactic;
this API binds registrations by type and the oracle rejects malformed fixtures.

Infinitesimal Z3/exact fixtures are emitted by `HexOrderedFn.EmitFixtures`.
Real refinement fixtures from `HexOrderedFn.EmitRealFixtures` check Horner bounds,
simultaneous refinement, total signs and first-success approximations with Z3
and independent exact Fraction arithmetic.
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
          else
            if !(low ≤ 0 && 0 ≤ high) then return false
  return true

#guard productsAgree

-- Algebraic laws on negative, positive, touching and disjoint closed bounds.
private def boundsAgree : Bool := Id.run do
  for ai in List.range 7 do
    for bi in List.range 7 do
      let lo : Rat := (ai : Int) - 3
      let low : Rat := (bi : Int) - 3
      let a : Bounds := ⟨lo, lo + 2, by grind⟩
      let b : Bounds := ⟨low, low + 2, by grind⟩
      if a.width != 2 || a.neg.width != 2 || (a.add b).width != 4 then return false
      if a.neg.neg != a || a.add b != b.add a || a.add (.singleton 0) != a then
        return false
      if a.inter a != some a || a.inter b != b.inter a then return false
      for zi in List.range 17 do
        let z : Rat := ((zi : Int) - 6) / 2
        let inside := lo ≤ z && z ≤ lo + 2 && low ≤ z && z ≤ low + 2
        let result := (a.inter b).any (fun c => c.lower ≤ z && z ≤ c.upper)
        if inside != result then return false
  return true

#guard boundsAgree

#guard Bounds.ofDyadic (.ofIntWithPrec 0 9) = .singleton 0
#guard Bounds.ofDyadic (.ofIntWithPrec 3 5) = .singleton (3/32)
#guard Bounds.ofDyadic (.ofIntWithPrec (2^128 + 1) 127) = .singleton (2 + 1/2^127)

#guard Real.requestWidth (1/7) = 1/7
#guard Real.requestWidth 0 = 1
#guard Real.requestWidth (-7/3) = 1

-- The start precision matters independently of the later success witness.
#guard firstSome trial 1 (acc_of_success trial 5 1 later 1 (by decide)) = -1
#guard firstSome trial 3 (acc_of_success trial 5 1 later 3 (by decide)) = 1
#guard firstSome trial 5 (acc_of_success trial 5 1 later 5 (by decide)) = 1

namespace InfinitesimalChecks
open Hex.OrderedFn.InfinitesimalTests
open scoped Hex.OrderedFn.Infinitesimal

private def scansAgree : Bool := Id.run do
  for n in [0, 1, 8, 12] do
    for a in [(-3 : Rat), -1, 1, 3] do
      let p := DensePoly.monomial n a
      if Infinitesimal.lowestIndex p != n || Infinitesimal.lowestCoeff p != a then
        return false
  return true

#guard scansAgree
#guard Infinitesimal.lowestIndex (0 : DensePoly Rat) = 0
#guard Infinitesimal.lowestCoeff (0 : DensePoly Rat) = 0

#guard Infinitesimal.sign orderSign (1 / (epsilon - 1)) = -1
#guard Infinitesimal.sign orderSign ((epsilon ^ 2 - 1) / (epsilon - 1)) = 1
#guard Infinitesimal.sign orderSign (-epsilon / (epsilon - 1)) = 1
#guard Infinitesimal.sign orderSign (epsilon - epsilon) = 0
#guard Infinitesimal.compare orderSign (epsilon - 1) 0 = .lt
#guard Infinitesimal.compare orderSign epsilon epsilon = .eq
#guard Infinitesimal.compare orderSign epsilon 0 = .gt
#guard (0 : First) < epsilon
#guard epsilon < (1 / 1000 : First)
#guard (1000 : First) < epsilon⁻¹
#guard delta < lift epsilon
#guard delta < lift (epsilon ^ 3)
#guard Infinitesimal.sign (Infinitesimal.sign orderSign) (delta - lift epsilon) = -1

-- Coefficient arithmetic in the polynomial ring over the infinitesimal field.
private def x : DensePoly First := DensePoly.monomial 1 1
private def e : DensePoly First := DensePoly.C epsilon
#guard (e*x^2 - 1)*(e*x^3 - 1) = e^2*x^5 - e*x^3 - e*x^2 + 1


end InfinitesimalChecks
