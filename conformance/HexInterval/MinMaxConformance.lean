/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval

/-!
# Exact minimum and maximum conformance

These guards discriminate every cut selector, tied endpoint attainment, empty
and unbounded behavior, operand order, both preflight comparisons, and final
normalization refusal.
-/

namespace Hex.Interval.MinMaxConformance

private def d (value : Int) : Dyadic := Dyadic.ofInt value

private def finite (lower : Int) (lowerStrict : Bool)
    (upper : Int) (upperStrict : Bool) : Raw :=
  .bounds (.finite (d lower) lowerStrict) (.finite (d upper) upperStrict)

private def smallLimit : EndpointLimit where
  maxEndpointHeight := 128
  maxAlignmentShift := 64

private def ready (raw : Raw) : Hex.Interval :=
  match Hex.Interval.ofRawWithin smallLimit raw with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

private def leftBand : Hex.Interval := ready (finite 1 false 4 false)
private def rightBand : Hex.Interval := ready (finite 2 false 3 false)

-- Minimum and maximum mix selectors rather than taking an intersection or
-- hull wholesale. Reversing the inputs pins commutative selection order.
#guard
  match Hex.Interval.minWithin smallLimit leftBand rightBand with
  | .ready interval => interval.view == finite 1 false 3 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.minWithin smallLimit rightBand leftBand with
  | .ready interval => interval.view == finite 1 false 3 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit leftBand rightBand with
  | .ready interval => interval.view == finite 2 false 4 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit rightBand leftBand with
  | .ready interval => interval.view == finite 2 false 4 false
  | .resourceLimit _ => false

private def leftTie : Hex.Interval := ready (finite 0 false 2 true)
private def rightTie : Hex.Interval := ready (finite 0 true 2 false)

-- At equal endpoints, minimum inherits lower attainment from either input
-- but needs upper attainment from both. Maximum has the dual rule.
#guard
  match Hex.Interval.minWithin smallLimit leftTie rightTie with
  | .ready interval => interval.view == finite 0 false 2 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit leftTie rightTie with
  | .ready interval => interval.view == finite 0 true 2 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.minWithin smallLimit rightTie leftTie with
  | .ready interval => interval.view == finite 0 false 2 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit rightTie leftTie with
  | .ready interval => interval.view == finite 0 true 2 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.minWithin smallLimit rightTie rightTie with
  | .ready interval => interval == rightTie
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit leftTie leftTie with
  | .ready interval => interval == leftTie
  | .resourceLimit _ => false

private def atMostOne : Hex.Interval :=
  ready (.bounds .unbounded (.finite (d 1) false))

private def atLeastOne : Hex.Interval :=
  ready (.bounds (.finite (d 1) false) .unbounded)

-- Empty is absorbing on both sides. One-sided extrema retain exactly the
-- unbounded side selected by the corresponding hull cut.
#guard
  match Hex.Interval.minWithin smallLimit Hex.Interval.empty leftBand with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.minWithin smallLimit leftBand Hex.Interval.empty with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit Hex.Interval.empty leftBand with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit leftBand Hex.Interval.empty with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.minWithin smallLimit atMostOne atLeastOne with
  | .ready interval => interval == atMostOne
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit atMostOne atLeastOne with
  | .ready interval => interval == atLeastOne
  | .resourceLimit _ => false

#guard
  match Hex.Interval.minWithin smallLimit Hex.Interval.whole leftBand with
  | .ready interval =>
      interval.view == .bounds .unbounded (.finite (d 4) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.maxWithin smallLimit Hex.Interval.whole leftBand with
  | .ready interval =>
      interval.view == .bounds (.finite (d 1) false) .unbounded
  | .resourceLimit _ => false

-- The first and second same-side comparisons are independently preflighted
-- before either selector can execute.
private def far : Dyadic := .ofOdd 1 1000000000 (by decide)

private def farLower : Hex.Interval :=
  match Hex.Interval.aboveWithin
      { maxEndpointHeight := 1000000100, maxAlignmentShift := 64 } far false with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

private def farUpper : Hex.Interval :=
  match Hex.Interval.belowWithin
      { maxEndpointHeight := 1000000100, maxAlignmentShift := 64 } far false with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

#guard
  match Hex.Interval.minWithin smallLimit leftBand farLower with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

#guard
  match Hex.Interval.maxWithin smallLimit leftBand farLower with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

#guard
  match Hex.Interval.minWithin smallLimit atMostOne farUpper with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

#guard
  match Hex.Interval.maxWithin smallLimit atMostOne farUpper with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

-- Same-side comparisons need no shift, but the selected final cuts do. This
-- pins the separate `ofRawWithin` comparison after selection.
private def bridgeLeft : Hex.Interval := ready (finite 1 false 4 false)
private def bridgeRight : Hex.Interval := ready (finite 3 false 12 false)

#guard
  match Hex.Interval.minWithin
      { maxEndpointHeight := 128, maxAlignmentShift := 0 }
      bridgeLeft bridgeRight with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 2

#guard
  match Hex.Interval.maxWithin
      { maxEndpointHeight := 128, maxAlignmentShift := 0 }
      bridgeLeft bridgeRight with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 2

end Hex.Interval.MinMaxConformance
