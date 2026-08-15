/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval
import HexInterval.Experiment.Representation

/-!
Conformance checks for exact raw interval cuts and canonical normalization.
The table covers every finite closure combination, both one-sided unbounded
shapes, the whole interval, the unique empty value, proper singletons, all
three empty equal-endpoint shapes, and reversed endpoints.  It also pins the
sealed public representation and its resource-safe constructors.
-/

namespace Hex.Interval.Conformance

private def d (value : Int) : Dyadic := Dyadic.ofInt value

private def finite (lower : Int) (lowerStrict : Bool)
    (upper : Int) (upperStrict : Bool) : Raw :=
  .bounds (.finite (d lower) lowerStrict) (.finite (d upper) upperStrict)

private def smallLimit : EndpointLimit where
  maxEndpointHeight := 128
  maxAlignmentShift := 64

#guard Raw.empty.normalizeUnchecked = .empty
#guard (Raw.bounds .unbounded .unbounded).normalizeUnchecked = .bounds .unbounded .unbounded
#guard
  (Raw.bounds .unbounded (.finite (d 1) false)).normalizeUnchecked =
    .bounds .unbounded (.finite (d 1) false)
#guard
  (Raw.bounds (.finite (d 0) true) .unbounded).normalizeUnchecked =
    .bounds (.finite (d 0) true) .unbounded

-- Every closure combination is nonempty when the finite endpoints differ.
#guard (finite 0 false 1 false).normalizeUnchecked = finite 0 false 1 false
#guard (finite 0 false 1 true).normalizeUnchecked = finite 0 false 1 true
#guard (finite 0 true 1 false).normalizeUnchecked = finite 0 true 1 false
#guard (finite 0 true 1 true).normalizeUnchecked = finite 0 true 1 true

-- Exactly the closed/closed equal-endpoint pair is a singleton.
#guard (finite 1 false 1 false).normalizeUnchecked = finite 1 false 1 false
#guard (finite 1 false 1 true).normalizeUnchecked = .empty
#guard (finite 1 true 1 false).normalizeUnchecked = .empty
#guard (finite 1 true 1 true).normalizeUnchecked = .empty

-- Reversed endpoints normalize to the unique empty representation.
#guard (finite 2 false 1 false).normalizeUnchecked = .empty
#guard (finite 2 true 1 true).normalizeUnchecked = .empty

-- The executable and propositional consistency views agree on representative
-- canonical and noncanonical values.
#guard (finite 0 true 1 true).consistent
#guard !(finite 1 true 1 false).consistent
#guard (finite 1 false 1 false).CutConsistent

-- The externally checked experiment rejects an unnormalized invalid trace
-- element rather than silently treating it as an empty proved interval.
#guard !Experiment.Checked.valid (finite 1 true 1 false)
#guard !Experiment.Checked.valid (Experiment.sample 5)

-- The planner-facing entry point agrees with exact normalization on inputs
-- whose endpoint and alignment costs fit its budget.
#guard
  match Raw.normalizeWithin smallLimit (finite 0 false 1 true) with
  | .ready raw _ => raw == finite 0 false 1 true
  | .resourceLimit _ => false
#guard
  match Raw.normalizeWithin smallLimit (finite 2 false 1 false) with
  | .ready raw _ => raw == .empty
  | .resourceLimit _ => false

-- A huge but compactly encoded exponent gap is rejected before `Dyadic.blt`
-- can allocate an aligned mantissa.
private def far : Dyadic := .ofOdd 1 1000000000 (by decide)

#guard
  match Raw.normalizeWithin
      { maxEndpointHeight := 1000000100, maxAlignmentShift := 64 }
      (.bounds (.finite (d 1) false) (.finite far false)) with
  | .ready _ _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

-- Finite endpoint height is charged even when the other side is unbounded and
-- no comparison shift is needed.
#guard
  match Raw.normalizeWithin smallLimit
      (.bounds .unbounded (.finite far false)) with
  | .ready _ _ => false
  | .resourceLimit cost => cost.upper.exponentMagnitude == 1000000000

-- Public construction exposes the same canonical views without exposing a
-- constructor or representation field.
#guard Hex.Interval.empty.view == .empty
#guard Hex.Interval.whole.view == .bounds .unbounded .unbounded
#guard decide (Hex.Interval.empty ≠ Hex.Interval.whole)

#guard
  match Hex.Interval.betweenWithin smallLimit (d 0) false (d 1) true with
  | .ready interval => interval.view == finite 0 false 1 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.betweenWithin smallLimit (d 2) false (d 1) false with
  | .ready interval => interval.view == .empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.singletonWithin smallLimit (d 1) with
  | .ready interval => interval.view == finite 1 false 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.belowWithin smallLimit far false with
  | .ready _ => false
  | .resourceLimit cost => cost.upper.exponentMagnitude == 1000000000

private def ready (raw : Raw) : Hex.Interval :=
  match Hex.Interval.ofRawWithin smallLimit raw with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

private def closed01 : Hex.Interval := ready (finite 0 false 1 false)
private def closed12 : Hex.Interval := ready (finite 1 false 2 false)
private def openLower12 : Hex.Interval := ready (finite 1 true 2 false)
private def openAtOne : Hex.Interval := ready (finite 0 false 1 true)
private def atMostOne : Hex.Interval :=
  ready (.bounds .unbounded (.finite (d 1) false))
private def atLeastOne : Hex.Interval :=
  ready (.bounds (.finite (d 1) false) .unbounded)
private def closed23 : Hex.Interval := ready (finite 2 false 3 false)
private def bridgeLeft : Hex.Interval := ready (finite 1 false 4 false)
private def bridgeRight : Hex.Interval := ready (finite 3 false 12 false)
private def openClosed01 : Hex.Interval := ready (finite 0 true 1 false)
private def closedOpen23 : Hex.Interval := ready (finite 2 false 3 true)
private def singletonOne : Hex.Interval := ready (finite 1 false 1 false)
private def singletonNegOne : Hex.Interval := ready (finite (-1) false (-1) false)
private def half : Dyadic := .ofOdd 1 1 (by decide)
private def singletonHalf : Hex.Interval :=
  ready (.bounds (.finite half false) (.finite half false))
private def twoPow100 : Dyadic := .ofOdd 1 (-100) (by decide)
private def widePower : Hex.Interval :=
  match Hex.Interval.betweenWithin
      { maxEndpointHeight := 128, maxAlignmentShift := 128 }
      (d 1) false twoPow100 false with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty
private def powerPlusOne : Dyadic := twoPow100 + d 1
private def powerPlusTwo : Dyadic := twoPow100 + d 2
private def powerBand : Hex.Interval :=
  match Hex.Interval.betweenWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 128 }
      powerPlusOne false powerPlusTwo false with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

-- Public intersection is exact at tied open/closed cuts, absorbs empty, and
-- retains independently unbounded ends.
#guard
  match Hex.Interval.intersectWithin smallLimit closed01 openLower12 with
  | .ready interval => interval.view == .empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.intersectWithin smallLimit closed01 atMostOne with
  | .ready interval => interval.view == finite 0 false 1 false
  | .resourceLimit _ => false

-- A tied endpoint is open when either contributing cut is open.  The strict
-- cut is deliberately the right input so this distinguishes disjunction from
-- copying the left flag.
#guard
  match Hex.Interval.intersectWithin smallLimit atMostOne openAtOne with
  | .ready interval => interval.view == finite 0 false 1 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.intersectWithin smallLimit Hex.Interval.empty closed01 with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

-- A finite-cut comparison is refused before the unchecked dyadic ordering can
-- align a billion-bit exponent gap.
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

private def mediumFar : Dyadic := .ofOdd 1 200 (by decide)

private def mediumToOne : Hex.Interval :=
  match Hex.Interval.betweenWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 200 }
      mediumFar false (d 1) false with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

#guard
  match Hex.Interval.intersectWithin smallLimit closed12 farLower with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

-- Same-side checks are absent for crossed one-sided inputs, so the selected
-- lower/upper normalization must itself remain behind `ofRawWithin`.
#guard
  match Hex.Interval.intersectWithin smallLimit farLower atMostOne with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

-- Hull chooses the smaller lower and larger upper cuts. Tied cuts are closed
-- when either input contains the endpoint; the strict input is placed first
-- so these guards reject copying one operand's flag.
#guard
  match Hex.Interval.hullWithin smallLimit openLower12 closed12 with
  | .ready interval => interval == closed12
  | .resourceLimit _ => false

#guard
  match Hex.Interval.hullWithin smallLimit openAtOne closed01 with
  | .ready interval => interval == closed01
  | .resourceLimit _ => false

-- Both strict contributors keep a tied endpoint strict; together with the
-- mixed guards above this pins conjunction rather than a constant flag.
#guard
  match Hex.Interval.hullWithin smallLimit openLower12 openLower12 with
  | .ready interval => interval == openLower12
  | .resourceLimit _ => false

#guard
  match Hex.Interval.hullWithin smallLimit openAtOne openAtOne with
  | .ready interval => interval == openAtOne
  | .resourceLimit _ => false

-- Reversing separated inputs exercises both selector directions. The result
-- is the interval closure [0,3], including the gap between [0,1] and [2,3].
#guard
  match Hex.Interval.hullWithin smallLimit closed01 closed23 with
  | .ready interval => interval.view == finite 0 false 3 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.hullWithin smallLimit closed23 closed01 with
  | .ready interval => interval.view == finite 0 false 3 false
  | .resourceLimit _ => false

-- Empty is an identity, while either unbounded side is retained.
#guard
  match Hex.Interval.hullWithin smallLimit Hex.Interval.empty closed01 with
  | .ready interval => interval == closed01
  | .resourceLimit _ => false

#guard
  match Hex.Interval.hullWithin smallLimit closed01 Hex.Interval.empty with
  | .ready interval => interval == closed01
  | .resourceLimit _ => false

#guard
  match Hex.Interval.hullWithin smallLimit atMostOne closed12 with
  | .ready interval =>
      interval.view == .bounds .unbounded (.finite (d 2) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.hullWithin smallLimit atLeastOne closed01 with
  | .ready interval =>
      interval.view == .bounds (.finite (d 0) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.hullWithin smallLimit atMostOne atLeastOne with
  | .ready interval => interval == Hex.Interval.whole
  | .resourceLimit _ => false

-- Same-side selection refuses an excessive alignment before ordering.
#guard
  match Hex.Interval.hullWithin smallLimit closed12 farLower with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

-- Same-side selectors need no shift here, but their selected outer cuts do.
-- This pins the separate final-normalization preflight in `ofRawWithin`.
#guard
  match Hex.Interval.hullWithin
      { maxEndpointHeight := 128, maxAlignmentShift := 0 }
      bridgeLeft bridgeRight with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 2

-- Addition uses the exact Minkowski endpoint sums. Closed endpoints are
-- attained, while either strict contributor makes the corresponding result
-- endpoint strict.
#guard
  match Hex.Interval.addWithin smallLimit closed01 closed23 with
  | .ready interval => interval.view == finite 2 false 4 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.addWithin smallLimit openClosed01 closedOpen23 with
  | .ready interval => interval.view == finite 2 true 4 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.addWithin smallLimit closedOpen23 openClosed01 with
  | .ready interval => interval.view == finite 2 true 4 true
  | .resourceLimit _ => false

-- Opposite exponent orders exercise both alignment branches in `Dyadic.add`.
#guard
  match Hex.Interval.addWithin smallLimit singletonHalf singletonOne with
  | .ready interval =>
      interval.view == .bounds
        (.finite ((d 3) >>> 1) false) (.finite ((d 3) >>> 1) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.addWithin smallLimit singletonOne singletonHalf with
  | .ready interval =>
      interval.view == .bounds
        (.finite ((d 3) >>> 1) false) (.finite ((d 3) >>> 1) false)
  | .resourceLimit _ => false

-- Empty is absorbing. Independent unbounded ends propagate through the
-- corresponding Minkowski cut, including the whole-line sum.
#guard
  match Hex.Interval.addWithin smallLimit Hex.Interval.empty closed01 with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.addWithin smallLimit closed01 Hex.Interval.empty with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.addWithin smallLimit atMostOne closed12 with
  | .ready interval =>
      interval.view == .bounds .unbounded (.finite (d 3) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.addWithin smallLimit atLeastOne closed01 with
  | .ready interval =>
      interval.view == .bounds (.finite (d 1) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.addWithin smallLimit atMostOne atLeastOne with
  | .ready interval => interval == Hex.Interval.whole
  | .resourceLimit _ => false

-- Endpoint addition refuses the billion-bit shift before `Dyadic.add` can
-- allocate the aligned mantissa.
#guard
  match Hex.Interval.addWithin smallLimit closed12 farLower with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

-- With both lower cuts unbounded, the independently preflighted upper
-- endpoint pair must still reject the same prohibited allocation.
#guard
  match Hex.Interval.addWithin smallLimit atMostOne farUpper with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

-- Input addition needs no shift and fits this tiny limit, but retaining the
-- canonical result `2` exceeds its endpoint-height budget. This pins the
-- separate checked output boundary after bounded temporary arithmetic.
#guard
  match Hex.Interval.addWithin
      { maxEndpointHeight := 1, maxAlignmentShift := 0 }
      singletonOne singletonOne with
  | .ready _ => false
  | .resourceLimit cost =>
      cost.lower.exponentMagnitude == 1 && cost.upper.exponentMagnitude == 1

-- Corresponding input endpoints require no alignment, but the two summed
-- output endpoints are one hundred powers of two apart. The final checked
-- canonicalization must reject that distinct output-comparison cost.
#guard
  match Hex.Interval.addWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 50 }
      widePower widePower with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 100

-- Subtraction uses crossed endpoints and is directional: [2,3] - [0,1] is
-- [1,3], while reversing the operands yields [-3,-1].
#guard
  match Hex.Interval.subWithin smallLimit closed23 closed01 with
  | .ready interval => interval.view == finite 1 false 3 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.subWithin smallLimit closed01 closed23 with
  | .ready interval => interval.view == finite (-3) false (-1) false
  | .resourceLimit _ => false

-- The lower result consumes the left lower and right upper strictness; the
-- upper result consumes the left upper and right lower strictness.
#guard
  match Hex.Interval.subWithin smallLimit openClosed01 closedOpen23 with
  | .ready interval => interval.view == finite (-3) true (-1) false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.subWithin smallLimit closedOpen23 openClosed01 with
  | .ready interval => interval.view == finite 1 false 3 true
  | .resourceLimit _ => false

-- Empty is absorbing. The right upper controls lower unboundedness and the
-- right lower controls upper unboundedness; two matching half-lines can span
-- the whole line.
#guard
  match Hex.Interval.subWithin smallLimit Hex.Interval.empty closed01 with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.subWithin smallLimit closed01 Hex.Interval.empty with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.subWithin smallLimit closed01 atLeastOne with
  | .ready interval =>
      interval.view == .bounds .unbounded (.finite (d 0) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.subWithin smallLimit closed01 atMostOne with
  | .ready interval =>
      interval.view == .bounds (.finite (d (-1)) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.subWithin smallLimit atMostOne atMostOne with
  | .ready interval => interval == Hex.Interval.whole
  | .resourceLimit _ => false

-- Each crossed endpoint pair has its own pre-allocation check.
#guard
  match Hex.Interval.subWithin smallLimit closed12 farUpper with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

#guard
  match Hex.Interval.subWithin smallLimit atMostOne farLower with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 1000000000

-- The lower subtraction `1 - 1` is cheap, but the upper pair needs a 200-bit
-- shift. The second preflight rejects before either unchecked subtraction
-- runs; the fixture itself stays small enough not to perform a huge admitted
-- comparison during construction.
#guard
  match Hex.Interval.subWithin smallLimit singletonOne mediumToOne with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 200

-- Both endpoint subtractions fit this tiny budget, but retaining the result
-- singleton `2` does not.
#guard
  match Hex.Interval.subWithin
      { maxEndpointHeight := 1, maxAlignmentShift := 0 }
      singletonOne singletonNegOne with
  | .ready _ => false
  | .resourceLimit cost =>
      cost.lower.exponentMagnitude == 1 && cost.upper.exponentMagnitude == 1

-- The two crossed input pairs need shifts zero and one. Cancellation produces
-- output endpoints `2^100` and `2^100 + 1`, so only the distinct final
-- canonical comparison exceeds this operation's alignment budget.
#guard
  match Hex.Interval.subWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 50 }
      powerBand singletonOne with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 100

-- Negation swaps the endpoints and preserves openness; empty stays empty.
#guard
  match Hex.Interval.negWithin smallLimit (ready (finite (-2) true 1 false)) with
  | .ready interval => interval.view == finite (-1) false 2 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.negWithin smallLimit atMostOne with
  | .ready interval => interval.view == .bounds (.finite (d (-1)) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.negWithin smallLimit Hex.Interval.empty with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

/-- The supported public view exposes its carried canonicality theorem without
adding any trust assumption. -/
theorem publicViewCanonical (interval : Hex.Interval) : interval.view.CutConsistent :=
  Hex.Interval.view_consistent interval

/-- info: 'Hex.Interval.Conformance.publicViewCanonical' depends on axioms: [propext] -/
#guard_msgs in
#print axioms publicViewCanonical

example {limit : EndpointLimit} {raw : Raw} {interval : Hex.Interval}
    (h : Hex.Interval.ofRawWithin limit raw = .ready interval) :
    interval.view = raw.normalizeUnchecked :=
  Hex.Interval.view_ofRawWithin_ready h

example (left right : Hex.Interval) (h : left.view = right.view) : left = right :=
  Hex.Interval.ext h

end Hex.Interval.Conformance
