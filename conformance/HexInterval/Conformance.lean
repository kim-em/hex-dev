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
