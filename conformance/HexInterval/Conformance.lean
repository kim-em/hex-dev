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

private def eightBitLimit : EndpointLimit where
  maxEndpointHeight := 8
  maxAlignmentShift := 0

private def nineBitLimit : EndpointLimit where
  maxEndpointHeight := 9
  maxAlignmentShift := 0

private def smallPowLimits : Arithmetic.PowLimits where
  maxExponent := 8

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

-- Multiplication's phase helpers remain distinguishable. Source size is an
-- observable endpoint refusal; the direct candidate guard pins the defensive
-- endpoint stage even though admitted corner growth makes it unreachable as
-- the first refusal of the current `mulWithin` pipeline. Only alignment is
-- reported as comparison work.
#guard
  match Raw.Mul.preflightEdge smallLimit (.finite far false) with
  | .error (.endpoint cost) => cost.exponentMagnitude == 1000000000
  | _ => false

#guard
  match Raw.Mul.preflightCandidate smallLimit (.finite far true) with
  | .error (.endpoint cost) => cost.exponentMagnitude == 1000000000
  | _ => false

#guard
  match Raw.Mul.preflightCompare
      { maxEndpointHeight := 1000000100, maxAlignmentShift := 64 }
      (.finite (d 1) true) (.finite far false) with
  | .error (.comparison cost) =>
      cost.lower.allowed { maxEndpointHeight := 1000000100, maxAlignmentShift := 64 } &&
        cost.upper.allowed
          { maxEndpointHeight := 1000000100, maxAlignmentShift := 64 } &&
        cost.alignmentShift == 1000000000
  | _ => false

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

-- Comparison cost cannot stand in for multiplicative growth. Both factors
-- fit the eight-bit endpoint limit and compare without alignment, but the
-- conservative product numerator needs sixteen bits. The arithmetic
-- preflight refuses before constructing `255 * 255` and reports that distinct
-- product cost.
#guard (EndpointCost.ofDyadic (d 255)).allowed eightBitLimit
#guard (CompareCost.ofDyadic (d 255) (d 255)).allowed eightBitLimit
#guard
  match Arithmetic.preflightMul eightBitLimit (d 255) (d 255) with
  | .error (.growth cost) =>
      cost.sources.map (·.numeratorBits) == [8, 8] &&
        cost.predicted.numeratorBits == 16 &&
        cost.predicted.exponentMagnitude == 0 &&
        !cost.allowed eightBitLimit
  | _ => false

-- Direct powers have their own one-source growth prediction. `3^4` fits the
-- eight-bit endpoint limit, while `3^5` is refused from metadata before
-- `Dyadic.pow` can allocate its mantissa.
#guard
  match Arithmetic.preflightPowGrowth eightBitLimit (d 3) 4 with
  | .ok cost =>
      cost.sources.map (·.numeratorBits) == [2] &&
        cost.predicted.numeratorBits == 8 &&
        (EndpointCost.ofDyadic ((d 3) ^ 4)).numeratorBits == 7 &&
        cost.predicted.exponentMagnitude == 0
  | _ => false

#guard
  match Arithmetic.preflightPowGrowth eightBitLimit (d 3) 5 with
  | .error (.growth cost) =>
      cost.sources.map (·.numeratorBits) == [2] &&
        cost.predicted.numeratorBits == 10 &&
        !cost.allowed eightBitLimit
  | _ => false

-- Unit numerators remain unit-sized even at a large exponent. This keeps the
-- preflight useful for exact powers of `1`, `-1`, and powers of two.
#guard
  match Arithmetic.preflightPowGrowth eightBitLimit (d 1) 1000000000 with
  | .ok cost => cost.predicted == EndpointCost.ofDyadic (d 1)
  | _ => false

#guard
  match Arithmetic.preflightPowGrowth eightBitLimit (d (-1)) 1000000001 with
  | .ok cost => cost.predicted == EndpointCost.ofDyadic (d 1)
  | _ => false

-- The direct-image convention keeps `0^0 = 1`; positive powers of zero stay
-- zero. Both have exact constant-size predictions.
#guard
  match Arithmetic.preflightPowGrowth eightBitLimit (d 0) 0 with
  | .ok cost => cost.predicted == EndpointCost.ofDyadic ((d 0) ^ 0)
  | _ => false

#guard
  match Arithmetic.preflightPowGrowth eightBitLimit (d 0) 1000000000 with
  | .ok cost => cost.predicted == EndpointCost.ofDyadic ((d 0) ^ 1000000000)
  | _ => false

private def quarter : Dyadic := .ofOdd 1 2 (by decide)
private def two : Dyadic := .ofOdd 1 (-1) (by decide)
private def threeHalves : Dyadic := .ofOdd 3 1 (by decide)
private def negThreeHalves : Dyadic := .ofOdd (-3) 1 (by decide)

-- Both signs of Core's signed dyadic exponent multiplication are reflected by
-- the exact magnitude metadata. Unit mantissas do not acquire numerator cost.
#guard
  match Arithmetic.preflightPowGrowth eightBitLimit two 3 with
  | .ok cost => cost.predicted == EndpointCost.ofDyadic (two ^ 3)
  | _ => false

-- A non-unit mantissa and nonzero dyadic exponent contribute independently to
-- the predicted retained height. Six mantissa bits plus exponent magnitude
-- three exceed the eight-bit combined endpoint limit.
#guard
  match Arithmetic.preflightPowGrowth eightBitLimit threeHalves 3 with
  | .error (.growth cost) =>
      cost.predicted.numeratorBits == 6 &&
        cost.predicted.exponentMagnitude == 3 &&
        !cost.allowed eightBitLimit
  | _ => false

-- Sign does not alter growth metadata, and exponent one is the identity case.
#guard
  match Arithmetic.preflightPowGrowth eightBitLimit negThreeHalves 1 with
  | .ok cost => cost.predicted == EndpointCost.ofDyadic (negThreeHalves ^ 1)
  | _ => false

#guard
  match Arithmetic.preflightPowGrowth eightBitLimit quarter 3 with
  | .ok cost =>
      cost.predicted.numeratorBits == 1 &&
        cost.predicted.exponentMagnitude == 6
  | _ => false

#guard
  match Arithmetic.preflightPowGrowth eightBitLimit quarter 4 with
  | .error (.growth cost) =>
      cost.predicted.numeratorBits == 1 &&
        cost.predicted.exponentMagnitude == 8 &&
        !cost.allowed eightBitLimit
  | _ => false

-- An inadmissible source is reported before multiplying its exponent by the
-- natural power. This separates source admission from predicted growth.
#guard
  match Arithmetic.preflightPowGrowth eightBitLimit far 1000000000 with
  | .error (.endpoint cost) => cost.exponentMagnitude == 1000000000
  | _ => false

#guard
  match Arithmetic.preflightPowGrowth eightBitLimit far 0 with
  | .error (.endpoint cost) => cost.exponentMagnitude == 1000000000
  | _ => false

-- Growth metadata is arbitrary-precision `Nat`, not a machine counter. This
-- exponent is one beyond `UInt64` range; it is diagnosed without wrapping and
-- without invoking Core power.
private def beyondUInt64 : Nat := 18446744073709551616

#guard
  match Arithmetic.preflightPowGrowth eightBitLimit two beyondUInt64 with
  | .error (.growth cost) =>
      cost.predicted.numeratorBits == 1 &&
        cost.predicted.exponentMagnitude == beyondUInt64 &&
        !cost.allowed eightBitLimit
  | _ => false

-- The composite prerequisite refuses huge nonzero unit powers with a distinct
-- work diagnostic even though their retained-growth prediction is constant.
#guard
  match Arithmetic.preflightPow eightBitLimit smallPowLimits
      (d 1) beyondUInt64 with
  | .error (.power work) => work.exponent == beyondUInt64
  | _ => false

#guard
  match Arithmetic.preflightPow eightBitLimit smallPowLimits
      (d (-1)) beyondUInt64 with
  | .error (.power work) => work.exponent == beyondUInt64
  | _ => false

-- Core's zero branch does not execute natural power or exponent conversion,
-- so it safely bypasses the scalar work cap even for an arbitrary large Nat.
#guard
  match Arithmetic.preflightPow eightBitLimit smallPowLimits
      (d 0) beyondUInt64 with
  | .ok cost =>
      cost.predicted == EndpointCost.ofDyadic ((d 0) ^ beyondUInt64)
  | _ => false

-- Once work passes, the composite preserves the growth prerequisite's exact
-- source and predicted-result diagnostic.
#guard
  match Arithmetic.preflightPow eightBitLimit smallPowLimits
      threeHalves 3 with
  | .error (.growth cost) =>
      cost.sources == [EndpointCost.ofDyadic threeHalves] &&
        cost.predicted.numeratorBits == 6 &&
        cost.predicted.encodedExponentBits == EndpointCost.natBits 3 &&
        cost.predicted.exponentMagnitude == 3 &&
        !cost.allowed eightBitLimit
  | _ => false

-- Source admission remains load-bearing after the work cap succeeds.
#guard
  match Arithmetic.preflightPow eightBitLimit smallPowLimits far 1 with
  | .error (.endpoint cost) => cost == EndpointCost.ofDyadic far
  | _ => false

-- An ordinary nonunit power is admitted only after both the actual exponent
-- and its combined retained growth pass.
#guard
  match Arithmetic.preflightPow nineBitLimit smallPowLimits
      threeHalves 3 with
  | .ok cost =>
      cost.predicted.numeratorBits == 6 &&
        cost.predicted.exponentMagnitude == 3
  | _ => false

-- Actual arbitrary-precision Nat comparison has no UInt64 wraparound: the
-- boundary value is admitted, while its successor is refused.
private def widePowLimits : Arithmetic.PowLimits where
  maxExponent := beyondUInt64

#guard
  match Arithmetic.preflightPow eightBitLimit widePowLimits
      (d 1) beyondUInt64 with
  | .ok cost => cost.predicted == EndpointCost.ofDyadic (d 1)
  | _ => false

#guard
  match Arithmetic.preflightPow eightBitLimit widePowLimits
      (d 1) (beyondUInt64 + 1) with
  | .error (.power work) => work.exponent == beyondUInt64 + 1
  | _ => false

/-! # Precision-indexed reciprocal/division resource prerequisite -/

private def precisionLimits : Arithmetic.PrecisionLimits where
  endpoint := { maxEndpointHeight := 18, maxAlignmentShift := 16 }
  maxPrecisionMagnitude := 16
  maxPrecisionBits := 8
  maxTemporaryBits := 32

-- The prerequisite authenticates Core's two rational-conversion shifts and
-- retained result without computing the reciprocal.  Positive and negative
-- `{3}` differ by the possible one-bit magnitude carry from flooring a
-- negative rational.
#guard
  match Arithmetic.preflightInv precisionLimits (d 3) 8 with
  | .ok (.checked cost) =>
      cost.sources.length == 1 &&
        cost.precision.magnitude == 8 && cost.precision.encodedBits == 4 &&
        cost.conversionShift == 8 && cost.crossProduct.isNone &&
        cost.rounding.numeratorBits == 9 && cost.rounding.denominatorBits == 2 &&
        cost.quotientBits == 9 && cost.predictedResultHeight == 17 &&
        cost.allowed precisionLimits
  | _ => false

#guard
  match Arithmetic.preflightInv precisionLimits (d (-3)) 8 with
  | .ok (.checked cost) =>
      cost.rounding.numeratorBits == 9 &&
        cost.quotientBits == 10 && cost.predictedResultHeight == 18 &&
        cost.allowed precisionLimits
  | _ => false

-- Direct division records the reduced rational cross-product bounds.  These
-- are not inferred from a comparison or from retained endpoint growth.
#guard
  match Arithmetic.preflightDiv precisionLimits (d 1) (d 3) 8 with
  | .ok (.checked cost) =>
      match cost.crossProduct with
      | some cross =>
          cross.numeratorBits == 1 && cross.denominatorBits == 2 &&
            cost.predictedResultHeight == 17 && cost.allowed precisionLimits
      | none => false
  | _ => false

#guard
  match Arithmetic.preflightDiv precisionLimits (d (-1)) (d 3) 8 with
  | .ok (.checked cost) =>
      cost.predictedResultHeight == 18 && cost.allowed precisionLimits
  | _ => false

-- A zero numerator remains zero through positive-precision rounding instead
-- of acquiring the precision's bit count. The nonzero denominator is still an
-- admitted, load-bearing source.
#guard
  match Arithmetic.preflightDiv precisionLimits 0 (d 3) 8 with
  | .ok (.checked cost) =>
      cost.sources == [EndpointCost.ofDyadic 0, EndpointCost.ofDyadic (d 3)] &&
        cost.rounding.numeratorBits == 0 && cost.quotientBits == 0 &&
        cost.predictedResultHeight == 0 && cost.allowed precisionLimits
  | _ => false

#guard
  match Arithmetic.preflightDiv precisionLimits 0 (d 3) (-8) with
  | .ok (.checked cost) =>
      cost.rounding.numeratorBits == 0 && cost.rounding.denominatorBits == 10 &&
        cost.quotientBits == 0 && cost.predictedResultHeight == 0 &&
        cost.allowed precisionLimits
  | _ => false

-- Core's zero cases do not inspect precision or enter rational conversion,
-- but the plan preserves every endpoint cost admitted before the short cut.
#guard
  match Arithmetic.preflightInv precisionLimits 0 1024 with
  | .ok (.zero sources) => sources == [EndpointCost.ofDyadic 0]
  | _ => false
#guard
  match Arithmetic.preflightDiv precisionLimits (d 1) 0 1024 with
  | .ok (.zero sources) =>
      sources == [EndpointCost.ofDyadic (d 1), EndpointCost.ofDyadic 0]
  | _ => false

-- Precision magnitude and encoding are refused before either rational
-- conversion or the source-exponent/precision metadata sum is formed.
#guard
  match Arithmetic.preflightInv precisionLimits (d 3) 1024 with
  | .error (.precision cost) =>
      cost.magnitude == 1024 && cost.encodedBits == 11 &&
        !cost.allowed precisionLimits
  | _ => false

private def tightPrecisionBitsLimits : Arithmetic.PrecisionLimits :=
  { precisionLimits with maxPrecisionMagnitude := 1024, maxPrecisionBits := 3 }

-- Encoding size is an independent gate: magnitude eight is admitted while
-- its four-bit encoding exceeds this deliberately smaller cap.
#guard
  match Arithmetic.preflightInv tightPrecisionBitsLimits (d 3) 8 with
  | .error (.precision cost) =>
      cost.magnitude == 8 && cost.encodedBits == 4 &&
        cost.magnitude ≤ tightPrecisionBitsLimits.maxPrecisionMagnitude &&
        !cost.allowed tightPrecisionBitsLimits
  | _ => false

private def inverseShiftInput : Dyadic := .ofOdd 3 (-8) (by decide)

private def nonCancellingLimits : Arithmetic.PrecisionLimits where
  endpoint := { maxEndpointHeight := 32, maxAlignmentShift := 15 }
  maxPrecisionMagnitude := 16
  maxPrecisionBits := 8
  maxTemporaryBits := 32

-- Core performs the source conversion and precision shifts separately.  The
-- signed values `-8` and `8` cancel algebraically, but the allocation work is
-- charged as `8 + 8` and refused before `toRat`.
#guard
  match Arithmetic.preflightInv nonCancellingLimits inverseShiftInput 8 with
  | .error (.quotient cost) =>
      cost.conversionShift == 16 &&
        cost.predictedResultHeight == 17 && !cost.allowed nonCancellingLimits
  | _ => false

private def oversizedSource : Dyadic := .ofOdd 1 32 (by decide)

-- Retained source admission precedes precision and rational-shape work.
#guard
  match Arithmetic.preflightInv precisionLimits oversizedSource 0 with
  | .error (.endpoint cost) =>
      cost.numeratorBits == 1 && cost.exponentMagnitude == 32 &&
        !cost.allowed precisionLimits.endpoint
  | _ => false

-- When source and precision both exceed their limits, source admission wins
-- deterministically and no precision metadata is consulted.
#guard
  match Arithmetic.preflightInv precisionLimits oversizedSource 1024 with
  | .error (.endpoint cost) => cost == EndpointCost.ofDyadic oversizedSource
  | _ => false

private def convertedTemporary : Dyadic := .ofOdd 3 16 (by decide)

private def tightConvertedLimits : Arithmetic.PrecisionLimits :=
  { precisionLimits with maxTemporaryBits := 16 }

-- The source and precision fit, but `toRat` would allocate a seventeen-bit
-- power-of-two denominator. The converted-shape gate is therefore
-- load-bearing independently of endpoint admission.
#guard
  match Arithmetic.preflightInv tightConvertedLimits convertedTemporary 0 with
  | .error (.quotient cost) =>
      cost.sources.all (EndpointCost.allowed tightConvertedLimits.endpoint) &&
        cost.precision.allowed tightConvertedLimits &&
        cost.converted == [{ numeratorBits := 2, denominatorBits := 17 }] &&
        !cost.converted.all
          (Arithmetic.RationalBound.allowed tightConvertedLimits.maxTemporaryBits) &&
        !cost.allowed tightConvertedLimits
  | _ => false

private def tightResultLimits : Arithmetic.PrecisionLimits where
  endpoint := { maxEndpointHeight := 16, maxAlignmentShift := 16 }
  maxPrecisionMagnitude := 16
  maxPrecisionBits := 8
  maxTemporaryBits := 32

-- Conversion and rounding temporaries fit, but the separately predicted
-- retained result height does not.
#guard
  match Arithmetic.preflightInv tightResultLimits (d 3) 8 with
  | .error (.quotient cost) =>
      cost.conversionShift == 8 &&
        cost.rounding.numeratorBits == 9 && cost.rounding.denominatorBits == 2 &&
        cost.rounding.allowed tightResultLimits.maxTemporaryBits &&
        cost.quotientBits == 9 && cost.predictedResultHeight == 17 &&
        !cost.allowed tightResultLimits
  | _ => false

private def tightQuotientLimits : Arithmetic.PrecisionLimits :=
  { precisionLimits with maxTemporaryBits := 9 }

-- Negative flooring may add one quotient-magnitude bit. All rational
-- temporaries fit nine bits, while the ten-bit integer quotient does not.
#guard
  match Arithmetic.preflightInv tightQuotientLimits (d (-3)) 8 with
  | .error (.quotient cost) =>
      cost.converted.all
          (Arithmetic.RationalBound.allowed tightQuotientLimits.maxTemporaryBits) &&
        cost.rounding.allowed tightQuotientLimits.maxTemporaryBits &&
        cost.quotientBits == 10 &&
        !(cost.quotientBits ≤ tightQuotientLimits.maxTemporaryBits) &&
        cost.predictedResultHeight ≤ tightQuotientLimits.endpoint.maxEndpointHeight &&
        !cost.allowed tightQuotientLimits
  | _ => false

private def oneOver256 : Dyadic := .ofOdd 1 8 (by decide)

private def tightTemporaryLimits : Arithmetic.PrecisionLimits where
  endpoint := { maxEndpointHeight := 16, maxAlignmentShift := 16 }
  maxPrecisionMagnitude := 16
  maxPrecisionBits := 8
  maxTemporaryBits := 15

-- Both retained sources and their `toRat` shapes fit, as does the predicted
-- retained result.  Division is nevertheless refused because `Rat.mul` may
-- allocate the sixteen-bit cross-product `255 * 256`.
#guard
  match Arithmetic.preflightDiv tightTemporaryLimits (d 255) oneOver256 0 with
  | .error (.quotient cost) =>
      cost.converted.all
          (Arithmetic.RationalBound.allowed tightTemporaryLimits.maxTemporaryBits) &&
        cost.conversionShift == 8 && cost.predictedResultHeight == 16 &&
        match cost.crossProduct with
        | some cross =>
            cross.numeratorBits == 16 && cross.denominatorBits == 1 &&
              !cross.allowed tightTemporaryLimits.maxTemporaryBits &&
              cost.quotientBits == 16 &&
              !cost.allowed tightTemporaryLimits
        | none => false
  | _ => false

private def ready (raw : Raw) : Hex.Interval :=
  match Hex.Interval.ofRawWithin smallLimit raw with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

private def farSingleton : Hex.Interval :=
  match Hex.Interval.singletonWithin
      { maxEndpointHeight := 1000000100, maxAlignmentShift := 0 } far with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

#guard farSingleton.view ==
  .bounds (.finite far false) (.finite far false)

private def closed01 : Hex.Interval := ready (finite 0 false 1 false)
private def closed12 : Hex.Interval := ready (finite 1 false 2 false)
private def openLower12 : Hex.Interval := ready (finite 1 true 2 false)
private def openAtOne : Hex.Interval := ready (finite 0 false 1 true)
private def atMostOne : Hex.Interval :=
  ready (.bounds .unbounded (.finite (d 1) false))
private def atLeastOne : Hex.Interval :=
  ready (.bounds (.finite (d 1) false) .unbounded)
private def closed23 : Hex.Interval := ready (finite 2 false 3 false)
private def closedNeg21 : Hex.Interval := ready (finite (-2) false (-1) false)
private def negOneToOpenZero : Hex.Interval := ready (finite (-1) false 0 true)
private def closedNeg21Cross : Hex.Interval := ready (finite (-2) false 1 false)
private def rightAbsClosed : Hex.Interval := ready (finite (-1) false 2 false)
private def rightAbsOpen : Hex.Interval := ready (finite (-1) false 2 true)
private def leftAbsOpen : Hex.Interval := ready (finite (-2) true 1 false)
private def tiedAbsMixed : Hex.Interval := ready (finite (-1) false 1 true)
private def tiedAbsMixedReverse : Hex.Interval := ready (finite (-1) true 1 false)
private def tiedAbsOpen : Hex.Interval := ready (finite (-1) true 1 true)
private def bridgeLeft : Hex.Interval := ready (finite 1 false 4 false)
private def bridgeRight : Hex.Interval := ready (finite 3 false 12 false)
private def openClosed01 : Hex.Interval := ready (finite 0 true 1 false)
private def closedOpen23 : Hex.Interval := ready (finite 2 false 3 true)
private def singletonOne : Hex.Interval := ready (finite 1 false 1 false)
private def singletonNegOne : Hex.Interval := ready (finite (-1) false (-1) false)
private def singletonZero : Hex.Interval := ready (finite 0 false 0 false)
private def singleton255 : Hex.Interval :=
  match Hex.Interval.singletonWithin eightBitLimit (d 255) with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty
private def mixedLeft : Hex.Interval := ready (finite (-2) false 3 false)
private def mixedRight : Hex.Interval := ready (finite (-4) false 5 false)
private def nonnegative : Hex.Interval :=
  ready (.bounds (.finite (d 0) false) .unbounded)
private def singletonThree : Hex.Interval := ready (finite 3 false 3 false)
private def atMostNegOne : Hex.Interval :=
  ready (.bounds .unbounded (.finite (d (-1)) false))
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

private def absFar : Dyadic := .ofOdd 1 200 (by decide)

private def absCrossFar : Hex.Interval :=
  match Hex.Interval.betweenWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 200 }
      (-absFar) false (d 1) false with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

-- Checked splitting is transactional: success carries both canonical
-- children, with the point closed on the left and strict on the right.
#guard
  match Hex.Interval.splitWithin smallLimit closed12 (d 1) with
  | .ready left right =>
      left.view == finite 1 false 1 false &&
        right.view == finite 1 true 2 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.splitWithin smallLimit closed23 (d 2) with
  | .ready left right =>
      left.view == finite 2 false 2 false &&
        right.view == finite 2 true 3 false
  | .resourceLimit _ => false

-- Whole has no source endpoints to select. A retained zero therefore produces
-- the canonical closed-left/strict-right half-lines directly.
#guard
  match Hex.Interval.splitWithin smallLimit Hex.Interval.whole (d 0) with
  | .ready left right =>
      left.view == .bounds .unbounded (.finite (d 0) false) &&
        right.view == .bounds (.finite (d 0) true) .unbounded
  | .resourceLimit _ => false

-- Point admission precedes every selector and child-normalization check, even
-- when the source itself has no finite endpoints.
#guard
  match Hex.Interval.splitWithin smallLimit Hex.Interval.whole far with
  | .ready _ _ => false
  | .resourceLimit cost => cost.upper.exponentMagnitude == 1000000000

-- A point outside the source gives one empty child and leaves the other
-- source set unchanged; no partial result is observable.
#guard
  match Hex.Interval.splitWithin smallLimit closed12 (d 0) with
  | .ready left right =>
      left == Hex.Interval.empty && right == closed12
  | .resourceLimit _ => false

#guard
  match Hex.Interval.splitWithin smallLimit closed12 (d 3) with
  | .ready left right =>
      left == closed12 && right == Hex.Interval.empty
  | .resourceLimit _ => false

-- Point ownership never adds a point excluded by the source interval.
#guard
  match Hex.Interval.splitWithin smallLimit openLower12 (d 1) with
  | .ready left right =>
      left == Hex.Interval.empty && right == openLower12
  | .resourceLimit _ => false

-- Empty bypasses point inspection and succeeds even for an endpoint that
-- would be over budget on a nonempty source.
#guard
  match Hex.Interval.splitWithin smallLimit Hex.Interval.empty far with
  | .ready left right =>
      left == Hex.Interval.empty && right == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.splitWithin smallLimit closed12 far with
  | .ready _ _ => false
  | .resourceLimit cost => cost.upper.exponentMagnitude == 1000000000

-- Once the point itself fits, each source-boundary selector comparison is
-- still independently refused before the unchecked dyadic comparison can
-- allocate its aligned mantissa.
private def splitFar : Dyadic := .ofOdd 1 100 (by decide)

#guard
  match Hex.Interval.splitWithin smallLimit atLeastOne splitFar with
  | .ready _ _ => false
  | .resourceLimit cost => cost.alignmentShift == 100

#guard
  match Hex.Interval.splitWithin smallLimit atMostOne splitFar with
  | .ready _ _ => false
  | .resourceLimit cost => cost.alignmentShift == 100

-- This bounded source was admitted with a ten-bit alignment budget. The
-- outside point lies between the endpoint exponents, so both selector
-- comparisons need only five bits, but the retained left child is the source
-- itself and its final normalization still needs ten. This isolates the
-- child-normalization preflight from point and selector refusal.
private def splitChildLimit : EndpointLimit where
  maxEndpointHeight := 16
  maxAlignmentShift := 5

private def splitSourceLimit : EndpointLimit where
  maxEndpointHeight := 16
  maxAlignmentShift := 10

private def splitLower : Dyadic := .ofOdd 1 10 (by decide)
private def splitOutside : Dyadic := .ofOdd 33 5 (by decide)

private def splitWideSource : Hex.Interval :=
  match Hex.Interval.betweenWithin splitSourceLimit
      splitLower false (d 1) false with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

#guard (CompareCost.ofDyadic splitLower splitOutside).allowed splitChildLimit
#guard (CompareCost.ofDyadic splitOutside (d 1)).allowed splitChildLimit
#guard !(splitWideSource.view.normalizeCost.allowed splitChildLimit)

#guard
  match Hex.Interval.splitWithin splitChildLimit splitWideSource splitOutside with
  | .ready _ _ => false
  | .resourceLimit cost => cost.alignmentShift == 10

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

private def farNegative : Hex.Interval :=
  match Hex.Interval.belowWithin
      { maxEndpointHeight := 1000000100, maxAlignmentShift := 64 } (-far) false with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

-- A source created under a larger budget is recharged at this operation's
-- boundary; sealing the source does not let an oversized endpoint bypass the
-- split preflight.
#guard
  match Hex.Interval.splitWithin smallLimit farLower (d 0) with
  | .ready _ _ => false
  | .resourceLimit cost => cost.lower.exponentMagnitude == 1000000000

#guard
  match Hex.Interval.splitWithin smallLimit farUpper (d 0) with
  | .ready _ _ => false
  | .resourceLimit cost => cost.upper.exponentMagnitude == 1000000000

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

-- Absolute value preserves sign-separated cuts, reverses negative cuts, and
-- closes zero exactly when the source contains it.
#guard
  match Hex.Interval.absWithin smallLimit Hex.Interval.empty with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit openClosed01 with
  | .ready interval => interval == openClosed01
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit closedNeg21 with
  | .ready interval => interval.view == finite 1 false 2 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit negOneToOpenZero with
  | .ready interval => interval.view == finite 0 true 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit closedNeg21Cross with
  | .ready interval => interval.view == finite 0 false 2 false
  | .resourceLimit _ => false

-- Both unequal selector directions and the selected endpoint's strictness are
-- observable. The larger right magnitude contributes its own closure flag;
-- the larger left magnitude inherits the source lower cut's strictness after
-- negation.
#guard
  match Hex.Interval.absWithin smallLimit rightAbsClosed with
  | .ready interval => interval.view == finite 0 false 2 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit rightAbsOpen with
  | .ready interval => interval.view == finite 0 false 2 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit leftAbsOpen with
  | .ready interval => interval.view == finite 0 false 2 true
  | .resourceLimit _ => false

-- At tied magnitudes the image endpoint is attained when either source end
-- is attained; it remains strict only when both are strict.
#guard
  match Hex.Interval.absWithin smallLimit tiedAbsMixed with
  | .ready interval => interval.view == finite 0 false 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit tiedAbsMixedReverse with
  | .ready interval => interval.view == finite 0 false 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit tiedAbsOpen with
  | .ready interval => interval.view == finite 0 false 1 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit Hex.Interval.whole with
  | .ready interval =>
      interval.view == .bounds (.finite (d 0) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit atLeastOne with
  | .ready interval => interval == atLeastOne
  | .resourceLimit _ => false

#guard
  match Hex.Interval.absWithin smallLimit atMostOne with
  | .ready interval =>
      interval.view == .bounds (.finite (d 0) false) .unbounded
  | .resourceLimit _ => false

-- Opposite endpoint magnitudes are preflighted before the unchecked selector
-- can align their mantissas.
#guard
  match Hex.Interval.absWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 64 } absCrossFar with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 200

-- A sign-separated case needs no selector comparison, but the selected
-- endpoint is still re-admitted under the caller's current retained-height
-- budget.
#guard
  match Hex.Interval.absWithin smallLimit farNegative with
  | .ready _ => false
  | .resourceLimit cost => cost.lower.exponentMagnitude == 1000000000

-- Returning an otherwise unchanged positive interval still rechecks its final
-- canonical comparison under the current caller budget.
#guard
  match Hex.Interval.absWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 64 } mediumToOne with
  | .ready _ => false
  | .resourceLimit cost => cost.alignmentShift == 200

-- Natural power keeps empty absorbing even at exponent zero, while every
-- nonempty zero power is the singleton one.
#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits
      Hex.Interval.empty beyondUInt64 with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

-- Core's zero short circuit remains load-bearing through the public operation:
-- an arbitrary large exponent does not consume the nonzero power-work budget.
#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits
      singletonZero beyondUInt64 with
  | .ready interval => interval.view == finite 0 false 0 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits closed01 0 with
  | .ready interval => interval.view == finite 1 false 1 false
  | .resourceLimit _ => false

-- Positive odd powers are strictly monotone over all reals and map direct
-- cuts, including negative/open and unbounded endpoints.
#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits leftAbsOpen 3 with
  | .ready interval => interval.view == finite (-8) true 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits closedNeg21 3 with
  | .ready interval => interval.view == finite (-8) false (-1) false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits atMostOne 3 with
  | .ready interval =>
      interval.view == .bounds .unbounded (.finite (d 1) false)
  | .resourceLimit _ => false

-- Positive even powers map the exact absolute-value hull. Strict zero is
-- retained when zero is excluded on either sign-separated side; mixed-sign
-- inputs contain zero and therefore close it.
#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits openClosed01 2 with
  | .ready interval => interval.view == finite 0 true 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits negOneToOpenZero 2 with
  | .ready interval => interval.view == finite 0 true 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits closedNeg21 2 with
  | .ready interval => interval.view == finite 1 false 4 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits rightAbsOpen 2 with
  | .ready interval => interval.view == finite 0 false 4 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits leftAbsOpen 2 with
  | .ready interval => interval.view == finite 0 false 4 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits tiedAbsMixed 2 with
  | .ready interval => interval.view == finite 0 false 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits tiedAbsOpen 2 with
  | .ready interval => interval.view == finite 0 false 1 true
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits atMostNegOne 2 with
  | .ready interval =>
      interval.view == .bounds (.finite (d 1) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits atMostOne 2 with
  | .ready interval =>
      interval.view == .bounds (.finite (d 0) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits Hex.Interval.whole 2 with
  | .ready interval =>
      interval.view == .bounds (.finite (d 0) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits
      Hex.Interval.whole beyondUInt64 with
  | .ready interval =>
      interval.view == .bounds (.finite (d 0) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits singletonNegOne 2 with
  | .ready interval => interval.view == finite 1 false 1 false
  | .resourceLimit _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits singletonZero 2 with
  | .ready interval => interval.view == finite 0 false 0 false
  | .resourceLimit _ => false

-- Refusal categories remain distinct. Work refuses huge nonzero unit powers;
-- growth refuses before `3^5`; even-power magnitude selection refuses before
-- its wide comparison; and final normalization can still refuse independently
-- after every endpoint power prerequisite succeeds.
#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits
      singletonOne beyondUInt64 with
  | .resourceLimit (.power work) => work.exponent == beyondUInt64
  | _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits
      singletonNegOne beyondUInt64 with
  | .resourceLimit (.power work) => work.exponent == beyondUInt64
  | _ => false

#guard
  match Hex.Interval.powWithin eightBitLimit smallPowLimits singletonThree 5 with
  | .resourceLimit (.growth cost) =>
      cost.predicted.numeratorBits == 10 && !cost.allowed eightBitLimit
  | _ => false

#guard
  match Hex.Interval.powWithin smallLimit smallPowLimits farNegative 1 with
  | .resourceLimit (.endpoint cost) => cost.exponentMagnitude == 1000000000
  | _ => false

#guard
  match Hex.Interval.powWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 64 }
      smallPowLimits absCrossFar 2 with
  | .resourceLimit (.comparison cost) => cost.alignmentShift == 200
  | _ => false

#guard
  match Hex.Interval.powWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 64 }
      smallPowLimits mediumToOne 1 with
  | .resourceLimit (.comparison cost) => cost.alignmentShift == 200
  | _ => false

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

-- A public interval admitted under a larger construction budget is rejected
-- at multiplication's source-endpoint phase under a smaller caller budget.
#guard
  match Hex.Interval.mulWithin smallLimit farSingleton singletonOne with
  | .resourceLimit (.endpoint cost) => cost.exponentMagnitude == 1000000000
  | _ => false

-- Source endpoints and all product-growth predictions fit, but the retained
-- candidates 1 and 2^100 require a prohibited alignment shift. This reaches
-- the public candidate-comparison diagnostic rather than only its helper.
#guard
  match Hex.Interval.mulWithin
      { maxEndpointHeight := 256, maxAlignmentShift := 50 }
      widePower singletonOne with
  | .resourceLimit (.comparison cost) =>
      cost.lower.allowed { maxEndpointHeight := 256, maxAlignmentShift := 50 } &&
        cost.upper.allowed { maxEndpointHeight := 256, maxAlignmentShift := 50 } &&
        cost.alignmentShift == 100
  | _ => false

-- Multiplication tracks endpoint attainment independently from the numerical
-- corner value. A contained zero closes the lower product endpoint even when
-- the other factor approaches zero only strictly.
#guard
  match Hex.Interval.mulWithin smallLimit closed01 openClosed01 with
  | .ready interval => interval == closed01
  | .resourceLimit _ => false

#guard
  match Hex.Interval.mulWithin smallLimit openClosed01 openClosed01 with
  | .ready interval => interval == openClosed01
  | .resourceLimit _ => false

-- Mixed signs exercise both minimum and maximum corner selectors.
#guard
  match Hex.Interval.mulWithin smallLimit mixedLeft mixedRight with
  | .ready interval => interval.view == finite (-12) false 15 false
  | .resourceLimit _ => false

-- Empty is absorbing. Singleton zero annihilates even a two-sided unbounded
-- factor, whereas a non-singleton interval containing zero still exposes both
-- unbounded directions when multiplied by the whole line.
#guard
  match Hex.Interval.mulWithin smallLimit Hex.Interval.empty Hex.Interval.whole with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

#guard
  match Hex.Interval.mulWithin smallLimit singletonZero Hex.Interval.whole with
  | .ready interval => interval == singletonZero
  | .resourceLimit _ => false

#guard
  match Hex.Interval.mulWithin smallLimit Hex.Interval.whole singletonZero with
  | .ready interval => interval == singletonZero
  | .resourceLimit _ => false

#guard
  match Hex.Interval.mulWithin smallLimit closed01 Hex.Interval.whole with
  | .ready interval => interval == Hex.Interval.whole
  | .resourceLimit _ => false

-- The unconditional extended-corner enumeration retains independent
-- unbounded sides; sign inspection only resolves finite-by-infinite corners.
#guard
  match Hex.Interval.mulWithin smallLimit nonnegative closed01 with
  | .ready interval => interval == nonnegative
  | .resourceLimit _ => false

private def nonpositiveOne : Hex.Interval :=
  ready (.bounds .unbounded (.finite (d (-1)) false))

#guard
  match Hex.Interval.mulWithin smallLimit nonpositiveOne nonpositiveOne with
  | .ready interval =>
      interval.view == .bounds (.finite (d 1) false) .unbounded
  | .resourceLimit _ => false

-- Product-growth refusal remains distinct from empty and happens while both
-- input endpoints and their exact comparison still fit the caller limit.
#guard
  match Hex.Interval.mulWithin eightBitLimit singleton255 singleton255 with
  | .ready _ => false
  | .resourceLimit (.growth cost) => cost.predicted.numeratorBits == 16
  | .resourceLimit _ => false

-- Ordinary positive multiplication succeeds through the richer arithmetic
-- result and retains both closed extrema.
#guard
  match Hex.Interval.mulWithin smallLimit closed12 closed23 with
  | .ready interval => interval.view == finite 2 false 6 false
  | .resourceLimit _ => false

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

/-! # Supported precision-indexed reciprocal -/

private def singletonNegThree : Hex.Interval := ready (finite (-3) false (-3) false)
private def closedOneThree : Hex.Interval := ready (finite 1 false 3 false)
private def closedNegOneZero : Hex.Interval := ready (finite (-1) false 0 false)
private def crossesZero : Hex.Interval := ready (finite (-1) false 1 false)
private def invDownThree : Dyadic := .ofOdd 85 8 (by decide)
private def invUpThree : Dyadic := .ofOdd 43 7 (by decide)

/-- Execute both the public prerequisite and Core reciprocal, then check that
the actual retained endpoint fits the successful predicted height. -/
private def invCostBounded (value : Dyadic) (precision : Precision) : Bool :=
  match Arithmetic.preflightInv precisionLimits value precision with
  | .ok (.checked cost) =>
      (EndpointCost.ofDyadic (value.invAtPrec precision)).allowed
        { maxEndpointHeight := cost.predictedResultHeight, maxAlignmentShift := 0 }
  | _ => false

-- The conservative prediction is checked against the actual Core result for
-- both input signs and for a nonzero negative precision. The last case uses
-- `2⁻⁸`, whose reciprocal is the nonzero coarse-grid value `2⁸`.
#guard invCostBounded (d 3) 8
#guard invCostBounded (d (-3)) 8
#guard invCostBounded oneOver256 (-8)
#guard oneOver256.invAtPrec (-8) == .ofOdd 1 (-8) (by decide)

-- `{3}` uses two independently rounded Core reciprocal calls.  The unequal
-- endpoints distinguish the outward upper rounding from copying the downward
-- result, and the negative case pins the sign-reversed construction.
#guard
  match Hex.Interval.invWithin precisionLimits 8 singletonThree with
  | .ready interval =>
      interval.view == .bounds
        (.finite invDownThree false) (.finite invUpThree false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 singletonNegThree with
  | .ready interval =>
      interval.view == .bounds
        (.finite (-invUpThree) false) (.finite (-invDownThree) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 closedOneThree with
  | .ready interval =>
      interval.view == .bounds
        (.finite invDownThree false) (.finite (d 1) false)
  | .resourceLimit _ => false

-- Expected-failure mutations: neither the downward endpoint reused as an
-- upper cut nor its sign-reflected analogue is the successful result.
#guard
  match Hex.Interval.invWithin precisionLimits 8 singletonThree with
  | .ready interval =>
      interval.view != .bounds
        (.finite invDownThree false) (.finite invDownThree false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 singletonNegThree with
  | .ready interval =>
      interval.view != .bounds
        (.finite (-invDownThree) false) (.finite (-invDownThree) false)
  | .resourceLimit _ => false

-- Open zero is a one-sided limit, while a closed zero contributes Lean's
-- total-inverse value `0⁻¹ = 0`. Crossing both signs requires the whole
-- connected hull. The singleton zero remains exact.
#guard
  match Hex.Interval.invWithin precisionLimits 8 openClosed01 with
  | .ready interval =>
      interval.view == .bounds (.finite (d 1) false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 closed01 with
  | .ready interval =>
      interval.view == .bounds (.finite 0 false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 closedNegOneZero with
  | .ready interval =>
      interval.view == .bounds .unbounded (.finite 0 false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 crossesZero with
  | .ready interval => interval == Hex.Interval.whole
  | .resourceLimit _ => false

-- Unbounded sign-separated inputs retain a strict zero limit. Whole remains
-- whole because the exact total-inverse image has both unbounded signs.
#guard
  match Hex.Interval.invWithin precisionLimits 8 atLeastOne with
  | .ready interval =>
      interval.view == .bounds (.finite 0 true) (.finite (d 1) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 atMostNegOne with
  | .ready interval =>
      interval.view == .bounds (.finite (d (-1)) false) (.finite 0 true)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 negOneToOpenZero with
  | .ready interval =>
      interval.view == .bounds .unbounded (.finite (d (-1)) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 Hex.Interval.whole with
  | .ready interval => interval == Hex.Interval.whole
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 1024 singletonZero with
  | .ready interval => interval == singletonZero
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 1024 Hex.Interval.empty with
  | .ready interval => interval == Hex.Interval.empty
  | .resourceLimit _ => false

-- Exact policy mutations: open zero never contributes Lean's value at zero,
-- closed zero is never discarded, and an unbounded sign-separated input keeps
-- its strict zero limit rather than closing it.
#guard
  match Hex.Interval.invWithin precisionLimits 8 openClosed01 with
  | .ready interval =>
      interval.view != .bounds (.finite 0 false) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 closed01 with
  | .ready interval =>
      interval.view != .bounds (.finite 0 true) .unbounded
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 atLeastOne with
  | .ready interval =>
      interval.view != .bounds (.finite 0 false) (.finite (d 1) false)
  | .resourceLimit _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 8 crossesZero with
  | .ready interval =>
      interval.view != .bounds .unbounded (.finite 0 false)
  | .resourceLimit _ => false

-- Precision, retained source, and predicted retained result are distinct
-- refusals, all occurring before `Dyadic.invAtPrec` is called.
#guard
  match Hex.Interval.invWithin precisionLimits 1024 singletonThree with
  | .resourceLimit (.precision cost) =>
      cost.magnitude == 1024 && !cost.allowed precisionLimits
  | _ => false

#guard
  match Hex.Interval.invWithin precisionLimits 0 farLower with
  | .resourceLimit (.endpoint cost) =>
      cost.exponentMagnitude == 1000000000 &&
        !cost.allowed precisionLimits.endpoint
  | _ => false

private def singletonShiftInput : Hex.Interval :=
  ready (.bounds (.finite inverseShiftInput false) (.finite inverseShiftInput false))

#guard
  match Hex.Interval.invWithin nonCancellingLimits 8 singletonShiftInput with
  | .resourceLimit (.quotient cost) =>
      cost.conversionShift == 16 && !cost.allowed nonCancellingLimits
  | _ => false

#guard
  match Hex.Interval.invWithin tightResultLimits 8 singletonThree with
  | .resourceLimit (.quotient cost) =>
      cost.predictedResultHeight == 17 && !cost.allowed tightResultLimits
  | _ => false

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
