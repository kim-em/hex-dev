/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Canonical

public section

/-!
# Arithmetic resource preflight

Endpoint comparison cost does not bound numerator growth in multiplication or
direct powers. This module supplies a separate, nonbreaking result and
diagnostic layer for checked arithmetic. Existing constructors and supported
public interval operations whose costs are comparisons continue to return
`BuildResult`; multiplication and direct natural power report growth without
fabricating a `CompareCost`. Concrete corner enumeration and interval
multiplication live in `HexInterval.Multiplication`, not in this reusable cost
layer. Precision-indexed reciprocal and division additionally cross Core's
`Dyadic.toRat`/`Rat.toDyadic` boundary, so their prerequisites record
precision, rational-conversion, and temporary product bounds separately from
retained endpoint growth.
-/

namespace Hex.Interval.Arithmetic

/-- Allocation-independent preflight data for endpoint growth. `sources`
records the already-admitted inputs and `predicted` is a conservative bound on
the endpoint an arithmetic action would construct. Multiplication uses two
sources; a direct power can reuse the same shape with one source. -/
structure Growth where
  sources : List EndpointCost
  predicted : EndpointCost
  deriving DecidableEq, Repr

namespace Growth

/-- Endpoint growth is admitted only when every source and the conservative
result bound fit the retained-height budget. -/
def allowed (limit : EndpointLimit) (growth : Growth) : Bool :=
  growth.sources.all (EndpointCost.allowed limit) &&
    growth.predicted.allowed limit

end Growth

/-- Execution-work limit for the direct natural-power operation. The cap
is on the actual exponent value, not the size of its binary encoding. -/
structure PowLimits where
  maxExponent : Nat
  deriving DecidableEq, Repr

/-- Work demanded by Core's nonzero dyadic natural-power path. -/
structure PowWork where
  exponent : Nat
  deriving DecidableEq, Repr

namespace PowWork

/-- Admit Core nonzero power work only when the actual natural exponent is no
larger than the configured scalar cap. `Nat` comparison is arbitrary precision
and cannot wrap at a machine-word boundary. -/
def allowed (limits : PowLimits) (work : PowWork) : Bool :=
  work.exponent ≤ limits.maxExponent

end PowWork

/-! ## Precision-indexed rational conversion -/

/-- Limits needed before entering Core's rational-backed dyadic reciprocal or
division. Retained endpoints and aggregate conversion shifts keep their
existing meanings. Precision encoding and temporary rational integers have
separate bounds rather than being disguised as endpoint height or comparison
cost. -/
structure PrecisionLimits where
  endpoint : EndpointLimit
  maxPrecisionMagnitude : Nat
  maxPrecisionBits : Nat
  maxTemporaryBits : Nat
  deriving DecidableEq, Repr

/-- Allocation-independent size of a requested signed precision. -/
structure PrecisionCost where
  encodedBits : Nat
  magnitude : Nat
  deriving DecidableEq, Repr

namespace PrecisionCost

/-- Measure a signed precision without constructing a power of two. -/
def ofPrecision (precision : Precision) : PrecisionCost :=
  let magnitude := precision.natAbs
  { encodedBits := EndpointCost.natBits magnitude, magnitude }

/-- Admit both the magnitude of a precision and the size of its existing
arbitrary-precision encoding. -/
def allowed (limits : PrecisionLimits) (cost : PrecisionCost) : Bool :=
  cost.encodedBits ≤ limits.maxPrecisionBits &&
    cost.magnitude ≤ limits.maxPrecisionMagnitude

end PrecisionCost

/-- Conservative bit bounds for the numerator and denominator of a rational
temporary. These are integer bit lengths, not retained dyadic endpoint data. -/
structure RationalBound where
  numeratorBits : Nat
  denominatorBits : Nat
  deriving DecidableEq, Repr

namespace RationalBound

/-- Admit both integer components of a rational temporary. -/
def allowed (limit : Nat) (bound : RationalBound) : Bool :=
  bound.numeratorBits ≤ limit && bound.denominatorBits ≤ limit

end RationalBound

/-- Complete pre-allocation record for a nonzero reciprocal or division.

`converted` bounds the exact `Dyadic.toRat` source shapes. `conversionShift`
charges every source-exponent shift plus the precision shift without signed
cancellation. `crossProduct` is absent for `invAtPrec` and bounds the reduced
rational numerator/denominator products formed by `divAtPrec`. `rounding`
bounds the rational side shifted by `Rat.toDyadic`, `quotientBits` bounds the
integer passed to `Dyadic.ofIntWithPrec`, and
`predictedResultHeight` bounds the canonical retained dyadic height after
trailing-zero normalization. -/
structure QuotientCost where
  sources : List EndpointCost
  precision : PrecisionCost
  converted : List RationalBound
  conversionShift : Nat
  crossProduct : Option RationalBound
  rounding : RationalBound
  quotientBits : Nat
  predictedResultHeight : Nat
  deriving DecidableEq, Repr

namespace QuotientCost

/-- Admit all retained inputs, precision metadata, conversion work,
rational temporaries, the integer quotient, and the retained result bound. -/
def allowed (limits : PrecisionLimits) (cost : QuotientCost) : Bool :=
  cost.sources.all (EndpointCost.allowed limits.endpoint) &&
    cost.precision.allowed limits &&
    cost.converted.all (RationalBound.allowed limits.maxTemporaryBits) &&
    cost.conversionShift ≤ limits.endpoint.maxAlignmentShift &&
    cost.crossProduct.all (RationalBound.allowed limits.maxTemporaryBits) &&
    cost.rounding.allowed limits.maxTemporaryBits &&
    cost.quotientBits ≤ limits.maxTemporaryBits &&
    cost.predictedResultHeight ≤ limits.endpoint.maxEndpointHeight

end QuotientCost

/-- A successful preflight. Core returns zero without rational conversion when
the reciprocal input or division denominator is zero; that plan still retains
the endpoint costs already admitted before the short circuit. -/
inductive QuotientPlan where
  | zero (sources : List EndpointCost)
  | checked (cost : QuotientCost)
  deriving DecidableEq, Repr

/-- Resource diagnostics for checked public arithmetic. Product growth,
direct-power work, precision requests, and rational-backed quotient work are
separate cases from endpoint and comparison work; none can be inferred
honestly from the cost of comparing already-admitted endpoints. -/
inductive Cost where
  | endpoint (cost : EndpointCost)
  | comparison (cost : CompareCost)
  | growth (cost : Growth)
  | power (work : PowWork)
  | precision (cost : PrecisionCost)
  | quotient (cost : QuotientCost)
  deriving DecidableEq, Repr

/-- Result type for public arithmetic whose work is not described by
`CompareCost`. Refusal remains distinct from the canonical empty interval. -/
inductive Result where
  | ready (interval : Hex.Interval)
  | resourceLimit (cost : Cost)

namespace Result

/-- Embed the existing checked-construction result into the richer arithmetic
result without changing the constructor, intersection, hull, addition, or
subtraction APIs. -/
@[expose] def ofBuild : BuildResult → Result
  | .ready interval => .ready interval
  | .resourceLimit cost => .resourceLimit (.comparison cost)

end Result

/-- Preflight a dyadic multiplication without multiplying its mantissas.

The source endpoint checks happen before the signed exponent sum is formed.
After those checks, the sum of exponent representations and the sum of the two
small numerator-bit counts are bounded metadata computations. A successful
result bounds the actual product numerator by `predicted.numeratorBits` and
uses its exact signed exponent magnitude. -/
def preflightMul (limit : EndpointLimit) (left right : Dyadic) :
    Except Cost Growth := do
  let leftCost := EndpointCost.ofDyadic left
  if !leftCost.allowed limit then
    throw (.endpoint leftCost)
  let rightCost := EndpointCost.ofDyadic right
  if !rightCost.allowed limit then
    throw (.endpoint rightCost)
  let predicted :=
    match left, right with
    | .zero, _ | _, .zero => EndpointCost.ofDyadic 0
    | .ofOdd _ leftExponent _, .ofOdd _ rightExponent _ =>
        let exponentMagnitude := (leftExponent + rightExponent).natAbs
        { numeratorBits := leftCost.numeratorBits + rightCost.numeratorBits
          encodedExponentBits := EndpointCost.natBits exponentMagnitude
          exponentMagnitude }
  let cost : Growth := { sources := [leftCost, rightCost], predicted }
  if !cost.allowed limit then
    throw (.growth cost)
  pure cost

/-- Preflight a direct dyadic natural power without raising its mantissa.

The source endpoint is admitted before any products involving the exponent
are formed. The remaining calculations use arbitrary-precision natural-number
metadata, not fixed-width counters: a conservative numerator-bit count and the
exact magnitude of the result exponent. Numerators of absolute value one are
treated exactly, so powers of `1` and `-1` are not spuriously charged in
proportion to the exponent.

This is only a retained-endpoint growth prerequisite. It does not bound the
execution work of `Nat.pow` or conversion of the natural exponent into Core's
signed dyadic-exponent multiplication. In particular, a unit mantissa at
dyadic exponent zero can pass this growth check for an arbitrarily large
natural exponent. Public `powWithin` therefore composes this check with the
separate exponent/work limit before invoking `Dyadic.pow`. -/
def preflightPowGrowth (limit : EndpointLimit) (source : Dyadic)
    (exponent : Nat) :
    Except Cost Growth := do
  let sourceCost := EndpointCost.ofDyadic source
  if !sourceCost.allowed limit then
    throw (.endpoint sourceCost)
  let predicted :=
    match source with
    | .zero =>
        if exponent = 0 then EndpointCost.ofDyadic 1
        else EndpointCost.ofDyadic 0
    | .ofOdd numerator sourceExponent _ =>
        if exponent = 0 then EndpointCost.ofDyadic 1
        else
          let numeratorBits :=
            if numerator.natAbs = 1 then 1
            else sourceCost.numeratorBits * exponent
          let exponentMagnitude := sourceExponent.natAbs * exponent
          { numeratorBits
            encodedExponentBits := EndpointCost.natBits exponentMagnitude
            exponentMagnitude }
  let cost : Growth := { sources := [sourceCost], predicted }
  if !cost.allowed limit then
    throw (.growth cost)
  pure cost

/-- Transactional prerequisite for invoking Core direct dyadic power.

For a nonzero source, the actual `Nat` exponent is checked before the retained
growth preflight and before any call to `Dyadic.pow`; refusal has the distinct
`Cost.power` diagnostic. A successful result therefore authenticates both the
work cap and `preflightPowGrowth`'s source/result endpoint-growth boundary.

The zero source deliberately bypasses the exponent cap. Core's `Dyadic.pow`
zero branch only tests whether the exponent is zero and returns `1` or `0`; it
does not evaluate `Nat.pow`, convert the exponent to `Int`, or multiply a
dyadic exponent. This exception does not apply to either `1` or `-1`. -/
def preflightPow (endpointLimit : EndpointLimit) (workLimits : PowLimits)
    (source : Dyadic) (exponent : Nat) : Except Cost Growth :=
  match source with
  | .zero => preflightPowGrowth endpointLimit source exponent
  | .ofOdd _ _ _ => do
      let work : PowWork := { exponent }
      if !work.allowed workLimits then
        throw (.power work)
      preflightPowGrowth endpointLimit source exponent

/-! ## Reciprocal and division prerequisites -/

/-- Admit one retained source endpoint before any precision or rational work. -/
def admitEndpoint (limits : PrecisionLimits) (value : Dyadic) :
    Except Cost EndpointCost := do
  let cost := EndpointCost.ofDyadic value
  if !cost.allowed limits.endpoint then throw (.endpoint cost)
  pure cost

/-- Admit a signed precision before any rational conversion or shift metadata. -/
def admitPrecision (limits : PrecisionLimits) (precision : Precision) :
    Except Cost PrecisionCost := do
  let cost := PrecisionCost.ofPrecision precision
  if !cost.allowed limits then throw (.precision cost)
  pure cost

namespace QuotientCost

/-- Exact component bit lengths allocated by `Dyadic.toRat`, computed without
performing its power-of-two shift. The endpoint cost is derived from the same
value, so callers cannot pair unrelated cost and value records. -/
def conversionBound (value : Dyadic) : RationalBound :=
  let cost := EndpointCost.ofDyadic value
  match value with
  | .zero => { numeratorBits := 0, denominatorBits := 1 }
  | .ofOdd _ (.ofNat exponent) _ =>
      { numeratorBits := cost.numeratorBits, denominatorBits := exponent + 1 }
  | .ofOdd _ (.negSucc exponent) _ =>
      { numeratorBits := cost.numeratorBits + exponent + 1, denominatorBits := 1 }

/-- Swapping a reduced nonzero rational's components performs no allocation. -/
def invertBound (bound : RationalBound) : RationalBound :=
  { numeratorBits := bound.denominatorBits
    denominatorBits := bound.numeratorBits }

/-- Exact bit length of a nonzero integer multiplied by a power of two whose
bit length is `powerBits`. A zero integer remains zero. This helper is private:
its second-argument invariant is established only by `conversionBound`. -/
private def mulPowTwo (valueBits powerBits : Nat) : Nat :=
  if valueBits = 0 then 0 else valueBits + powerBits - 1

/-- Conservative bounds for `left / right` after `Rat.mul` performs its two
cross-gcd reductions and before either retained product is allocated.

`conversionBound` establishes structurally that every dyadic denominator is
an exact power of two (including one). Thus the unreduced numerator is the
left numerator times the right power-of-two denominator, and the unreduced
denominator is the left power-of-two denominator times the right numerator.
The private exact shift bound applies to precisely those products; gcd
reduction can only make their retained components smaller. -/
def divisionBound (left right : Dyadic) : RationalBound :=
  let leftBound := conversionBound left
  let rightBound := conversionBound right
  { numeratorBits := mulPowTwo leftBound.numeratorBits rightBound.denominatorBits
    denominatorBits := mulPowTwo rightBound.numeratorBits leftBound.denominatorBits }

/-- Bound the numerator/denominator shifted by Core `Rat.toDyadic`. Shifting a
zero numerator left preserves its zero-bit size at every positive precision. -/
def roundingBound (precision : Precision) (bound : RationalBound) : RationalBound :=
  match precision with
  | .ofNat shift =>
      { bound with
        numeratorBits := if bound.numeratorBits = 0 then 0 else bound.numeratorBits + shift }
  | .negSucc shift => { bound with denominatorBits := bound.denominatorBits + shift + 1 }

private def negative : Dyadic → Bool
  | .ofOdd (.negSucc _) _ _ => true
  | _ => false

/-- Bound the integer quotient passed to `Dyadic.ofIntWithPrec`. A positive
quotient has no more bits than the shifted rational numerator; flooring a
negative quotient may add one magnitude bit. -/
def boundQuotientBits (isNegative : Bool) (rounding : RationalBound) : Nat :=
  if rounding.numeratorBits = 0 then 0
  else rounding.numeratorBits + (if isNegative then 1 else 0)

/-- Bound the canonical result height after `Dyadic.ofIntWithPrec`. Removing
`t` trailing zeroes decreases numerator bits by `t` while changing exponent
magnitude by at most `t`, so quotient bits plus precision magnitude suffices. -/
def boundResultHeight (precision : Precision) (quotientBits : Nat) : Nat :=
  if quotientBits = 0 then 0 else quotientBits + precision.natAbs

end QuotientCost

/-- Preflight the public resource prerequisite for Core `Dyadic.invAtPrec`.
No rational conversion, shift, division, or result construction occurs here. -/
def preflightInv (limits : PrecisionLimits) (value : Dyadic)
    (precision : Precision) : Except Cost QuotientPlan := do
  let source ← admitEndpoint limits value
  match value with
  | .zero => pure (.zero [source])
  | _ =>
      let precisionCost ← admitPrecision limits precision
      let converted := QuotientCost.conversionBound value
      let rounding := QuotientCost.roundingBound precision (QuotientCost.invertBound converted)
      let quotientBits :=
        QuotientCost.boundQuotientBits (QuotientCost.negative value) rounding
      let cost : QuotientCost :=
        { sources := [source]
          precision := precisionCost
          converted := [converted]
          conversionShift := source.exponentMagnitude + precisionCost.magnitude
          crossProduct := none
          rounding
          quotientBits
          predictedResultHeight := QuotientCost.boundResultHeight precision quotientBits }
      if !cost.allowed limits then throw (.quotient cost)
      pure (.checked cost)

/-- Preflight the public resource prerequisite for Core `Dyadic.divAtPrec`.
Both retained sources are admitted before the denominator-zero short circuit.
For a nonzero denominator, the record bounds both `toRat` conversions, the
reduced rational cross-products, the precision shift, and the retained result.
No source conversion or arithmetic is executed here. -/
def preflightDiv (limits : PrecisionLimits) (left right : Dyadic)
    (precision : Precision) : Except Cost QuotientPlan := do
  let leftCost ← admitEndpoint limits left
  let rightCost ← admitEndpoint limits right
  match right with
  | .zero => pure (.zero [leftCost, rightCost])
  | _ =>
      let precisionCost ← admitPrecision limits precision
      let leftBound := QuotientCost.conversionBound left
      let rightBound := QuotientCost.conversionBound right
      let crossProduct := QuotientCost.divisionBound left right
      let rounding := QuotientCost.roundingBound precision crossProduct
      let quotientBits := QuotientCost.boundQuotientBits
        (QuotientCost.negative left != QuotientCost.negative right) rounding
      let cost : QuotientCost :=
        { sources := [leftCost, rightCost]
          precision := precisionCost
          converted := [leftBound, rightBound]
          conversionShift := leftCost.exponentMagnitude + rightCost.exponentMagnitude +
            precisionCost.magnitude
          crossProduct := some crossProduct
          rounding
          quotientBits
          predictedResultHeight := QuotientCost.boundResultHeight precision quotientBits }
      if !cost.allowed limits then throw (.quotient cost)
      pure (.checked cost)

end Hex.Interval.Arithmetic
