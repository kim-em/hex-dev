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
public interval operations continue to return `BuildResult`; multiplicative
operations can report growth without fabricating a `CompareCost`. Concrete
corner enumeration and interval multiplication live in
`HexInterval.Multiplication`, not in this reusable cost layer; direct-power
preflight remains a prerequisite rather than a public interval-power API.
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

/-- Execution-work limit for a future direct natural-power operation. The cap
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

/-- Resource diagnostics for checked public arithmetic. Product growth is a
separate case from endpoint and comparison work: a comparison between two
admitted factors may be cheap even when their product is too large. Direct
power execution work is also reported separately from retained growth. -/
inductive Cost where
  | endpoint (cost : EndpointCost)
  | comparison (cost : CompareCost)
  | growth (cost : Growth)
  | power (work : PowWork)
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
natural exponent. A future public power operation must enforce a separate
exponent/work limit before invoking `Dyadic.pow`. -/
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

end Hex.Interval.Arithmetic
