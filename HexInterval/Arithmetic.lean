/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Canonical

@[expose] public section

/-!
# Arithmetic resource preflight

Endpoint comparison cost does not bound numerator growth in multiplication.
This module supplies a separate, nonbreaking result and diagnostic layer for
checked arithmetic. Existing constructors and the additive public operations
continue to return `BuildResult`; multiplicative operations can report product
growth without fabricating a `CompareCost`.
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

/-- Resource diagnostics for checked public arithmetic. Product growth is a
separate case from endpoint and comparison work: a comparison between two
admitted factors may be cheap even when their product is too large. -/
inductive Cost where
  | endpoint (cost : EndpointCost)
  | comparison (cost : CompareCost)
  | growth (cost : Growth)
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
def ofBuild : BuildResult → Result
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

end Hex.Interval.Arithmetic
