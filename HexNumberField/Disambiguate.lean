/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Lazy
public meta import HexNumberField.Lazy

public section

/-!
Finite-precision disambiguation of candidate algebraic roots.

An evaluation eliminant supplies a reciprocal-Cauchy lower bound for every
nonzero value. A conservative Horner majorant turns that lower bound into an
input-computable endpoint, and the search below chooses the first precision at
which the certified evaluation ball is small enough to distinguish zero from
nonzero. No caller performs unbounded refinement.
-/
namespace Hex

namespace ZPoly

/-- Remove zero roots and content from a candidate-evaluation eliminant. -/
@[expose]
def normalizeEval (q : ZPoly) : ZPoly :=
  primitivePart q.removeX

/-- Denominator in the reciprocal-Cauchy lower bound
`|z| ≥ 1 / (1 + height q)` for a nonzero root `z` of the normalized
evaluation eliminant. -/
@[expose]
def evalLowerDenom (q : ZPoly) : Nat :=
  1 + coeffAbsMax q.normalizeEval

end ZPoly

namespace Disambiguation

/-- Error-amplification majorant for Horner evaluation at a root of `q`,
parameterized by an integer magnitude bound on coefficients so tower elements
can reuse the same recurrence. The factor two on the root bound covers the
`|re| + |im|` centre magnitude used by complex-ball multiplication; the three
extra propagated-error units cover centre-radius conversion and the bilinear
radius term. -/
@[expose]
def evalMajorant {A : Type} [Zero A] [DecidableEq A]
    (f : DensePoly A) (valueBound : A → Nat) (q : ZPoly) : Nat :=
  let rootBound := 2 ^ cauchyExp q + 1
  let state := f.toArray.foldr
    (fun coeff state =>
      let value := state.1 * rootBound + valueBound coeff
      let error :=
        2 * state.1 + 2 * rootBound * state.2 + 3 * state.2 + 1
      (value, error))
    (0, 0)
  Nat.max 1 state.2

end Disambiguation

namespace QAdjoin

/-- Ceiling of the absolute value of a rational, computed with integer
arithmetic. -/
@[expose]
def ratAbsCeil (q : Rat) : Nat :=
  (q.num.natAbs + q.den - 1) / q.den

/-- Integer magnitude majorant for a fixed-field coordinate evaluated at any
root of its defining polynomial. -/
@[expose]
def valueMajorant {p : ZPoly} {x : SimpleRoot p} (a : QAdjoin p x) : Nat :=
  let rootBound := 2 ^ cauchyExp p + 1
  a.coeffs.toArray.foldr
    (fun coeff acc => acc * rootBound + ratAbsCeil coeff) 0

/-- Error-amplification majorant for Horner evaluation at a root of `q`.

The state tracks a value bound `V` and a coefficient of the common input
error `E`. For `(acc * y) + c`, coefficient errors are at most one nominal
unit. The update `E' = 2*V + 2*B*E + 3*E + 1` covers root error, the
`|re| + |im|` inflation in propagated accumulator error, their product, and
coefficient error. -/
@[expose]
def evalMajorant {p : ZPoly} {x : SimpleRoot p}
    (f : DensePoly (QAdjoin p x)) (q : ZPoly) : Nat :=
  Disambiguation.evalMajorant f valueMajorant q

end QAdjoin

/-- The specified finite search endpoint
`ceilLog2(ceil(2 * (1 + height(q)) * C)) + 2`. All inputs are integral, so
the displayed ceiling is already exact. -/
@[expose]
def evalDisambiguationLimit (q : ZPoly) (majorant : Nat) : Nat :=
  ceilLog2 (2 * q.evalLowerDenom * Nat.max 1 majorant) + 2

/-- The evaluation radius is below one third of the reciprocal-Cauchy lower
bound, written without division as `3 * D * radius < 1`. The factor three is
needed because {name}`Hex.DyadicComplexBall.excludesZero` uses the centre's
maximum coordinate, which can
be a factor `sqrt 2` below its Euclidean norm. -/
@[expose]
def evalRadiusSmall (q : ZPoly) (radius : Dyadic) : Bool :=
  decide (((3 * q.evalLowerDenom : Nat) : Dyadic) * radius < 1)

/-- Least precision in the finite prescribed range whose certified Horner
ball has sufficiently small radius. A failed ball construction is skipped;
the companion proves that the endpoint succeeds for the shipped evaluators. -/
@[expose]
def evalDisambiguationPrec (q : ZPoly) (majorant : Nat)
    (evalAt : Nat → Option DyadicComplexBall) : Option Nat :=
  let limit := evalDisambiguationLimit q majorant
  (List.range (limit + 1)).findSome? fun prec => do
    let ball ← evalAt prec
    if evalRadiusSmall q ball.radius then some prec else none

/-- Decide whether a candidate evaluation can be zero. A zero eliminant is
retained immediately. Otherwise evaluate at the first sufficiently small
precision and retain exactly when the certified ball does not exclude zero. -/
@[expose]
def retainZero? (q : ZPoly) (majorant : Nat)
    (evalAt : Nat → Option DyadicComplexBall) : Option Bool :=
  if q.normalizeEval.isZero then
    some true
  else do
    let prec ← evalDisambiguationPrec q majorant evalAt
    let ball ← evalAt prec
    some (!ball.excludesZero)

/-! Compiled bound and bounded-search checks. -/

#guard
    let q : ZPoly := DensePoly.ofList [0, 0, -6, 12]
    q.normalizeEval = DensePoly.ofList [-1, 2] &&
      q.evalLowerDenom = 3

#guard
    let q : ZPoly := DensePoly.ofList [-1, 1]
    let f : DensePoly Nat := DensePoly.ofList [1, 2]
    Disambiguation.evalMajorant f id q = 14

#guard
    let q : ZPoly := DensePoly.ofList [-1, 1]
    let evalAt := fun prec : Nat =>
      some ({ re := 0, im := 0, radius := Dyadic.ofIntWithPrec 1 prec } :
        DyadicComplexBall)
    evalDisambiguationLimit q 8 = 7 &&
      evalDisambiguationPrec q 8 evalAt = some 3 &&
      retainZero? q 8 evalAt = some true

#guard
    let zeroEval : ZPoly := 0
    retainZero? zeroEval 1 (fun _ => none) = some true

#guard
    let q : ZPoly := DensePoly.ofList [-1, 1]
    let evalAt := fun prec : Nat =>
      some ({ re := 1, im := 0, radius := Dyadic.ofIntWithPrec 1 prec } :
        DyadicComplexBall)
    retainZero? q 8 evalAt = some false

end Hex
