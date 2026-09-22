/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ.IntegerPolynomial

public section

/-!
Basic data for real root isolation: the half-open dyadic interval type,
exact dyadic Horner evaluation of an integer polynomial, and the exact
sign of a dyadic value.

Every witness in this library is an exact comparison between dyadic
values or integer counts; there is no rounding and no error budget.
`Dyadic` comes from Lean core (`Init.Data.Dyadic`).
-/
namespace Hex

/-- A half-open dyadic interval `(lower, upper]`.

The isolation convention throughout the library is half-open on the
left: a root at `upper` belongs to the interval, a root at `lower` does
not. This is what makes bisection at a midpoint have no endpoint case
analysis — a root exactly at the midpoint `m` lands in the left child
`(lower, m]`. The `lt` field records that the interval is nonempty. -/
structure DyadicInterval where
  /-- The excluded left endpoint. -/
  lower : Dyadic
  /-- The included right endpoint. -/
  upper : Dyadic
  /-- The interval is nonempty: `lower < upper`. -/
  lt : lower < upper

/-- The dyadic midpoint `(lower + upper) / 2` of the interval, computed
by an exact arithmetic right shift of the sum by one bit. -/
def DyadicInterval.midpoint (I : DyadicInterval) : Dyadic :=
  (I.lower + I.upper) >>> (1 : Int)

/-- The exact width `upper - lower` of the interval. -/
def DyadicInterval.width (I : DyadicInterval) : Dyadic :=
  I.upper - I.lower

/-- The exact sign of a dyadic value as an integer in `{-1, 0, 1}`.

A nonzero dyadic is `ofOdd n k` with `n` odd, and its sign is the sign
of the odd numerator `n` (the power-of-two scale `2^{-k}` is positive),
so no evaluation is needed. -/
@[expose]
def dyadicSign : Dyadic → Int
  | .zero => 0
  | .ofOdd n _ _ => if n < 0 then -1 else 1

namespace ZPoly

/-- One Horner operation on an unnormalized numerator and binary precision.
The pair `(a, k)` represents `a * 2^(-k)`. Zero accumulators discard the
precision, so constants and exact cancellations do not shift by an unused
endpoint exponent. Zero coefficients retain the signed precision without
materializing powers of two, including at enormous integral endpoints. -/
@[expose] def hornerDyadic (n e c : Int) (acc : Int × Int) : Int × Int :=
  if acc.1 = 0 then (c, 0)
  else
    let k := acc.2 + e
    if c = 0 then (n * acc.1, k)
    else if 0 ≤ k then ((c <<< k.toNat) + n * acc.1, k)
    else (c + ((n * acc.1) <<< (-k).toNat), 0)

/-- Evaluate an integer polynomial at a dyadic point by Horner's rule,
returning an exact `Dyadic` value.

At integer points, the array fold carries an integer numerator and binary
precision, normalizing only the final result. At fractional points, ordinary
dyadic arithmetic normalizes intermediate values to avoid accumulating
cancellable powers of two.
Coefficients are stored in ascending degree order. -/
@[expose]
def evalDyadic (p : ZPoly) (x : Dyadic) : Dyadic :=
  let (n, e) := match x with
    | .zero => (0, 0)
    | .ofOdd n e _ => (n, e)
  -- TODO: When the toolchain includes the fix for https://github.com/leanprover/lean4/issues/15264,
  -- verify that Dyadic.ofIntWithPrec uses the faster trailing-zero counter.
  -- On that toolchain, compare this split with normalized Horner at all points
  -- using Hex.RealRootsBench.runCancellation and Hex.SturmBench.runReplay; simplify
  -- if the integer specialization no longer helps. Keep intermediate fractional
  -- normalization: a faster final count alone does not prevent numerator growth.
  if 0 < e then
    p.toArray.foldr (fun c acc => Dyadic.ofInt c + x * acc) 0
  else
    let (a, k) := p.toArray.foldr (hornerDyadic n e) (0, 0)
    Dyadic.ofIntWithPrec a k

end ZPoly

/-! Sanity checks (kept light; conformance lives in the shared
sub-project). -/

-- `x² − 1` evaluated at `3/2` is `9/4 − 1 = 5/4`.
example : ZPoly.evalDyadic (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    ((Dyadic.ofInt 3) >>> (1 : Int)) = (Dyadic.ofInt 5) >>> (2 : Int) := by decide

-- The constant polynomial `7` evaluates to `7` at any point.
example : ZPoly.evalDyadic (DensePoly.ofCoeffs #[(7 : Int)]) (Dyadic.ofInt 4)
    = Dyadic.ofInt 7 := by decide

-- Signs of `-3/2`, `0`, `5/4`.
example : dyadicSign ((Dyadic.ofInt (-3)) >>> (1 : Int)) = -1 := by decide
example : dyadicSign 0 = 0 := by decide
example : dyadicSign ((Dyadic.ofInt 5) >>> (2 : Int)) = 1 := by decide

-- The midpoint of `(1, 2]` is `3/2`; its width is `1`.
example : (DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 2) (by decide)).midpoint
    = (Dyadic.ofInt 3) >>> (1 : Int) := by decide
example : (DyadicInterval.mk (Dyadic.ofInt 1) (Dyadic.ofInt 2) (by decide)).width
    = Dyadic.ofInt 1 := by decide

-- The zero polynomial evaluates to `0` everywhere.
example : ZPoly.evalDyadic (DensePoly.ofCoeffs (#[] : Array Int)) (Dyadic.ofInt 5)
    = 0 := by decide

-- `x² − 1` at the negative point `−1/2` is `1/4 − 1 = −3/4`.
example : ZPoly.evalDyadic (DensePoly.ofCoeffs #[(-1 : Int), 0, 1])
    ((Dyadic.ofInt (-1)) >>> (1 : Int)) = (Dyadic.ofInt (-3)) >>> (2 : Int) := by decide

-- A nonzero polynomial hitting an exact zero: `x − 1` at `1`.
example : ZPoly.evalDyadic (DensePoly.ofCoeffs #[(-1 : Int), 1]) (Dyadic.ofInt 1)
    = 0 := by decide

-- The midpoint of the negative interval `(−2, −1]` is `−3/2`.
example : (DyadicInterval.mk (Dyadic.ofInt (-2)) (Dyadic.ofInt (-1)) (by decide)).midpoint
    = (Dyadic.ofInt (-3)) >>> (1 : Int) := by decide

end Hex
