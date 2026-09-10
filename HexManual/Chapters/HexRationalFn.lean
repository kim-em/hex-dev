/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual
import HexRationalFnMathlib
import HexPolyFp.PrimeField
import Mathlib.Tactic.Ring

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "HexRationalFn: exact rational functions" =>
%%%
tag := "hex-rational-fn"
%%%

# Canonical fractions

A rational function stores coprime dense numerator and denominator polynomials,
with a monic denominator. Equality compares these canonical arrays; it does not
sample values. The computational library is Mathlib-free. Its companion identifies
the representation with Mathlib's `RatFunc`.

`normalize` requires a nonzero denominator; `ofFraction?` checks that condition.
Arithmetic cancels common factors before multiplying. Total field division sends
division by zero to zero; `div?` and `inv?` instead reject it.

# A two-stage recurrence

Consider initially resting stages with
`y[n] = a*y[n-1] + u[n]` and `w[n] = b*w[n-1] + y[n]`.
Write `X` for formal delay. Their formal generating-function equations are
`(1-aX)Y = U` and `(1-bX)W = Y`. Eliminating `Y` gives
`W = U/((1-aX)(1-bX))`. This algebraic derivation does not
assume convergence of a generating series.

```lean
namespace RationalFnRecurrence
theorem eliminate (A B U Y W : RatFunc ℚ)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hY : A * Y = U) (hW : B * W = Y) :
    W = U / (A * B) := by
  apply (eq_div_iff (mul_ne_zero hA hB)).2
  calc
    W * (A * B) = A * (B * W) := by ring
    _ = U := by rw [hW, hY]
end RationalFnRecurrence
```

For `a=1`, `b=2`, exact arithmetic verifies the transfer function
and a second cascade with a cancelling factor:

```lean
open Hex
namespace RationalFnCascade
def x : RationalFn Rat := RationalFn.X
def first : RationalFn Rat := 1 / (1 - x)
def second : RationalFn Rat := 1 / (1 - 2 * x)
#guard first * second = 1 / ((1 - x) * (1 - 2 * x))
#guard ((1 - x) / (1 - 2 * x)) * first = second
end RationalFnCascade
```

Cancellation identifies the rational transfer function. It does not establish
internal stability, preserve hidden state, or cover nonzero initial conditions.

# Removed factors and excluded inputs

The expression `(X²-1)/(X-1)` excludes `X=1`. Its rational function is
`X+1`, whose canonical denominator is one. The original expression's exclusion
is not stored in the rational function:

```lean
open Hex
namespace RationalFnDomain
def p : DensePoly Rat := #p[-1, 0, 1]
def q : DensePoly Rat := #p[-1, 1]
#guard q.eval 1 = 0
#guard (RationalFn.ofFraction? p q).map
  (fun f => RationalFn.eval? f 1) = some (some 2)
#guard RationalFn.eval?
  (1 / (RationalFn.X : RationalFn Rat)) 0 = none
#guard RationalFn.div? (0 : RationalFn Rat) 0 = none
end RationalFnDomain
```

`eval?` returns `none` at a canonical pole. In contrast, Mathlib's total
`RatFunc.eval` returns zero there. The companion's `eval?_eq_some` theorem
therefore includes nonvanishing of the canonical denominator.

# Finite fields are not sample-based equality

Over the field with two elements, `X²-X` is nonzero but vanishes at every
field element. Meanwhile the derivative of `X²` vanishes:

```lean
open Hex
namespace RationalFnFinite
instance : ZMod64.Bounds 2 := ⟨by decide, by decide⟩
instance : ZMod64.PrimeModulus 2 :=
  ZMod64.primeModulusOfPrime (by decide)
def x : RationalFn (ZMod64 2) := RationalFn.X
#guard x ^ (2 : Nat) - x ≠ 0
#guard ([0, 1] : List (ZMod64 2)).all
  (fun a => RationalFn.eval?
    (x ^ (2 : Nat) - x) a == some 0)
#guard RationalFn.derivative (x ^ (2 : Nat)) = 0
end RationalFnFinite
```

# Certificates and the Mathlib boundary

`certifyWith` produces a canonical pair and Bézout witnesses.
`check` checks input validity, monicity, fraction equality and the Bézout identity.
Kernel replay uses `check_sound`; it does not rerun gcd search.

The companion exports `equiv` and `algEquiv`. Its `normalize_spec` identifies
both the fraction and its canonical numerator and denominator. Use the
lightweight field instance induced by the same Mathlib coefficient field;
a local priority for `Field.toGrindField` makes this choice explicit in
concrete-field proofs.
