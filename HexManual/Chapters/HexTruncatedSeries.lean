/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import VersoManual
public import HexTruncatedSeriesMathlib

import all HexTruncatedSeries.Classes
import all HexTruncatedSeries.Comp
import all HexTruncatedSeries.Defs
import all HexTruncatedSeries.ExpLog
import all HexTruncatedSeries.Inverse
import all HexTruncatedSeries.Precision
import all HexTruncatedSeries.Revert
import all HexTruncatedSeries.Ring
import all HexTruncatedSeries.Sqrt
import all HexTruncatedSeriesMathlib.Basic
import all HexTruncatedSeriesMathlib.Newton
import all HexTruncatedSeriesMathlib.Ops
public meta import HexTruncatedSeries.Defs
public meta import HexTruncatedSeries.Precision
public meta import HexTruncatedSeries.Ring
public meta import HexTruncatedSeries.Newton

public section

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexTruncatedSeries: power series to a fixed precision" =>
%%%
tag := "hex-truncated-series"
%%%

# Introduction
%%%
tag := "hex-truncated-series-intro"
%%%

A formal power series `a₀ + a₁x + a₂x² + ⋯` over a commutative ring `R` has
infinitely many coefficients, and a program can hold only finitely many of
them. `HexTruncatedSeries` computes with the first `n` coefficients, for an
`n` fixed in the type: a value of type `TSeries R n` is a power series modulo
`xⁿ`. Besides the ring operations, it provides the classical operations on
power series: inverse, square root, exponential, logarithm, substitution of
one series into another, and the compositional inverse. Every coefficient it
returns is exact.

Generating functions are the most direct use. Euler showed that the number
`p(k)` of partitions of `k` is the coefficient of `xᵏ` in

`1 / ((1 - x)(1 - x²)(1 - x³)⋯)`.

Modulo `x³⁰` only the first 29 factors matter, and inverting their product
gives `p(0), p(1), …, p(29)`. Here `X` is the indeterminate `x`, and
`.coeffs` is the vector of coefficients in increasing degree:

```lean
open Hex Hex.TSeries

namespace HexTruncatedSeriesChapter

/-- `(1 - x)(1 - x²)⋯(1 - xⁿ⁻¹)` at precision `n`. -/
def euler (n : Nat) : TSeries Int n :=
  (List.range (n - 1)).foldl
    (fun acc j => acc * (1 - X ^ (j + 1))) 1

def partitions : TSeries Int 30 :=
  invOfUnit (euler 30) 1
```

```lean (name := tsPartitions)
#eval partitions.coeffs
```
```leanOutput tsPartitions
#v[1, 1, 2, 3, 5, 7, 11, 15, 22, 30, 42, 56, 77, 101, 135, 176, 231, 297, 385, 490, 627, 792, 1002, 1255, 1575, 1958,
   2436, 3010, 3718, 4565]
```

Here `invOfUnit a u` inverts `a`, given an inverse `u` of its constant
coefficient; the constant coefficient of Euler's product is `1`. The inverse
is computed by Newton's method, which doubles the number of correct
coefficients at each step, and needs no division in `R` beyond the one the
caller supplies. So it works over `ℤ`, and so does the compositional inverse.
The exponential and logarithm divide by `1, 2, …, n - 1`, and their types say
so; see {ref "hex-truncated-series-exp-log"}[Exponential and logarithm].

`HexTruncatedSeries` depends only on {ref "hex-basic"}[`HexBasic`], and not on
Mathlib; import it to compute. Its coefficient rings are instances of
`Lean.Grind.CommRing`, which every Mathlib `CommRing` provides. The companion
`HexTruncatedSeriesMathlib`, which imports Mathlib, proves that `TSeries R n`
is the quotient of Mathlib's `PowerSeries R` by the ideal `(Xⁿ)`, and that
the operations with a Mathlib counterpart agree with it; import it to prove
theorems about Mathlib's power series. See
{ref "hex-truncated-series-mathlib"}[The Mathlib correspondence].

# Series and their coefficients
%%%
tag := "hex-truncated-series-representation"
%%%

{docstring Hex.TSeries}

{name}`Hex.TSeries.coeff` reads coefficients: `a.coeff i` is the coefficient
of `xⁱ`, and is `0` when `i ≥ n`. That `0` is a convention which keeps
statements about coefficients short. It does not say that the series being
approximated has a zero coefficient there, only that `a` does not record it.
{name}`Hex.TSeries.ofFn` builds a series from a function giving its
coefficients, {name}`Hex.TSeries.C` makes a constant series, and
{name}`Hex.TSeries.X` is the series `x`. The usual notation `+`, `-`, `*`,
`^` and numerals is available, and multiplication discards every term of
degree `n` or more. Two series are equal when their `n` coefficients agree
({name}`Hex.TSeries.ext`), and equality is decidable when it is decidable in
`R`. For example, `(1 - x)(1 + x + x² + ⋯) = 1`:

```lean
def ones : TSeries Int 8 := ofFn fun _ => 1
#guard ones * (1 - X) = 1
```

Euler's product from the introduction has the coefficients of the pentagonal
number theorem: apart from the constant coefficient `1`, the nonzero ones sit
at the pentagonal numbers `k(3k - 1)/2` and `k(3k + 1)/2` for `k ≥ 1`, that is
`1, 2, 5, 7, 12, 15, 22, 26, …`, and they are `(-1)ᵏ`:

```lean (name := tsEuler)
#eval (euler 30).coeffs
```
```leanOutput tsEuler
#v[1, -1, -1, 0, 0, 1, 0, 1, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]
```

The operations below are total functions. Where an operation only makes sense
under a hypothesis, such as a zero constant coefficient for `exp`, the
function does not check it: it returns some series in every case, and the
theorems about it carry the hypothesis. Where checking is possible, an
`Option`-valued form such as `inv?` or `comp?` checks the hypothesis and
returns `none` when it fails.

Precisions `0` and `1` are allowed. `TSeries R 0` is the zero ring, in which
every element is a unit and has a square root. The hypotheses of the theorems
below are stated so that they remain true there: the theorems about the
logarithm, for example, assume `(a - 1).coeff 0 = 0` rather than
`a.coeff 0 = 1`, which would be false at precision `0`.

# Changing the precision
%%%
tag := "hex-truncated-series-precision"
%%%

{name}`Hex.TSeries.truncate` keeps the coefficients below a smaller
precision `m`. It is a ring homomorphism, so a computation at precision `n`
also gives the answer at every smaller precision:

{docstring Hex.TSeries.truncate_mul}

{name}`Hex.TSeries.extend` goes the other way, padding with zeros to a larger
precision. It is not a ring homomorphism, because it asserts that the
coefficients it does not know are zero. At precision `2` the product `x · x`
is `0`, while after extending to precision `3` it is `x²`:

```lean
def x2 : TSeries Int 2 := X
def x3 : TSeries Int 3 := x2.extend 3 (by decide)
#guard x2 * x2 = 0
#guard x3 * x3 ≠ (x2 * x2).extend 3 (by decide)
```

So `extend` gives the right answer when the missing coefficients are known to
vanish, for example for a polynomial of degree less than `n`.
{name}`Hex.TSeries.mulXPow` multiplies by `xᵏ`, discarding the top `k`
coefficients. {name}`Hex.TSeries.divXPow?` divides by `xᵏ`, and returns
`none` unless the bottom `k` coefficients are zero; its result has precision
`n - k`, since the top `k` coefficients of the quotient are unknown.
{name}`Hex.TSeries.valuation?` finds the first nonzero coefficient, and
returns `none` for the zero series:

```lean
def shifted : TSeries Int 6 := X ^ 2 * (3 + X)
```

```lean (name := tsDivide)
#eval (shifted.valuation?,
  (shifted.divXPow? 2).map (·.coeffs),
  (shifted.divXPow? 3).map (·.coeffs))
```
```leanOutput tsDivide
(some 2, some #v[3, 1, 0, 0], none)
```

The derivative {name}`Hex.TSeries.deriv` also loses precision: the
coefficient of `xⁿ⁻¹` in the derivative is `n aₙ`, and `aₙ` is not known, so
the derivative of a series of precision `n` has precision `n - 1`.
{name}`Hex.TSeries.integrate` gains one, returning the integral with
constant coefficient `0` at precision `n + 1`. It divides the coefficient of
`xᵏ⁻¹` by `k` for `k = 1, …, n`, and so needs those inverses in `R`, which are
supplied by an instance of {name}`Hex.TSeries.NatInverses`:

{docstring Hex.TSeries.NatInverses}

In each case the loss or gain of precision is part of the type. A caller who
needs `n` coefficients of a derivative computes at precision `n + 1`.

# Inverses and Newton's method
%%%
tag := "hex-truncated-series-newton"
%%%

For `n ≥ 1`, a series is a unit of `TSeries R n` exactly when its constant
coefficient is a unit of `R`.

{docstring Hex.TSeries.invOfUnit}

If `b` inverts `a` modulo `xᵏ`, then `b(2 - ab)` inverts `a` modulo `x²ᵏ`.
`invOfUnit a u` starts from the constant `u` and applies this step
`⌈log₂ n⌉` times. The step that reaches precision `2k` computes its products
only below `x²ᵏ`, using {name}`Hex.TSeries.mulUpTo`. Each step then costs
about a quarter of the step after it, and the whole inverse costs a constant
multiple of a single multiplication at precision `n`. The library
proves that the result is an inverse, and that it is the only one:

{docstring Hex.TSeries.invOfUnit_mul}

{docstring Hex.TSeries.invOfUnit_unique}

`invOfUnit` does not check its witness. Given a `u` that does not invert the
constant coefficient it returns some series, and the theorems above say
nothing about it. {name}`Hex.TSeries.inv?` finds the witness itself, using a
{name}`Hex.TSeries.UnitOps` instance on `R`. When the lookup is also lawful,
that is, it finds an inverse exactly for the units of `R`
({name}`Hex.TSeries.LawfulUnitOps`), `inv?` returns `none` exactly when the
series is not a unit ({name}`Hex.TSeries.inv?_isSome_iff`). The library
provides lawful instances for `Int` and `Rat`. The series `2 - x` is not a
unit over
`ℤ`, and over `ℚ` its inverse is `1/2 + x/4 + x²/8 + ⋯`:

```lean
def twoMinusX : TSeries Int 5 := 2 - X
def twoMinusXQ : TSeries Rat 5 := 2 - X
```

```lean (name := tsInverse)
#eval ((inv? twoMinusX).map (·.coeffs),
  (inv? twoMinusXQ).map (·.coeffs))
```
```leanOutput tsInverse
(none, some #v[(1 : Rat)/2, (1 : Rat)/4, (1 : Rat)/8, (1 : Rat)/16, (1 : Rat)/32])
```

The square root, exponential and compositional inverse below are computed by
Newton's method in the same way, with the same bounded steps.

# Square roots
%%%
tag := "hex-truncated-series-sqrt"
%%%

A square root of a series is determined by its constant coefficient, as long
as `2` times that coefficient is a unit. So the caller chooses a square root
`r` of the constant coefficient, and supplies an inverse `v` of `2r`:

{docstring Hex.TSeries.sqrtOfRoot}

{docstring Hex.TSeries.sqrtOfRoot_sq}

{docstring Hex.TSeries.sqrt_unique}

The generating function `c(x) = Σ Cₖ xᵏ` of the Catalan numbers satisfies
`c = 1 + x c²`, so `x c(x) = (1 - √(1 - 4x))/2`, taking the square root with
constant coefficient `1`:

```lean
def catalanSqrt : TSeries Rat 10 :=
  C (1 / 2) * (1 - sqrtOfRoot (1 - 4 * X) 1 (1 / 2))
```

```lean (name := tsCatalanSqrt)
#eval catalanSqrt.coeffs
```
```leanOutput tsCatalanSqrt
#v[0, 1, 1, 2, 5, 14, 42, 132, 429, 1430]
```

Neither half of the condition that `2r` is a unit can be dropped. Over
`ℤ/2ℤ`, where `r = 1` is a unit but `2` is not, `1 + x` has no square root at
precision `2`, since `(1 + bx)² = 1 + b²x²`. Over `ℤ/9ℤ`, where `2` is a unit
but `r = 3` is not, `x` has no square root with constant coefficient `3` at
precision `2`, since `(3 + bx)² = 6bx` and `6b = 1` has no solution.

The square root is computed by Newton's method for the inverse square root
`z = 1/√a`, with the step `z ↦ z(3 - az²)/2`, starting from `1/r`; the result
is `az`. This needs no inversion of a series at any step.

{name}`Hex.TSeries.sqrt?` checks that `r² = a₀` and, from precision `2` on,
looks up the inverse of `2r` with `UnitOps`. (At precision `1` the answer is
the constant `r`, and at precision `0` there is nothing to check.) Over `ℤ`
it fails on `1 - 4x`, because `2` is not a unit
of `ℤ`, even though the square root `1 - 2x - 2x² - 4x³ - ⋯` has integer
coefficients:

```lean (name := tsSqrtInt)
#eval (sqrt? (1 - 4 * X : TSeries Int 10) 1).map
  (·.coeffs)
```
```leanOutput tsSqrtInt
none
```

The library never looks for `r` itself. Finding a square root in `R` is a
question about `R` (over `ℤ/pℤ` for an odd prime `p` it is the Tonelli–Shanks
algorithm), and the choice matters: when `2r` is a unit in a nonzero ring,
`r` and `-r` give different square roots.
The Catalan numbers over `ℤ` come from the compositional inverse instead; see
{ref "hex-truncated-series-composition"}[Composition and reversion].

# Exponential and logarithm
%%%
tag := "hex-truncated-series-exp-log"
%%%

For a series `a` with constant coefficient `0` at precision `n`,
`exp a = Σ_{k<n} aᵏ/k!` (the terms with `k ≥ n` vanish), and for a
series `a` with constant coefficient `1`, `log a` is the integral of `a′/a`
with constant coefficient `0`. At precision `n` both need the inverses of
`1, …, n - 1` in `R`, and nothing more, so both take an instance of
`NatInverses R (n - 1)`:

{docstring Hex.TSeries.exp}

{docstring Hex.TSeries.log}

Every ring has `NatInverses R 0` and `NatInverses R 1`, `Rat` has
`NatInverses Rat m` for every `m`, and `HexTruncatedSeriesMathlib` provides
an instance for every `ℚ`-algebra. Over `ℤ`, then, `exp` and `log` exist at
precision at most `2`, and `exp (X : TSeries Int 3)` does not typecheck, since
`exp x = 1 + x + x²/2 + ⋯`. Over `ℤ/pℤ` with `p` prime, the inverses of
`1, …, n - 1` exist exactly when `n ≤ p`, so `exp` and `log` make sense up to
precision `p`, where Mathlib's exponential, which needs a `ℚ`-algebra, does
not exist. This library does not depend on a type of integers modulo `p`, so
an instance for one has to come from the code that uses it.

The exponential generating function of the Bell numbers, which count the
partitions of a set of `k` elements, is `exp(eˣ - 1)`:

```lean
def bellEGF : TSeries Rat 10 := exp (exp X - 1)

def factorial : Nat → Nat
  | 0 => 1
  | k + 1 => (k + 1) * factorial k
```

```lean (name := tsBell)
#eval (List.range 10).map fun k =>
  (factorial k : Rat) * bellEGF.coeff k
```
```leanOutput tsBell
[1, 1, 2, 5, 15, 52, 203, 877, 4140, 21147]
```

Taking the logarithm of Euler's generating function for partitions,

`log ∏ⱼ 1/(1 - xʲ) = Σⱼ Σₘ xʲᵐ/m`,

so for `k ≥ 1`, `k` times the coefficient of `xᵏ` is the sum `σ(k)` of the
divisors of `k` (the first entry printed is the constant coefficient, `0`):

```lean
def partitionsQ : TSeries Rat 30 :=
  ofFn fun i => (partitions.coeff i : Rat)
```

```lean (name := tsSigma)
#eval (List.range 30).map fun (k : Nat) =>
  (k : Rat) * (log partitionsQ).coeff k
```
```leanOutput tsSigma
[0, 1, 3, 4, 7, 6, 12, 8, 15, 13, 18, 12, 28, 14, 24, 24, 31, 18, 39, 20, 42, 32, 36, 24, 60, 31, 42, 40, 56, 30]
```

The logarithm is computed directly from its definition, with one inverse, one
derivative, one product and one integral. The exponential is computed by
Newton's method applied to `log y = a`, with the step
`y ↦ y(1 + a - log y)`, taking one logarithm at each step. The library proves
the functional equations:

{docstring Hex.TSeries.log_exp}

{docstring Hex.TSeries.exp_log}

{docstring Hex.TSeries.exp_add}

# Composition and reversion
%%%
tag := "hex-truncated-series-composition"
%%%

{name}`Hex.TSeries.comp` substitutes one series into another. When `b` has
constant coefficient `0`, `comp a b = a(b(x)) = Σₖ aₖ bᵏ`, where only
`k < n` matters because `bᵏ` is divisible by `xᵏ`. When `b` has a nonzero
constant coefficient `c`, the constant coefficient of `a(b(x))` would be the
infinite sum `Σ aₖ cᵏ`, which has no meaning in a general ring.

{docstring Hex.TSeries.comp_spec}

The sum is evaluated by the algorithm of Brent and Kung. With `s` about `√n`,
it splits `a` into blocks of `s` coefficients, computes the powers
`b⁰, b¹, …, bˢ` once, evaluates each block as a linear combination of those
powers, and combines the blocks by Horner's rule in `bˢ`. This takes about
`2√n` multiplications of series, and `n²` multiplications of coefficients to
form the blocks. Horner's rule in `b` itself, available as
{name}`Hex.TSeries.compHorner`, takes `n` multiplications of series. The
exponential generating function of the Bell numbers is a composition:

```lean
#guard comp (exp X) (exp X - 1) = bellEGF
```

When `b` has constant coefficient `0` and linear coefficient a unit, it has a
compositional inverse: a series `y` with `b(y(x)) = x`, and then also
`y(b(x)) = x`. {name}`Hex.TSeries.revOfUnit` computes it, given an inverse of
the linear coefficient:

{docstring Hex.TSeries.revOfUnit}

{docstring Hex.TSeries.revOfUnit_comp}

It uses Newton's method for the equation `b(y) = x`, with the step
`y ↦ y - (b(y) - x)/b′(y)`. The only division is by `b′(y)`, whose constant
coefficient is the linear coefficient of `b`, so no other division is needed
and reversion works over `ℤ`. The Catalan series `y = x c(x)` satisfies
`y = x + y²`, so it is the compositional inverse of `x - x²`:

```lean (name := tsCatalanRev)
#eval (revOfUnit (X - X ^ 2 : TSeries Int 10) 1).coeffs
```
```leanOutput tsCatalanRev
#v[0, 1, 1, 2, 5, 14, 42, 132, 429, 1430]
```

Lagrange's inversion formula gives the coefficients of the compositional
inverse directly: for `1 ≤ k < n`, `[xᵏ] y = (1/k) [xᵏ⁻¹] (x/b)ᵏ`, where
`x/b` is the inverse of the unit series `b/x`. Evaluated as written, it
divides by `k`, so {name}`Hex.TSeries.revLagrange`, which evaluates it, needs
`NatInverses R (n - 1)`. The library proves that the two agree whenever both
apply:

{docstring Hex.TSeries.revLagrange_eq}

A rooted tree whose `k` vertices are labelled `1, …, k` is a root together
with a set of rooted trees on the other labels, so the exponential generating
function `T` of such trees satisfies `T = x eᵀ`. So `T` is the compositional
inverse of `x e⁻ˣ`, and for `k ≥ 1` its coefficients recover Cayley's
formula `kᵏ⁻¹`:

```lean
def trees : TSeries Rat 10 :=
  revOfUnit (X * exp (-X)) 1
#guard revLagrange (X * exp (-X)) 1 = trees
```

```lean (name := tsCayley)
#eval (List.range 10).map fun k =>
  (factorial k : Rat) * trees.coeff k
```
```leanOutput tsCayley
[0, 1, 2, 9, 64, 625, 7776, 117649, 2097152, 43046721]
```

# Costs
%%%
tag := "hex-truncated-series-costs"
%%%

Multiplication uses the schoolbook method, about `n²/2` multiplications of
coefficients at precision `n`. It needs only addition and multiplication in
`R`, so it is the same code for every coefficient ring. With bounded Newton
steps, the inverse, square root, logarithm and exponential each cost a
constant number of multiplications at precision `n`, so `O(n²)` operations on
coefficients. Composition costs `O(√n)` multiplications plus `O(n²)`
coefficient operations, so `O(n^2.5)` in all, and reversion costs about as
much as a composition. Over `ℚ` the coefficients themselves grow: the
coefficients of `exp x` have denominators `k!`.

The report `reports/hex-truncated-series-performance.md` measures each
operation on one core of a shared machine. A product of two series of
precision 4096 with integer coefficients from 1 to 101 takes 0.10 s, and
1.7 s with rational coefficients drawn from the same range of integers.

Newton's method is not the fastest way to invert a series when multiplication
is schoolbook. The direct recurrence `bₖ = -u Σⱼ<ₖ aₖ₋ⱼ bⱼ` takes `n²/2`
coefficient multiplications against about `4n²/3`, and when inverting `1 - x`
over `ℚ` at precision 4096 the recurrence is 2.7 times as fast. Newton's
method is used because it turns a fast multiplication into a fast inverse:
{ref "hex-poly-fast"}[`HexPolyFast`] runs the same iteration with its fast
polynomial multiplication to divide polynomials, and proves the result equal
to `invOfUnit`. For composition, Brent and Kung's algorithm is 12 times as
fast as Horner's rule at precision 512, and Newton reversion is 5 times as
fast as Lagrange's formula there.

FLINT's series functions over `ℚ`, which use fast multiplication, are 14 to
350 times as fast at the precisions `n` in this table, where the column Hex
gives the time taken by this library:

:::table +header
* * operation
  * `n`
  * Hex
  * FLINT
* * inverse of `1 - x`
  * 1024
  * 259 ms
  * 0.74 ms
* * `exp x`
  * 256
  * 134 ms
  * 9.4 ms
* * `log (1 + x)`
  * 256
  * 23 ms
  * 0.26 ms
* * square root of `1 + x`
  * 256
  * 100 ms
  * 5.4 ms
* * `1/(1 - x)` composed with `x + x²`
  * 128
  * 45 ms
  * 0.26 ms
* * compositional inverse of `x + x²`
  * 128
  * 185 ms
  * 0.88 ms
:::

# The Mathlib correspondence
%%%
tag := "hex-truncated-series-mathlib"
%%%

`HexTruncatedSeriesMathlib` gives `TSeries R n` Mathlib's `CommRing`
structure, built from the operations above, so Mathlib's lemmas apply to the
same addition and multiplication that the programs use. It defines
{name}`HexTruncatedSeriesMathlib.ofPowerSeries`, which keeps the first `n`
coefficients of a Mathlib power series, as a surjective ring homomorphism:

{docstring HexTruncatedSeriesMathlib.ofPowerSeriesHom}

{docstring HexTruncatedSeriesMathlib.ker_ofPowerSeriesHom}

So `TSeries R n` is the quotient of the ring of power series by `(Xⁿ)`:

{docstring HexTruncatedSeriesMathlib.quotEquiv}

Truncation commutes with inversion:

{docstring HexTruncatedSeriesMathlib.ofPowerSeries_invOfUnit}

This turns computations into proofs about Mathlib's power series. The
theorem below determines the coefficient of `x¹⁰` in the inverse of the
finite product `(1 - x)(1 - x²)⋯(1 - x¹⁰)`. The factors beyond it do not
change that coefficient, so by Euler's identity it is `p(10) = 42`; the
theorem itself does not mention partitions. The proof truncates at precision
`11`, moves the inverse and the product across the homomorphism, and lets
`decide +kernel` run the Newton iteration:

```lean
open HexTruncatedSeriesMathlib in
theorem partitions_ten :
    PowerSeries.coeff 10 (PowerSeries.invOfUnit
      (∏ j ∈ Finset.range 10,
        (1 - PowerSeries.X ^ (j + 1)) :
        PowerSeries ℤ) 1) = 42 := by
  rw [← coeff_ofPowerSeries (n := 11) _ 10 (by decide),
    ofPowerSeries_invOfUnit _ 1 (by simp),
    ← ofPowerSeriesHom_apply, map_prod]
  simp only [map_sub, map_one, map_pow,
    ofPowerSeriesHom_apply, ofPowerSeries_X]
  decide +kernel

end HexTruncatedSeriesChapter
```

The companion proves the same kind of statement for the other operations
that have a counterpart in Mathlib: substitution
({name}`HexTruncatedSeriesMathlib.ofPowerSeries_subst`), the compositional
inverse ({name}`HexTruncatedSeriesMathlib.ofPowerSeries_substInvOfIsUnit`),
the exponential ({name}`HexTruncatedSeriesMathlib.ofPowerSeries_exp`) and
the logarithm ({name}`HexTruncatedSeriesMathlib.ofPowerSeries_logOf`), as
well as powers, truncation and the derivative. Their hypotheses differ from
Mathlib's in two places. Mathlib's substitution `f.subst g` needs only that
the constant coefficient of `g` be nilpotent, while `comp` needs it to be
`0`, and the correspondence assumes the stronger hypothesis: over `ℤ/4ℤ` at
precision `1`, substituting `g = 2` into `f = X` gives the constant `2`,
while `comp` of the truncations gives `0`. Mathlib's exponential and
logarithm are defined over `ℚ`-algebras, so those two correspondences assume
one, and the exponential and logarithm over `ℤ/pℤ` described above have no
Mathlib counterpart.

Mathlib has no square root of power series either. The companion proves
that, given a square root `r` of the constant coefficient with `2r` a unit,
there is exactly one power series square root with constant coefficient `r`:

{docstring HexTruncatedSeriesMathlib.exists_unique_sq}

# Cross-references
%%%
tag := "hex-truncated-series-cross-references"
%%%

* {ref "hex-basic"}[`HexBasic`] supplies the vector operations that
  `TSeries` is built on, chosen so that the kernel can evaluate them, which is
  what makes proofs by `decide +kernel` such as the one above possible.
* {ref "hex-poly-fast"}[`HexPolyFast`] divides polynomials by Newton's
  method: it reverses the divisor, inverts it as a truncated series using its
  fast multiplication, with a proof that the result is `invOfUnit`, and
  multiplies. It also computes Padé approximants of truncated series.
