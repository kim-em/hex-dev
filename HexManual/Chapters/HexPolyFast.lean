/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexPolyFast
import HexPolyZ
import HexPolyFp
import HexPolyTheory
import Mathlib.LinearAlgebra.Lagrange

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolyFast: fast dense polynomials" =>
%%%
tag := "hex-poly-fast"
%%%

# Introduction
%%%
tag := "hex-poly-fast-intro"
%%%

{ref "hex-poly"}[`HexPoly`] multiplies polynomials by the schoolbook method,
divides them by long division and computes their gcd by Euclid's algorithm.
All three take a number of coefficient operations quadratic in the degree. `HexPolyFast` implements the
classical faster algorithms for the same type `DensePoly R`: Karatsuba
multiplication, division by Newton iteration, the half-gcd algorithm, product
and remainder trees for evaluating and interpolating at many points, and Padé
approximation. Each operation that `HexPoly` already has comes with a theorem
saying that the fast version returns exactly the same polynomial, and each new
operation comes with a theorem saying what its answer is.

A Padé approximant of a power series is a rational function `p / q` whose own
power series agrees with it to a given order. If a sequence satisfies a linear
recurrence of order `n`, its generating function is a rational function whose
denominator has degree at most `n`, and a Padé approximant recovers it from the
first `2n` terms. The numbers of ways to tile a `3 × 2k` rectangle with
dominoes are `1, 3, 11, 41, 153, 571, 2131, 7953, …`. Asking for a numerator
of degree at most 1 and a denominator of degree at most 2 finds their
generating function:

```lean
open Hex Hex.DensePoly

namespace HexPolyFastChapter

def tilings : TSeries Rat 8 :=
  TSeries.ofFn fun i =>
    [1, 3, 11, 41, 153, 571, 2131, 7953].getD i 0
```

```lean (name := pfTilings)
#eval (pade? (karatsubaPlan 32) tilings 1 2).map
  fun a => (a.p, a.q)
```
```leanOutput pfTilings
some (#p[1, -1], #p[1, -4, 1])
```

A polynomial prints as the list of its coefficients, constant term first, so
the generating function is `(1 - x) / (1 - 4x + x²)`, and the tilings satisfy
`aₖ = 4aₖ₋₁ - aₖ₋₂`. The approximant was computed from the first four terms.
Multiplying all eight terms by the denominator, and keeping the coefficients
of `1, x, …, x⁷`, gives back the numerator, so the other four terms satisfy
the recurrence too:

```lean
#guard mulLow (karatsubaPlan 32) 8 #p[1, -4, 1]
    (polyOfSeries tilings) = #p[1, -1]
```

The first argument of both calls, `karatsubaPlan 32`, says how to multiply:
by Karatsuba's method, switching to the schoolbook method for factors with
at most 32 coefficients. {name}`Hex.DensePoly.pade?` runs the half-gcd algorithm, which
does its work in such products. Multiplication, the half-gcd algorithm and
Padé approximation each have a section below.

`HexPolyFast` does not depend on Mathlib, and has no theory companion of its
own: its theorems are stated in terms of `HexPoly` and
{ref "hex-truncated-series"}[`HexTruncatedSeries`] operations, which their
companions relate to Mathlib's polynomials and power series.
{ref "hex-poly-fast-theory"}[Proofs and Mathlib] shows how to use them.

# Multiplication plans
%%%
tag := "hex-poly-fast-plans"
%%%

Every operation in this chapter takes a {name}`Hex.DensePoly.MulPlan`: a
record of three multiplication functions together with proofs that they
compute the product of `HexPoly`.

{docstring Hex.DensePoly.MulPlan}

A plan is an ordinary value passed as an argument, not a typeclass instance.
The integer and prime-field polynomials `ZPoly` and `FpPoly p` of
{ref "hex-poly-z"}[`HexPolyZ`] and {ref "hex-poly-fp"}[`HexPolyFp`] are
`DensePoly Int` and `DensePoly (ZMod64 p)`, and those libraries provide their
own plans, {name}`Hex.ZPoly.fastPlan` and {name}`Hex.FpPoly.fastPlan`. For
full products these choose, by the sizes of the factors, between the
schoolbook method, Kronecker substitution, packed multiplication and
number-theoretic transforms; their squares and slices use Karatsuba's
method. A caller
chooses the plan at each call, and the `*` of `DensePoly` stays the schoolbook
product. `HexPolyFast` itself provides two plans that work over any
commutative ring: {name}`Hex.DensePoly.schoolbookPlan` and
{name}`Hex.DensePoly.karatsubaPlan`.

Karatsuba's method splits each factor at `xᵏ`, with `k` about half the length,
as `a = a₀ + xᵏ a₁` and `b = b₀ + xᵏ b₁`, and computes three half-size
products `a₀b₀`, `a₁b₁` and `(a₀ + a₁)(b₀ + b₁)`. The middle coefficient
`a₀b₁ + a₁b₀` is the third product minus the other two, so

`ab = a₀b₀ + xᵏ ((a₀ + a₁)(b₀ + b₁) - a₀b₀ - a₁b₁) + x²ᵏ a₁b₁`.

Applied recursively this takes `O(n^log₂3) ≈ O(n^1.585)` coefficient
operations for factors with `n` coefficients. The subtraction is why plans
need a commutative ring, while `HexPoly`'s product needs only addition and
multiplication. `karatsubaPlan cutoff` uses the schoolbook method when a
factor has at most `cutoff` coefficients. When one factor is much longer than the other, it cuts
the longer one into blocks of the shorter one's length and adds up the block
products, so the cost is the number of blocks times the cost of one balanced
product. Squaring has its own recursion, which needs the three squares `a₀²`,
`a₁²` and `(a₀ + a₁)²`.

The central trinomial coefficients count the ways to take `n` steps of `-1`,
`0` or `+1` and return to `0`. The `n`th is the coefficient of `xⁿ` in
`(1 + x + x²)ⁿ`. Squaring six times computes the 64th:

```lean
def trinomial : DensePoly Int := #p[1, 1, 1]

def power64 : DensePoly Int :=
  (List.range 6).foldl
    (fun p _ => squareWith (karatsubaPlan 32) p)
    trinomial
```

```lean (name := pfTrinomial)
#eval (power64.size, power64.coeff 64)
```
```leanOutput pfTrinomial
(129, 209099036316263774148543463251)
```

The theorems about planned products are the proof fields of the plan:

{docstring Hex.DensePoly.mulWith_eq}

{docstring Hex.DensePoly.squareWith_eq}

## Parts of a product

Newton iteration and the half-gcd algorithm use only some coefficients of a
product. {name}`Hex.DensePoly.mulSlice` returns `len` consecutive
coefficients of `a * b`, starting at `xˡᵒ`, as a polynomial whose constant
term is the coefficient of `xˡᵒ`, and {name}`Hex.DensePoly.mulLow` returns the
first `len`. The Karatsuba plan skips every partial product that
cannot contribute to the requested coefficients. The middle product
{name}`Hex.DensePoly.mulMiddleChecked` is the slice from `xⁿ⁻¹` to `xᵐ⁻¹` of
a product of factors with `m ≥ n` coefficients, taken in either order; it is
zero if either factor is.

{docstring Hex.DensePoly.coeff_mulSlice}

The cyclic product {name}`Hex.DensePoly.mulCyclic?` computes `a * b` modulo
`xⁿ - 1`, that is, the cyclic convolution of the coefficient sequences, and
{name}`Hex.DensePoly.mulNegacyclic?` computes it modulo `xⁿ + 1`. Both fold a
planned product, and return `none` for `n = 0`:

```lean (name := pfCyclic)
#eval mulCyclic? (karatsubaPlan 32) 3
  (#p[1, 2, 3] : DensePoly Int) #p[4, 5, 6]
```
```leanOutput pfCyclic
some #p[31, 31, 28]
```

{docstring Hex.DensePoly.mulCyclic_eq_modByMonic}

# Division by Newton iteration
%%%
tag := "hex-poly-fast-division"
%%%

Division with remainder reduces to multiplication. Write `rev f` for the
polynomial whose coefficients are those of `f` in reverse order. If
`a = q b + r` with `a` of degree `m`, `b` of degree `n` and `r` of degree less
than `n`, then reversing gives `rev a ≡ rev q · rev b` modulo `xᵐ⁻ⁿ⁺¹`. The
constant term of `rev b` is the leading coefficient of `b`. When it is
invertible, `rev b` has an inverse as a power series, and

`rev q = rev a · (rev b)⁻¹  mod xᵐ⁻ⁿ⁺¹`.

The remainder is then `a - q b`. Newton's method computes the inverse of a
power series `g`: if `h` agrees with `g⁻¹` to `k` terms, then `h (2 - g h)`
agrees with it to `2k` terms. Each step costs a few multiplications at the
new precision, and the precisions double, so the whole inverse costs a
constant times one multiplication at the final precision. Dividing a
polynomial with `2n` coefficients by one with `n` therefore costs a constant
times one product of polynomials with `n` coefficients. {name}`Hex.DensePoly.reverseSeries` reverses a polynomial into a
series, and {name}`Hex.DensePoly.reciprocalWith` runs Newton's method. It
takes the inverse of the constant term as an argument, and the theorem
{name}`Hex.DensePoly.reciprocalWith_eq` says that it returns the same series
as `TSeries.invOfUnit` from `HexTruncatedSeries`, which computes the inverse
one coefficient at a time.

When many polynomials are divided by the same divisor, the inverse needs to be
computed only once. A {name}`Hex.DensePoly.DivPlan` stores a divisor and the
inverse of its reversal to a fixed number of terms, its capacity, which bounds
the length of the quotients it can produce.
{name}`Hex.DensePoly.DivPlan.ofMonic` builds one for a monic divisor over a
commutative ring, and {name}`Hex.DensePoly.DivPlan.ofNonzero` for a nonzero
divisor over a field. {name}`Hex.DensePoly.DivPlan.divMod` and
{name}`Hex.DensePoly.DivPlan.mod` take a proof that the quotient fits.

Modulo `x² - x - 1`, the power `xᵏ` reduces to `Fₖ x + Fₖ₋₁`, where `Fₖ` is
the `k`th Fibonacci number:

```lean
def golden : DensePoly Int := #p[-1, -1, 1]

def goldenPlan : DivPlan Int :=
  DivPlan.ofMonic (karatsubaPlan 32) golden
    (by unfold Monic; decide +kernel) (by decide) 128

def reduce (p : DensePoly Int) :
    Option (DensePoly Int) :=
  if h : quotientLength p goldenPlan.divisor ≤
      goldenPlan.capacity then
    some (goldenPlan.mod p h)
  else none
```

```lean (name := pfFibonacci)
#eval reduce (monomial 100 1)
```
```leanOutput pfFibonacci
some #p[218922995834555169026, 354224848179261915075]
```

For a single division over a field, {name}`Hex.DensePoly.divModWith` builds
the plan and uses it once. It returns exactly the quotient and remainder of
`HexPoly`'s long division, including its conventions for a zero divisor and
for a divisor longer than the dividend:

{docstring Hex.DensePoly.divModWith_eq}

When the divisor or the quotient has at most eight coefficients, long division
is faster, and compiled code for `divModWith` uses it. In fact
`divModWith` is defined to be `HexPoly`'s `divMod`, and a `@[csimp]` lemma,
which proves the two functions equal, tells the compiler to run the
Newton version instead. So a proof that evaluates `divModWith` in the kernel,
for example by `decide`, sees long division. The gcd functions and
multipoint evaluation below are set up in the same way.

# The half-gcd algorithm
%%%
tag := "hex-poly-fast-half-gcd"
%%%

Euclid's algorithm divides `r₀ = a` by `r₁ = b`, then `r₁` by the remainder
`r₂`, and so on, with `rᵢ₊₁ = rᵢ₋₁ - qᵢ rᵢ`. Each step is a multiplication by
the matrix `[[0, 1], [1, -qᵢ]]`, so the pair `(rᵢ, rᵢ₊₁)` is the product of
the matrices so far applied to `(a, b)`. When `a` and `b` have degree about
`n`, the quotients in the first half of the algorithm, until the degree has
dropped by `n/2`, depend only on the top halves of the coefficients of `a` and
`b`. The half-gcd algorithm computes the product of those quotient matrices
recursively from the top halves, applies it to `a` and `b`, and repeats the
process on the result. With fast multiplication, this costs
`O(M(n) log n)`, where `M(n)` is the cost of one product.

This implementation does not trust the top halves. It computes the matrix from
the top halves, applies it to the whole of `a` and `b`, and accepts it only if
the two resulting polynomials have the degrees that the top halves predict.
Otherwise it discards the matrix and takes one ordinary Euclidean step with
{name}`Hex.DensePoly.divModWith`. Accepted matrices are proved to be products
of Euclid's own quotient matrices, so the algorithm returns exactly the gcd
and Bézout coefficients of `HexPoly`'s `xgcd`, which are not normalized to
make the gcd monic. The gcd functions, interpolation and Padé approximation
need a field of coefficients. Matrices are values of type
{name}`Hex.DensePoly.GcdStep`.

```lean (name := pfXgcd)
#eval xgcdWith (karatsubaPlan 32)
  (#p[-1, 0, 0, 1] : DensePoly Rat) #p[-1, 0, 1]
```
```leanOutput pfXgcd
{ gcd := #p[-1, 1], left := #p[1], right := #p[0, -1] }
```

Here `(x³ - 1) · 1 + (x² - 1) · (-x) = x - 1`.

{docstring Hex.DensePoly.xgcdWith_eq}

{docstring Hex.DensePoly.gcdWith_eq}

{name}`Hex.DensePoly.xgcdLeftWith` returns only the gcd and the coefficient
of `a`, as `HexPoly`'s `xgcdLeft` does.

# Many points at once
%%%
tag := "hex-poly-fast-multipoint"
%%%

Evaluating a polynomial of degree less than `n` at `n` points by Horner's
rule takes `n²` operations. The remainder of `f` modulo `x - a` is `f(a)`, and
the remainders of `f` modulo many polynomials can be computed together with a
product tree. Its leaves are the moduli `m₁, …, mₙ`, and each node holds the
product of the two nodes below it, so the root is `m₁ ⋯ mₙ`. The remainder
tree reduces `f` modulo the root, then reduces that remainder modulo the two
children of the root, and so on down to the leaves. With fast multiplication
and division, for `n` linear leaves both trees take `O(M(n) log n)`
operations.

{name}`Hex.DensePoly.ProductTree.build` builds a product tree from an array of
polynomials. It keeps only the leaves and the root, and recomputes the other
levels on request with {name}`Hex.DensePoly.ProductTree.level?`.
{name}`Hex.DensePoly.RemainderTree.build` builds a remainder tree from monic
leaves, {name}`Hex.DensePoly.MonicLeaf`, and stores a division plan at every
node. {name}`Hex.DensePoly.RemainderTree.remainders?` returns the remainders
of a polynomial `p` modulo every leaf, in order; it succeeds whenever
`p.size ≤ tree.rootDegree + tree.capacity`, where `rootDegree` is the sum of
the degrees of the leaves and `capacity` is chosen when the tree is built.

{name}`Hex.DensePoly.EvalPlan.build` builds the remainder tree for the leaves
`x - aᵢ` at a list of points, with capacity for polynomials with as many
coefficients as there are points. {name}`Hex.DensePoly.EvalPlan.eval` then
evaluates a polynomial at all the points; a longer polynomial is evaluated at
each point by Horner's rule.

{docstring Hex.DensePoly.EvalPlan.get_eval}

Interpolation inverts evaluation, and needs a field. Given distinct points `a₁, …, aₙ` and values
`y₁, …, yₙ`, let `m = (x - a₁) ⋯ (x - aₙ)`. Lagrange's formula for the unique
polynomial of degree less than `n` with `f(aᵢ) = yᵢ` is

`f = Σᵢ yᵢ / m'(aᵢ) · m / (x - aᵢ)`.

{name}`Hex.DensePoly.InterpPlan.build?` builds the product tree for `m`,
evaluates the derivative `m'` at all the points with the remainder tree, and
stores the inverses `1 / m'(aᵢ)`. It returns `none` exactly when two points
are equal. {name}`Hex.DensePoly.InterpPlan.interpolate?` then sums Lagrange's
formula up the tree: a node whose children have products `m_L` and `m_R`, and
partial sums `f_L` and `f_R`, gets `f_L m_R + f_R m_L`. It returns `none`
exactly when the number of values differs from the number of points.

The sums `0, 1, 5, 14` of the squares up to `0², 1², 2², 3²` determine the
cubic polynomial `n(n + 1)(2n + 1) / 6` that gives the sum of the squares up
to `n²`:

```lean
def squaresPlan : Option (InterpPlan Rat) :=
  InterpPlan.build? (karatsubaPlan 32) #[0, 1, 2, 3]

def sumSquares : Option (DensePoly Rat) :=
  squaresPlan.bind (·.interpolate? #[0, 1, 5, 14])
```

```lean (name := pfSquares)
#eval sumSquares
```
```leanOutput pfSquares
some #p[0, (1 : Rat)/6, (1 : Rat)/2, (1 : Rat)/3]
```

Evaluating at `4, 5, 6, 7` continues the sequence:

```lean (name := pfSquaresEval)
#eval sumSquares.map fun f =>
  (EvalPlan.build (karatsubaPlan 32)
    #[4, 5, 6, 7]).eval f
```
```leanOutput pfSquaresEval
some #[30, 55, 91, 140]
```

{docstring Hex.DensePoly.InterpPlan.interpolate?_sound}

{docstring Hex.DensePoly.InterpPlan.interpolate?_unique}

# Padé approximation
%%%
tag := "hex-poly-fast-pade"
%%%

Let `s` be a power series known to `N = m + n + 1` terms. An `[m/n]` Padé
approximant of `s` is a pair of polynomials `p` of degree at most `m` and
`q ≠ 0` of degree at most `n` with `q s ≡ p` modulo `xᴺ`. One always exists:
the congruence is `N` linear equations in the `N + 1` coefficients of `p` and
`q`. The extended Euclidean algorithm applied to `xᴺ` and `s` finds one. Each
remainder it produces has the form `u xᴺ + v s`, so `v s` is congruent to the
remainder modulo `xᴺ`, and the first remainder of degree at most `m` gives
`p` and `q = v`. {name}`Hex.DensePoly.padeHomogeneous` stops the half-gcd
algorithm at that remainder, and returns a
{name}`Hex.DensePoly.PadeApproximant`, which carries proofs of the degree
bounds, of `q ≠ 0` and of the congruence:

{docstring Hex.DensePoly.PadeApproximant}

The pair need not have `q(0) ≠ 0`. When it does, `q` is invertible as a
power series and `s ≡ p / q` modulo `xᴺ`; this is the approximation of the
introduction. {name}`Hex.DensePoly.pade?` scales the denominator to have constant term `1`,
as in the introduction, and returns a {name}`Hex.DensePoly.NormalizedPade`:

{docstring Hex.DensePoly.pade?_eq_none_iff}

The `[2/2]` approximant of `eˣ` is
`(1 + x/2 + x²/12) / (1 - x/2 + x²/12)`:

```lean
def expSeries : TSeries Rat 5 :=
  TSeries.ofFn fun i =>
    [1, 1, 1/2, 1/6, 1/24].getD i 0
```

```lean (name := pfExp)
#eval (pade? (karatsubaPlan 32) expSeries 2 2).map
  fun a => (a.p, a.q)
```
```leanOutput pfExp
some (#p[1, (1 : Rat)/2, (1 : Rat)/12], #p[1, (-1 : Rat)/2, (1 : Rat)/12])
```

For the series `x` and `m = 0`, `n = 1`, the congruence `q x ≡ p` modulo `x²`
forces `p = 0` and `q` to be a multiple of `x`. There is no approximant with
`q(0) = 1`, and `pade?` returns `none`. The homogeneous approximant is
`p = 0`, `q = -x`:

```lean
def xSeries : TSeries Rat 2 := TSeries.X

#guard (pade? (karatsubaPlan 32) xSeries 0 1).isNone
#guard (padeHomogeneous (karatsubaPlan 32)
    xSeries 0 1).q = #p[0, -1]

end HexPolyFastChapter
```

# Costs
%%%
tag := "hex-poly-fast-costs"
%%%

The fast algorithms are faster only for large enough inputs, and how large
depends on the operation. These times were measured with the library's
benchmark program, `hexpolyfast_bench`, on one core of a shared machine
(`chungus2`) on 2026-10-05, using `karatsubaPlan 32`. Each time is the average
over repeated calls with the same input, in a single run. The inputs are:

* products: two factors with `n` coefficients, which are integers of absolute
  value at most 51, stored as `Int` or as `Rat`;
* division: a polynomial with `2n + 1` coefficients divided by one with
  `n + 1`, over the field with 65537 elements;
* extended gcd: two polynomials of degree about `n` over the field with two
  elements;
* evaluation: a polynomial with `n` coefficients at `n` points, over the field
  with 65537 elements;
* Padé approximation: the `[n/n]` approximant of the series with coefficients
  `1 / (i + 1)` over the field with 65537 elements.

The direct methods are the schoolbook product, long division, Euclid's
algorithm, Horner's rule at each point, and, for the Padé approximant,
Gauss–Jordan elimination on its linear equations.

:::table +header
* * operation
  * `n`
  * direct
  * fast
* * product over `Int`
  * 1024
  * 6.5 ms
  * 1.8 ms
* * product over `Int`
  * 4096
  * 116 ms
  * 17 ms
* * product over `Rat`
  * 4096
  * 3.3 s
  * 0.53 s
* * division, one-shot
  * 1024
  * 14.5 ms
  * 17.2 ms
* * division, one-shot
  * 4096
  * 228 ms
  * 153 ms
* * division, cached plan
  * 1024
  * 14.5 ms
  * 5.5 ms
* * extended gcd
  * 1024
  * 22 ms
  * 69 ms
* * extended gcd
  * 4096
  * 373 ms
  * 712 ms
* * evaluation, cached plan
  * 1024
  * 4.4 ms
  * 10.3 ms
* * evaluation, cached plan
  * 4096
  * 72 ms
  * 99 ms
* * Padé approximant
  * 256
  * 119 ms
  * 11 ms
* * Padé approximant
  * 1024
  * 7.6 s
  * 0.11 s
:::

Karatsuba multiplication is already faster than the schoolbook method at 64
coefficients. Division with a cached plan is as fast as long division at 64
coefficients and faster beyond, while one-shot division, which also computes
the inverse, overtakes long division only between 1024 and 2048. The half-gcd algorithm and
multipoint evaluation are still slower than Euclid's algorithm and Horner's
rule at 4096, although the gap is closing as `n` grows. Building an
evaluation plan for 4096 points takes a further 170 ms. Interpolation has no
`HexPoly` counterpart. Recovering `x³ - 7x + 11` from its values at
`0, 1, …, 1023` over the field with 65537 elements takes 39 ms including building the plan,
and 6 ms with a plan built in advance.

For full products of integer and prime-field polynomials, the plans of
`HexPolyZ` and `HexPolyFp` can be much faster than `karatsubaPlan`. The Hex libraries use the fast algorithms only where
they measured a gain. The finite-field and factorization libraries keep
Euclidean division and gcd. {ref "hex-hensel"}[`HexHensel`] multiplies long
lists of small linear factors with a product tree and `ZPoly.fastPlan`, and
{ref "hex-rational-fn"}[`HexRationalFn`] divides with `divModWith` and
`karatsubaPlan 8`.

# Proofs and Mathlib
%%%
tag := "hex-poly-fast-theory"
%%%

There is no `HexPolyFastTheory`. The theorems above say that each fast
operation agrees with a `HexPoly` or `HexTruncatedSeries` operation, or
describe its result by evaluation, divisibility and degree, and
{ref "hex-poly-theory"}[`HexPolyTheory`] translates those into statements
about Mathlib's `Polynomial`. For example, the interpolation plan computes
Mathlib's Lagrange interpolant `Lagrange.interpolate`:

```lean
open Hex Hex.DensePoly HexPolyTheory Polynomial

namespace HexPolyFastChapterTheory

variable (plan : InterpPlan ℚ)

/-- The `i`th point of an interpolation plan. -/
def node (i : Fin plan.size) : ℚ :=
  plan.points[i.1]'(by simp)

theorem node_injective :
    Function.Injective (node plan) := by
  intro i j hij
  by_contra hne
  let ys : Array ℚ := Array.ofFn fun k :
    Fin plan.size => if k = i then 1 else 0
  have hsize : ys.size = plan.size := by simp [ys]
  obtain ⟨p, hp⟩ :
      ∃ p, plan.interpolate? ys = some p := by
    cases h : plan.interpolate? ys with
    | none =>
      have := (plan.interpolate?_eq_none_iff ys).mp h
      exact absurd hsize this
    | some p => exact ⟨p, rfl⟩
  have hi :=
    (plan.interpolate?_sound ys p hp).2 i i.2
  have hj :=
    (plan.interpolate?_sound ys p hp).2 j j.2
  have hij' : plan.points[i.1]'(by simp) =
      plan.points[j.1]'(by simp) := hij
  rw [hij', hj] at hi
  simp [ys, Ne.symm hne] at hi

theorem interpolate?_eq_lagrange (ys : Array ℚ)
    (p : DensePoly ℚ)
    (h : plan.interpolate? ys = some p) :
    toPolynomial p =
      Lagrange.interpolate Finset.univ (node plan)
        (fun i => ys.getD i 0) := by
  obtain ⟨hsize, heval⟩ :=
    plan.interpolate?_sound ys p h
  apply Lagrange.eq_interpolate_of_eval_eq
  · exact (node_injective plan).injOn
  · rw [Finset.card_univ, Fintype.card_fin,
      Polynomial.degree_lt_iff_coeff_zero]
    intro m hm
    rw [coeff_toPolynomial]
    exact coeff_eq_zero_of_size_le p (by omega)
  · intro i _
    rw [eval_toPolynomial]
    exact heval i i.2

end HexPolyFastChapterTheory
```

The proof that the points of a plan are distinct uses only the public
theorems: if two points were equal, the values `1` and `0` at them could not
both be interpolated.

# Cross-references
%%%
tag := "hex-poly-fast-cross-references"
%%%

* {ref "hex-poly"}[`HexPoly`] defines `DensePoly` and the schoolbook product,
  long division and Euclidean algorithm that this library speeds up.
* {ref "hex-truncated-series"}[`HexTruncatedSeries`] defines the series
  `TSeries R n` used for reciprocals and Padé approximation.
* {ref "hex-poly-z"}[`HexPolyZ`] and {ref "hex-poly-fp"}[`HexPolyFp`] define
  the multiplication plans {name}`Hex.ZPoly.fastPlan` and
  {name}`Hex.FpPoly.fastPlan`.
* {ref "hex-hensel"}[`HexHensel`] uses product trees, and
  {ref "hex-rational-fn"}[`HexRationalFn`] uses `divModWith`.
