/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import VersoManual
public import HexPolyZGcd
public import HexPolyZGcdMathlib

import all HexPolyZ.ExactDivision
import all HexPolyZGcd.Cert
import all HexPolyZGcd.Gcd
import all HexPolyZGcd.Maximal
import all HexPolyZGcd.SquareFree
import all HexPolyZGcdMathlib.Gcd

public section

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolyZGcd: greatest common divisors of integer polynomials" =>
%%%
tag := "hex-poly-z-gcd"
%%%

# Introduction
%%%
tag := "hex-poly-z-gcd-intro"
%%%

`HexPolyZGcd` computes greatest common divisors of polynomials with integer
coefficients. With the gcd it returns the two cofactors, the quotients of the
inputs by the gcd, and evidence that the cofactors have no common factor, so
every answer can be checked independently of the algorithm that found it.
Around the gcd it provides exact division, decidable divisibility, the gcd of
a list, the least common multiple, the gcd of polynomials with rational
coefficients, and the decomposition of a polynomial into its square-free part
and its repeated factors, the first step of factoring it.

Since `x^m - 1` is the product of the cyclotomic polynomials `Φ_d` over the
divisors `d` of `m`, the gcd of `x^m - 1` and `x^n - 1` is `x^gcd(m,n) - 1`.
For `m = 12` and `n = 8`:

```lean (name := intro)
open Hex

namespace HexPolyZGcdChapter

def f : ZPoly := DensePoly.monomial 12 1 - 1
def g : ZPoly := DensePoly.monomial 8 1 - 1

#eval (ZPoly.gcd f g, ZPoly.cofactors f g)
```
```leanOutput intro
(#p[-1, 0, 0, 0, 1], #p[1, 0, 0, 0, 1, 0, 0, 0, 1], #p[1, 0, 0, 0, 1])
```

A polynomial prints as the list of its coefficients, constant term first, so
the gcd is `x^4 - 1` and the cofactors are `x^8 + x^4 + 1` and `x^4 + 1`.
The section {ref "hex-poly-z-gcd-mathlib"}[The Mathlib correspondence] turns
this computation into a theorem about `Polynomial ℤ`: every common divisor of
`X^12 - 1` and `X^8 - 1` divides `X^4 - 1`.

`HexPolyZGcd` does not depend on Mathlib. It builds on
{ref "hex-poly-z"}[HexPolyZ] for integer polynomials,
{ref "hex-poly-fp"}[HexPolyFp] for polynomials modulo a prime,
{ref "hex-modular"}[HexModular] for Chinese remaindering and
{ref "hex-resultant"}[HexResultant] for subresultants. Its companion
`HexPolyZGcdMathlib` restates the results in terms of Mathlib's
`Polynomial ℤ`.

# Integer polynomials and their gcd
%%%
tag := "hex-poly-z-gcd-normalization"
%%%

An integer polynomial has type {name}`Hex.ZPoly`, which is
`DensePoly Int` from {ref "hex-poly"}[HexPoly]: the array of coefficients,
constant term first, with no trailing zeros. The literal
`#p[a₀, a₁, …, aₙ]` is `a₀ + a₁ x + ⋯ + aₙ xⁿ`, and
`DensePoly.monomial n c` is `c xⁿ`.

In `ℤ[x]` a gcd is determined up to multiplication by a unit, and the units
are `1` and `-1`. The library returns the gcd with positive leading
coefficient, and `gcd 0 0 = 0`. Integer factors are part of the gcd: the
content of a polynomial, the gcd of its coefficients, is a factor like any
other, so the gcd of `2x` and `4x` is `2x`, and the gcd of `6` and `4x` is
`2`:

```lean (name := contents)
#eval (ZPoly.gcd #p[0, 2] #p[0, 4],
  ZPoly.gcd (DensePoly.C 6) #p[0, 4],
  ZPoly.gcd #p[2, -1] #p[-4, 2])
```
```leanOutput contents
(#p[0, 2], #p[2], #p[-2, 1])
```

{docstring Hex.ZPoly.NormalizedGcd}

Two polynomials in this form that divide each other are equal, so this
convention picks out one gcd:

{docstring Hex.ZPoly.eq_of_normalized_dvd}

# Certificates
%%%
tag := "hex-poly-z-gcd-certificates"
%%%

That `d` divides `f` and `h` is easy to check: divide, and compare the
products `d · f'` and `d · h'` with the inputs. That `d` is the *greatest*
common divisor is not, since `1` also divides both. It suffices to know that
the cofactors `f'` and `h'` have no common factor other than `±1`, and in
`ℤ[x]` that is subtle. Over a field one would exhibit `α f' + β h' = 1`, but
`ℤ[x]` is not a principal ideal domain: `x` and `2` have no common factor,
and yet `α x + β · 2 = 1` has no solution, because the left side has even
constant term. A certificate therefore uses one of two other kinds of
evidence:

{docstring Hex.ZPoly.CoprimeWitness}

The first kind is the usual one. Suppose a prime `p` divides neither leading
coefficient, and the images of `f'` and `h'` modulo `p` satisfy
`α f' + β h' = 1` in `F_p[x]`. If `d` divides both cofactors, then its image
divides `1` and so is a constant. Since reduction modulo `p` keeps the
degrees of `f'` and `h'`, and degrees add in both `ℤ[x]` and `F_p[x]`, it
also keeps the degree of `d`, which is therefore `0`. So `d` is an integer
dividing the contents of `f'` and `h'`, and the checker requires these
contents to be coprime. The second kind needs no prime: if
`u f' + v h' = k` with `k` a nonzero integer, then `d` divides `k` and so is
a constant, and the same argument with the contents applies. When `f'` and
`h'` are coprime, such `u`, `v` and `k` always exist, with `k` their
resultant (see {ref "hex-resultant"}[HexResultant]), while a usable prime
need not exist among the primes below `2^31` that the library computes with.

A certificate is a candidate gcd, the two cofactors and a witness:

{docstring Hex.ZPoly.GcdCert}

{name}`Hex.ZPoly.checkGcd` `f h c` accepts the certificate `c` when
`f = c.gcd · c.cofL` and `h = c.gcd · c.cofR`, the gcd is in the normal form
above, the contents of the cofactors are coprime, and the witness is valid
for the cofactors. For a modular witness, validity means that reduction
modulo `p` keeps the degree of each cofactor and that `α f' + β h' = 1`
modulo `p`. The products are compared by
{name}`Hex.ZPoly.mulEqPacked`, which packs each polynomial into one large
integer, with the coefficients in widely spaced slots, and compares a single
integer product, without computing the product polynomial.

{docstring Hex.ZPoly.checkGcd_sound}

To see a certificate, this chapter uses a small helper that describes the
witness, writing the polynomials `α` and `β` modulo `p` with coefficients
in `0, …, p - 1`:

```lean
def lift {p : Nat} [ZMod64.Bounds p]
    (a : FpPoly p) : ZPoly :=
  DensePoly.ofList
    (a.toArray.toList.map fun c => (c.toNat : Int))

def witness : ZPoly.CoprimeWitness → String
  | .modular p a b =>
    letI : ZMod64.Bounds p.m := p.bounds
    s!"modular: p = {p.m}, α = {repr (lift a)}, " ++
      s!"β = {repr (lift b)}"
  | .constant u v k =>
    s!"constant: u = {repr u}, v = {repr v}, k = {k}"
```

```lean (name := introWitness)
#eval witness (ZPoly.gcdCert f g).coprime
```
```leanOutput introWitness
"modular: p = 2, α = #p[1], β = #p[0, 0, 0, 0, 1]"
```

Modulo `2`, `1 · (x^8 + x^4 + 1) + x^4 · (x^4 + 1) = 1`. The cofactors
also satisfy `(x^8 + x^4 + 1) - x^4 (x^4 + 1) = 1` over `ℤ`, a witness of
the second kind with `k = 1`; the Mathlib example at the end of the chapter
uses that one.

A checked certificate makes its gcd greatest. Write `d = c · d₀`, where `c`
is the content of `d` and `d₀` is primitive, that is, has content `1`. The
cofactors stay coprime over `ℚ[x]`, so over `ℚ[x]` the candidate is the gcd
up to a nonzero rational factor, and `d₀` divides it there. By Gauss's lemma
a primitive integer polynomial that divides another over `ℚ[x]` divides it
over `ℤ[x]`, so `d₀` divides the candidate in `ℤ[x]`. Since the contents of
the cofactors are coprime, `c` divides the content of the candidate, and
together these give that `d` divides the candidate. The theorem is stated
for the property that {name}`Hex.ZPoly.checkGcd_sound` establishes:

{docstring Hex.ZPoly.CoprimeCofactors}

{docstring Hex.ZPoly.dvd_gcd_of_coprimeCofactors}

# Computing gcds
%%%
tag := "hex-poly-z-gcd-operations"
%%%

{name}`Hex.ZPoly.gcdCert` `f h` computes a certificate for `f` and `h`, by
the methods described in {ref "hex-poly-z-gcd-algorithms"}[How the gcd is found].
{name}`Hex.ZPoly.gcd` and {name}`Hex.ZPoly.cofactors` read the gcd and the
cofactors off this certificate, and every certificate it returns has passed
the checker:

{docstring Hex.ZPoly.gcdCert_checks}

From it come the laws of a gcd:

{docstring Hex.ZPoly.gcd_dvd_left}

{docstring Hex.ZPoly.dvd_gcd}

{name}`Hex.ZPoly.isCoprime` tests whether the gcd is `1`,
{name}`Hex.ZPoly.gcdList` folds the gcd over a list, starting from `0`, and
{name}`Hex.ZPoly.lcm` divides the product by the gcd. The gcd of
`x^12 - 1`, `x^8 - 1` and `x^6 - 1` is `x^2 - 1`, and the least common
multiple of the first two is `(x^12 - 1)(x^4 + 1)`:

```lean (name := listLcm)
def g6 : ZPoly := DensePoly.monomial 6 1 - 1

#eval (ZPoly.gcdList [f, g, g6], ZPoly.lcm f g)
```
```leanOutput listLcm
(#p[-1, 0, 1], #p[-1, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1])
```

{name}`Hex.ZPoly.ratGcd` computes the gcd of two polynomials with rational
coefficients. It clears denominators, computes the integer gcd and returns it
scaled to be monic, the usual convention over a field. Both
`1/2 + x/3` and `3/4 + x/2` are multiples of `x + 3/2`:

```lean (name := ratGcd)
#eval ZPoly.ratGcd (DensePoly.ofList [1/2, 1/3])
  (DensePoly.ofList [3/4, 1/2])
```
```leanOutput ratGcd
#p[(3 : Rat)/2, 1]
```

## Exact division
%%%
tag := "hex-poly-z-gcd-division"
%%%

Checking a candidate begins with dividing by it. {name}`Hex.ZPoly.divExact?`, from HexPolyZ, returns the quotient
when the division is exact and `none` otherwise. Before dividing, it rejects
a divisor whose degree is too large, whose leading coefficient or content
does not divide that of the dividend, or whose value at `1` does not divide
the dividend's value there. `x^4 - 1` divides `x^12 - 1`. `x^5 - 1` passes
all these tests, and long division shows that it does not divide:

```lean (name := divExact)
#eval (ZPoly.divExact? f #p[-1, 0, 0, 0, 1],
  ZPoly.divExact? f #p[-1, 0, 0, 0, 0, 1])
```
```leanOutput divExact
(some #p[1, 0, 0, 0, 1, 0, 0, 0, 1], none)
```

`HexPolyZGcd` uses {name}`Hex.ZPoly.divExact?` to make divisibility
decidable, so `decide` evaluates `g ∣ f`:

```lean (name := dvd)
#eval (decide ((#p[-1, 0, 0, 1] : ZPoly) ∣ f),
  decide ((#p[1, 1] : ZPoly) ∣ #p[1, 0, 1]))
```
```leanOutput dvd
(true, false)
```

`divExact? f 0` is `none`, even for `f = 0`, while `0 ∣ 0` holds; the
instance treats a zero divisor separately.

# How the gcd is found
%%%
tag := "hex-poly-z-gcd-algorithms"
%%%

The textbook method, Euclid's algorithm over `ℚ[x]`, is correct and slow.
Its remainders acquire large numerators and denominators even when the
inputs and the answer are small. Knuth's example in _The Art of Computer
Programming_, volume 2, §4.6.1, is the pair
`x^8 + x^6 - 3x^4 - 3x^3 + 8x^2 + 2x - 5` and
`3x^6 + 5x^4 - 4x^2 - 9x + 21`. Here are its remainders:

```lean (name := knuthRemainders)
def knuthF : ZPoly := #p[-5, 2, 8, -3, -3, 0, 1, 0, 1]
def knuthG : ZPoly := #p[21, -9, -4, 0, 5, 0, 3]

partial def remainders (a b : DensePoly Rat) :
    List (DensePoly Rat) :=
  if b.isZero then [] else
    let r := (DensePoly.divMod a b).2
    r :: remainders b r

#eval remainders (ZPoly.toRatPoly knuthF)
  (ZPoly.toRatPoly knuthG)
```
```leanOutput knuthRemainders
[#p[(-1 : Rat)/3, 0, (1 : Rat)/9, 0, (-5 : Rat)/9],
 #p[(441 : Rat)/25, -9, (-117 : Rat)/25],
 #p[(-102500 : Rat)/6591, (233150 : Rat)/19773],
 #p[(-1288744821 : Rat)/543589225],
 #p[]]
```

The last nonzero remainder is a constant, so the polynomials are coprime.
{name}`Hex.ZPoly.gcd` reaches the same conclusion from a single image modulo
`47`, where the two polynomials are already coprime:

```lean (name := knuthGcd)
#eval (ZPoly.gcd knuthF knuthG,
  witness (ZPoly.gcdCert knuthF knuthG).coprime)
```
```leanOutput knuthGcd
(#p[1], "modular: p = 47, α = #p[16, 42, 29, 45, 42, 34], β = #p[24, 21, 35, 11, 31, 3, 33, 20]")
```

{name}`Hex.ZPoly.gcdCert` tries several methods in turn, in the manner of
FLINT's `fmpz_poly_gcd`. Each produces a candidate certificate, and a
candidate the checker rejects passes the problem to the next method. The
methods need no proof of correctness, since only certificates the checker
accepts are returned.

1. *Trivial cases.* If an input is zero or a constant, the answer is
   immediate. Otherwise the gcd of the contents and the largest common
   power of `x` are divided out of both inputs and multiplied back into the
   answer at the end.
2. *The first remainder.* When `f - h` has lower degree than both `f` and
   `h`, it is offered as the gcd, with its sign adjusted. It is accepted when
   the cofactors differ by `±1`, as for `c a` and `c (a + 1)`.
3. *A coprimality test.* Unless some coefficient is at least `2^17` in
   absolute value, the inputs are reduced modulo the prime `47`. If the images are coprime, the
   extended Euclidean algorithm in `F_47[x]` gives `α` and `β`, and the gcd
   is `1`, at the cost of one image gcd. If the images are not coprime, nothing follows, since `47` may
   divide the resultant of coprime polynomials.
4. *The heuristic gcd* of Char, Geddes and Gonnet, for inputs of degree
   below 32 whose coefficients are below `2^17` in absolute value. Evaluate both inputs at an
   integer `ξ` larger than twice every coefficient, take the integer gcd of
   the two values, and read a polynomial off its digits in base `ξ`,
   choosing digits of absolute value at most `ξ/2`. The integer gcd may contain extra
   factors that do not come from the polynomial gcd, so the result can be
   wrong, and the checker decides. On failure `ξ` roughly doubles, until
   the estimated sizes of the evaluated integers, summed over the attempts,
   would exceed 4096 bits.
5. *Brown's modular algorithm.* For each prime `p`, compute the monic gcd of
   the images in `F_p[x]` and multiply it by `γ`, the gcd of the leading
   coefficients of the primitive parts of the inputs, since the leading
   coefficient of the true gcd divides `γ`. A prime that lowers the degree
   of an input, or divides `γ`, is *bad* and skipped. An image of higher
   degree than one seen before is *unlucky*, because the prime divides a
   resultant of the cofactors, and is skipped; an image of lower degree
   makes all earlier images unlucky, and they are discarded. The images of
   equal degree are combined coefficient by coefficient with the Chinese
   remainder theorem (see {ref "hex-modular"}[HexModular]), and after each
   prime the primitive part of the result, with the content restored, is
   offered to the checker. The primes are sixteen fixed primes just below
   `2^24`, then primes just below `2^31`. The number of primes is bounded
   using the Landau–Mignotte bound on the coefficients of a factor, but the
   loop stops as soon as the checker accepts, which can be far earlier.
6. *The subresultant algorithm.* The extended subresultant chain of
   {ref "hex-resultant"}[HexResultant] works over `ℤ` without fractions.
   Its last nonzero entry is a multiple of the gcd, and for the cofactors it
   provides `u`, `v` and a nonzero integer `k` with `u f' + v h' = k`, a
   witness of the second kind. If this produces no accepted certificate, the
   library falls back on Euclid's algorithm over `ℚ[x]`, with denominators
   cleared, which is proved always to produce one.

To find a witness for a candidate, the library tries a difference
`f' - h'` that is a nonzero constant, then the primes `2, 3, 5, …, 47`, and
then three primes just below `2^24`. A modular witness contains a proof
that `p` is prime, and small primes come first because a certificate written
out in a proof must supply that proof, for instance by trial division
checked by `decide`, which is cheap for small `p`. The cofactors `x` and `x + 2 · 3 · 5 ⋯ 43` are coprime, but their
images coincide modulo every prime up to `43`, and the library uses their
constant difference:

```lean (name := primorial)
#eval witness (ZPoly.gcdCert #p[0, 1]
  #p[2 * 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23
    * 29 * 31 * 37 * 41 * 43, 1]).coprime
```
```leanOutput primorial
"constant: u = #p[1], v = #p[-1], k = -13082761331670030"
```

The cofactors of a checked gcd need not be primitive; only their contents
must be coprime. For `12x^2 + 12x^3` and `36x + 18x^2` the gcd is `6x`, and
the cofactors `2x + 2x^2` and `6 + 3x` have contents `2` and `3`:

```lean (name := contentCofactors)
#eval ZPoly.cofactors #p[0, 0, 12, 12] #p[0, 36, 18]
```
```leanOutput contentCofactors
(#p[0, 2, 2], #p[6, 3])
```

# The square-free part
%%%
tag := "hex-poly-z-gcd-square-free"
%%%

A polynomial is square-free when no irreducible factor occurs more than
once. Over `ℚ`, the repeated factors of `f` are exactly the common factors
of `f` and its derivative `f'`: if `f = p^e q` with `p` irreducible, `e ≥ 1`
and `p` not dividing `q`, then `p^(e-1)` divides `f'` and `p^e` does not.
So `gcd(f, f')` contains each irreducible factor of `f` once less than `f`
does, and `f / gcd(f, f')` contains each one exactly once. Factoring
algorithms such as {ref "hex-berlekamp-zassenhaus"}[Berlekamp–Zassenhaus]
need square-free input, and compute this first.

{name}`Hex.ZPoly.sqfDecomp` takes the primitive part `p` of `f`, which keeps
the sign of `f`, and returns a
{name}`Hex.ZPoly.PrimitiveSquareFreeDecomposition` with three fields:
`primitive`, which is `p`; `repeatedPart`, which is `gcd(p, p')`; and
`squareFreeCore`, which is `p / gcd(p, p')` with positive leading
coefficient. For `f = 0` all three are `0`. For `6 (x - 1)^3 (x + 2)^2 (x^2 + 1)`, the square-free core is
`(x - 1)(x + 2)(x^2 + 1) = x^4 + x^3 - x^2 + x - 2` and the repeated part is
`(x - 1)^2 (x + 2) = x^3 - 3x + 2`:

```lean (name := sqf)
def repeated : ZPoly :=
  DensePoly.C 6 * #p[-1, 1] * #p[-1, 1] * #p[-1, 1] *
    #p[2, 1] * #p[2, 1] * #p[1, 0, 1]

#eval let d := ZPoly.sqfDecomp repeated
  (d.squareFreeCore, d.repeatedPart)
```
```leanOutput sqf
(#p[-2, 1, -1, 1, 1], #p[2, -3, 0, 1])
```

{docstring Hex.ZPoly.sqfDecomp_reassembly_signed}

{docstring Hex.ZPoly.sqfDecomp_squareFreeCore}

Here {name}`Hex.ZPoly.SquareFreeRat` says that the gcd over `ℚ[x]` of a
polynomial and its derivative is a constant or zero. It holds for `0`, which
is why the theorem assumes a nonzero core.

HexPolyZ also computes this decomposition, by
{name}`Hex.ZPoly.primitiveSquareFreeDecomposition`, using Euclid's algorithm
over `ℚ[x]`. {name}`Hex.ZPoly.sqfDecomp` uses the integer gcd instead, and
its proof shows that it agrees with the HexPolyZ version up to sign. For
inputs of degree at most 7 it still uses Euclid's algorithm over `ℚ[x]` for
the gcd, which is faster on such small inputs than building a certificate.

# The Mathlib correspondence
%%%
tag := "hex-poly-z-gcd-mathlib"
%%%

`HexPolyZGcdMathlib` restates these results for Mathlib's `Polynomial ℤ`,
through the ring isomorphism {name}`HexPolyZMathlib.equiv` between
{name}`Hex.ZPoly` and `Polynomial ℤ` from
{ref "hex-poly-z-mathlib"}[HexPolyZMathlib]. The theorems are stated in
terms of divisibility:

{docstring HexPolyZGcdMathlib.gcd_dvd_left}

{docstring HexPolyZGcdMathlib.dvd_gcd}

{docstring HexPolyZGcdMathlib.coprimeCofactors_greatest}

{docstring HexPolyZGcdMathlib.divExact?_eq_dvd}

The condition `g ≠ 0` is needed because `divExact? 0 0` is `none` while
`0 ∣ 0` holds.

Here is the gcd of the introduction as a theorem about `Polynomial ℤ`: every
common divisor of `X^12 - 1` and `X^8 - 1` divides `X^4 - 1`. The proof
writes down the certificate, with the integral witness found above, and the
kernel checks it with `decide +kernel`. The computation of the gcd plays no
part in the proof.

```lean
def g4 : ZPoly := DensePoly.monomial 4 1 - 1

def cert : ZPoly.GcdCert where
  gcd := g4
  cofL := #p[1, 0, 0, 0, 1, 0, 0, 0, 1]
  cofR := #p[1, 0, 0, 0, 1]
  coprime := .constant 1 #p[0, 0, 0, 0, -1] 1

theorem cert_valid : ZPoly.checkGcd f g cert = true := by
  decide +kernel

open Polynomial

theorem gcd_X12_X8 (d : ℤ[X]) (h12 : d ∣ X ^ 12 - 1)
    (h8 : d ∣ X ^ 8 - 1) : d ∣ X ^ 4 - 1 := by
  have hc : ZPoly.CoprimeCofactors f g g4 :=
    ZPoly.coprimeCofactors_of_checkGcd cert_valid
  have := HexPolyZGcdMathlib.coprimeCofactors_greatest
    hc (HexPolyZMathlib.equiv.symm d)
  simp [f, g, g4,
    monomial_one_right_eq_X_pow] at this
  exact this h12 h8

end HexPolyZGcdChapter
```

The theorem {name}`Hex.ZPoly.checkGcd_sound` gives the factorizations
`X^12 - 1 = (X^4 - 1)(X^8 + X^4 + 1)` and `X^8 - 1 = (X^4 - 1)(X^4 + 1)` as
well, so `X^4 - 1` is a gcd of the two polynomials in `Polynomial ℤ`.

# Costs
%%%
tag := "hex-poly-z-gcd-costs"
%%%

For inputs of degree at most `n` with `b`-bit coefficients, Euclid's
algorithm over `ℚ[x]` performs `O(n)` divisions on numbers whose size can
grow exponentially with `n`, while the entries of the subresultant chain
have `O(n (b + log n))` bits. Brown's algorithm needs one gcd in `F_p[x]`,
of `O(n²)` word operations, for each prime. Its budget of primes comes from
the Landau–Mignotte bound for the inputs, but it stops at the first prime
whose reconstruction the checker accepts, which depends on the size of the
gcd and not on that of intermediate results. Checking a certificate costs
two packed integer products and a gcd of contents, and then, for a modular
witness, the reduction of the cofactors modulo `p` and two products in
`F_p[x]`, or, for an integral witness, two products in `ℤ[x]`.

The report `reports/hex-poly-z-gcd-performance.md` measures the library on
pseudo-random inputs, compiled, on one core of a shared machine
(`chungus2`, an AMD EPYC 9455). These are medians from its comparison with
Euclid's algorithm over `ℚ[x]`, run on the same inputs:

:::table +header
* * inputs
  * `ZPoly.gcd`
  * Euclid over `ℚ[x]`
* * coprime, degree 64
  * 1.35 ms
  * 589 ms
* * 8-bit factors, degree 128
  * 2.03 ms
  * 3265 ms
* * 256-bit factors, degree 32
  * 3.67 ms
  * 572 ms
* * 512-bit factors, degree 13, common factor `2x + 3`
  * 0.29 ms
  * 100 ms
:::

The coprime inputs have coefficients of 8 bits. Each other input is a
product of factors whose coefficients have the stated size, and the
inputs of degree 128 and 32 have a gcd of half the degree.
A separate run compared the library with FLINT's `fmpz_poly_gcd`, called
from Python through python-flint; the FLINT column includes about 0.013 ms
for the call itself. In that comparison the two cofactors differ by `1`:
the coprime pairs are `a` and `a + 1`, and the other pairs are `c a` and
`c (a + 1)` with `c` of half the degree. So the first remainder, method 2
above, is the gcd, which favours the library:

:::table +header
* * inputs
  * `ZPoly.gcd`
  * FLINT
* * coprime, degree 512
  * 0.97 ms
  * 0.36 ms
* * 8-bit factors, degree 512
  * 1.79 ms
  * 0.54 ms
* * 256-bit factors, degree 512
  * 22.8 ms
  * 73.8 ms
:::

On these inputs the library was between 2.3 and 3.3 times slower than FLINT
at degrees 64 to 512 with 8-bit factors, and faster with 256-bit factors. On polynomials with up to 128 distinct linear
factors and one repeated factor, {name}`Hex.ZPoly.sqfDecomp` was between 1.3
and 84 times faster than the HexPolyZ version, the gap growing with the
degree.

Replaying a certificate with `decide +kernel` is much slower than running
the checker as compiled code, and a certificate with a modular witness also
needs a proof that its prime is prime. The proof of `gcd_X12_X8` above uses
an integral witness, which needs no prime.

# Cross-references
%%%
tag := "hex-poly-z-gcd-cross-references"
%%%

* {ref "hex-poly-z"}[HexPolyZ] provides integer polynomials, content and
  primitive part, exact division, and the Landau–Mignotte bound.
* {ref "hex-poly-fp"}[HexPolyFp] provides the gcds and the extended
  Euclidean algorithm in `F_p[x]`.
* {ref "hex-modular"}[HexModular] provides the Chinese remaindering used by
  Brown's algorithm.
* {ref "hex-resultant"}[HexResultant] provides the extended subresultant
  chain.
* {ref "hex-mv-gcd"}[HexMvGcd] computes gcds of polynomials in several
  variables and uses this library in one variable.
