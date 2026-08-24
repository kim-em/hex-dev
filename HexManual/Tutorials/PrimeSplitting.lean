/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexBerlekampZassenhaus
import Mathlib.NumberTheory.KummerDedekind

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "Prime splitting via Kummer-Dedekind" =>
%%%
tag := "tutorial-prime-splitting"
%%%

# The story
%%%
tag := "tutorial-prime-splitting-story"
%%%

In the Gaussian integers `ℤ[i]`, the prime `5` stops being prime: it
factors as `(2 + i)(2 - i)`. The prime `3` stays prime. The prime `2`
does something stranger, becoming a unit times the *square* of `1 + i`.
Every prime of `ℤ` meets one of these three fates in `ℤ[i]`, and which
one is decided by a finite computation: factor `x² + 1` modulo
`p`. Two distinct roots mod `5`, no roots mod `3`, a repeated root
mod `2`.

That is not a coincidence about `ℤ[i]`; it is the first case of the
Kummer-Dedekind theorem, the standard dictionary between factoring a
polynomial over `𝔽ₚ` and factoring the ideal `(p)` in the ring of
integers of a number field. It is also exactly the computation the hex
factorization pipeline automates. This page takes two concrete number
fields, factors their defining polynomials modulo a handful of primes
with {ref "hex-poly-fp"}[`HexPolyFp`] and
{ref "hex-berlekamp"}[`HexBerlekamp`], and reads off the arithmetic of
primes upstairs, with
{ref "hex-berlekamp-zassenhaus"}[`HexBerlekampZassenhaus`] certifying
the inputs and several of the answers. The dictionary itself is quoted
number theory, stated carefully below but not re-proved here; the
closing section is precise about that boundary.

# Two number fields, certified
%%%
tag := "tutorial-prime-splitting-fields"
%%%

A number field is `K = ℚ(α)` for `α` a root of an irreducible integer
polynomial. This page works with two of them: `ℚ(i)`, defined by
`x² + 1`, and the cubic field `ℚ(∛2)`, defined by `x³ - 2`. Both
polynomials are {name}`Hex.ZPoly` values, dense integer polynomials
with coefficients listed from the constant term up.

Irreducibility is the entry ticket: it is what makes `ℚ(x)/(f)` a
*field* of degree `deg f` rather than a product of smaller pieces. The
executable check is {name}`Hex.ZPoly.isIrreducible`, which runs the
full Berlekamp-Zassenhaus factorizer {name}`Hex.ZPoly.factorize` and
inspects the result; the `irreducibility` elaborator then produces the
kernel-checked theorem, exactly as in
{ref "tutorial-aes-modulus"}[the AES modulus tutorial] but over `ℤ`.

```lean
open Hex

namespace PrimeSplittingTutorial

/-- `x² + 1`, the defining polynomial of `ℚ(i)`. -/
def fGauss : ZPoly := #p[1, 0, 1]

/-- `x³ - 2`, the defining polynomial of `ℚ(∛2)`. -/
def fCubic : ZPoly := #p[-2, 0, 0, 1]

-- Both pass the executable irreducibility check ...
#guard ZPoly.isIrreducible fGauss
#guard ZPoly.isIrreducible fCubic

-- ... because each is its own entire factorization.
#guard (ZPoly.factorize fGauss).factors
    = #[(fGauss, 1)]
#guard (ZPoly.factorize fGauss).scalar = 1
#guard (ZPoly.factorize fCubic).factors
    = #[(fCubic, 1)]

/-- Kernel-certified: `x² + 1` is irreducible. -/
theorem fGauss_irred : ZPoly.Irreducible fGauss :=
  irreducibility fGauss

/-- Kernel-certified: `x³ - 2` is irreducible. -/
theorem fCubic_irred : ZPoly.Irreducible fCubic :=
  irreducibility fCubic

end PrimeSplittingTutorial
```

The certified theorems are worth a remark each. For `x³ - 2` the
elaborator finds an Eisenstein-style witness at the prime `2`; for
`x² + 1`, which is Eisenstein at no prime, it finds a prime `p` where
the polynomial stays irreducible mod `p` and emits a single-prime
modular certificate. Both proof terms are replayed by the kernel on
literal data.

# The correspondence
%%%
tag := "tutorial-prime-splitting-kd"
%%%

Fix a number field `K = ℚ(α)` with `α` an algebraic integer, `f` its
monic minimal polynomial of degree `n`, and let `𝒪` be the ring of
integers of `K`. In `𝒪` a prime `p` of `ℤ` need not stay prime, but
unique factorization is restored at the level of ideals: the ideal
`(p)` factors uniquely as

```
(p) = P₁^e₁ · P₂^e₂ ⋯ P_r^e_r
```

with distinct prime ideals `Pᵢ`. Each `Pᵢ` has a *residue degree*
`fᵢ`, meaning its residue ring `𝒪/Pᵢ` is the finite field of `p^fᵢ`
elements, and the exponent `eᵢ` is its *ramification index*. The
invariants balance: `Σ eᵢ·fᵢ = n`, whatever `p` does.

The Kummer-Dedekind theorem computes all of it from one polynomial
factorization. Suppose `p` does not divide the conductor of `ℤ[α]`
(the caveat gets its own section below; for this page's two fields the
conductor is `1` and the hypothesis is vacuous). Factor the reduction
of `f` into monic irreducibles over `𝔽ₚ`:

```
f ≡ g₁^e₁ · g₂^e₂ ⋯ g_r^e_r  (mod p)
```

Then the primes of `𝒪` above `p` are exactly `Pᵢ = (p, gᵢ(α))`, one
per distinct factor, with residue degree `fᵢ = deg gᵢ` and
ramification index the multiplicity `eᵢ`. The three fates of the
opening section get their standard names from the shape of this data:
`p` *splits completely* when `r = n` (all factors linear and
distinct), is *inert* when `f` stays irreducible (`r = 1`, `e = 1`),
and *ramifies* when some `eᵢ > 1`, which for `p` prime to the
conductor happens exactly when `p` divides the discriminant of `f`.

# The mod-p pipeline
%%%
tag := "tutorial-prime-splitting-pipeline"
%%%

The right-hand side of the dictionary is a computation hex already
has, in three moves. {name}`Hex.ZPoly.modP` reduces the integer
polynomial to an {name}`Hex.FpPoly`.
{name}`Hex.FpPoly.squareFreeDecomposition` (Yun's algorithm) separates
the multiplicities, which matters precisely at the ramified primes.
{name}`Hex.Berlekamp.berlekampFactor` then splits each square-free
part into irreducibles, as described in the
{ref "hex-berlekamp"}[`HexBerlekamp` chapter]. Composing the three and
keeping only the shape `(deg gᵢ, eᵢ)` gives the splitting type as a
sorted list of (residue degree, ramification index) pairs.

```lean
open Hex

namespace PrimeSplittingTutorial

/-- The shape of `f mod p`: one
`(degree, multiplicity)` pair per distinct irreducible
factor, sorted. Under Kummer-Dedekind, each pair is a
prime above `p` with that residue degree and
ramification index. -/
def splittingType (p : Nat) [ZMod64.Bounds p]
    [ZMod64.PrimeModulus p] (f : FpPoly p) :
    List (Nat × Nat) :=
  let dec := FpPoly.squareFreeDecomposition
    ZMod64.PrimeModulus.prime f
  let pairs := dec.factors.flatMap fun sf =>
    if h : DensePoly.leadingCoeff sf.factor = 1 then
      (Berlekamp.berlekampFactor sf.factor
          (by exact h)).factors.map
        fun g => (g.size - 1, sf.multiplicity)
    else
      [(sf.factor.size - 1, sf.multiplicity)]
  pairs.mergeSort fun a b =>
    decide (a.1 < b.1) ||
      (a.1 == b.1 && decide (a.2 ≤ b.2))

/-- Coefficients as naturals, for readable factors. -/
def coeffNats {p : Nat} [ZMod64.Bounds p]
    (f : FpPoly p) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

-- The primes this page visits, with machine-word
-- bounds and primality facts as instances.
private instance pm2 : ZMod64.PrimeModulus 2 :=
  ⟨by decide⟩
private instance b3 : ZMod64.Bounds 3 :=
  ⟨by decide, by decide⟩
private instance pm3 : ZMod64.PrimeModulus 3 :=
  ⟨by decide⟩
private instance b5 : ZMod64.Bounds 5 :=
  ⟨by decide, by decide⟩
private instance pm5 : ZMod64.PrimeModulus 5 :=
  ⟨by decide⟩
private instance b7 : ZMod64.Bounds 7 :=
  ⟨by decide, by decide⟩
private instance pm7 : ZMod64.PrimeModulus 7 :=
  ⟨by decide⟩
private instance b13 : ZMod64.Bounds 13 :=
  ⟨by decide, by decide⟩
private instance pm13 : ZMod64.PrimeModulus 13 :=
  ⟨by decide⟩
private instance b31 : ZMod64.Bounds 31 :=
  ⟨by decide, by decide⟩
private instance pm31 : ZMod64.PrimeModulus 31 :=
  ⟨by decide⟩

end PrimeSplittingTutorial
```

The `if` branch is not dead code in general (Berlekamp's precondition
is a monic input), but for the monic polynomials this page reduces it
never fires: every square-free factor Yun returns is monic. Note what
`splittingType` is: an honest computation, checked below by `#guard`
against independently known number theory. The kernel-certified
variant of the same factorizations appears in
{ref "tutorial-prime-splitting-certified"}[a later section].

# The Gaussian integers
%%%
tag := "tutorial-prime-splitting-gauss"
%%%

For `K = ℚ(i)` the ring of integers is `ℤ[i]` itself, the conductor is
`1`, and the discriminant is `-4`, so Kummer-Dedekind applies at every
prime and ramification can only happen at `2`.

```lean
open Hex

namespace PrimeSplittingTutorial

-- p = 2: x² + 1 ≡ (x + 1)², ramified:
-- (2) = (2, i + 1)² = (1 + i)².
#guard splittingType 2 (ZPoly.modP 2 fGauss)
    = [(1, 2)]

-- p = 3: x² + 1 irreducible mod 3, inert: (3) stays
-- prime with residue field of 9 elements.
#guard splittingType 3 (ZPoly.modP 3 fGauss)
    = [(2, 1)]

-- p = 5 and p = 13: two distinct roots, split.
#guard splittingType 5 (ZPoly.modP 5 fGauss)
    = [(1, 1), (1, 1)]
#guard splittingType 13 (ZPoly.modP 13 fGauss)
    = [(1, 1), (1, 1)]

-- Mod 13 the roots are 5 and 8: the factors are
-- x - 5 and x - 8, stored as x + 8 and x + 5.
def g13 : FpPoly 13 := #p[1, 0, 1]
#guard ZPoly.modP 13 fGauss == g13
theorem g13_monic : DensePoly.Monic g13 := by rfl

#guard ((Berlekamp.berlekampFactor g13 g13_monic)
  |>.factors.map coeffNats) == [[8, 1], [5, 1]]

end PrimeSplittingTutorial
```

Reading the mod-13 factorization through the dictionary: the primes
above `13` are `(13, i - 5)` and `(13, i - 8)`, each with residue
degree one. And indeed `13 = (3 + 2i)(3 - 2i)` in `ℤ[i]`, with
`i ≡ 5 (mod 3 + 2i)`: the ideal-theoretic answer collapses to honest
element factorizations because `ℤ[i]` is a principal ideal domain.

The split/inert dichotomy here is a theorem of Fermat in disguise:
`x² + 1` has a root mod an odd `p` exactly when `p ≡ 1 (mod 4)`, so
the primes that split in `ℤ[i]`, equivalently the primes that are sums
of two squares, are exactly those congruent to `1` mod `4`. The
`#guard`s above are four instances of that pattern, computed by
Berlekamp factorization rather than quadratic reciprocity.

# A cubic field
%%%
tag := "tutorial-prime-splitting-cubic"
%%%

The field `ℚ(∛2)` is more interesting: its Galois closure has group
`S₃`, so primes have five possible fates rather than three, and which
one occurs is no longer a congruence condition on `p` alone. The ring
of integers is `ℤ[∛2]` (conductor `1` again), and the discriminant of
`x³ - 2` is `-108 = -2²·3³`, so exactly `2` and `3` ramify.

```lean
open Hex

namespace PrimeSplittingTutorial

-- p = 2: x³ - 2 ≡ x³, totally ramified:
-- (2) = (2, ∛2)³ = (∛2)³.
#guard splittingType 2 (ZPoly.modP 2 fCubic)
    = [(1, 3)]

-- p = 3: x³ - 2 ≡ (x + 1)³, totally ramified.
#guard splittingType 3 (ZPoly.modP 3 fCubic)
    = [(1, 3)]

-- p = 5: one root (3³ = 27 ≡ 2) and an irreducible
-- quadratic: a degree-1 and a degree-2 prime.
#guard splittingType 5 (ZPoly.modP 5 fCubic)
    = [(1, 1), (2, 1)]

-- p = 7: no cube root of 2 mod 7, inert.
#guard splittingType 7 (ZPoly.modP 7 fCubic)
    = [(3, 1)]

-- p = 31: totally split. 2 ≡ 4³ mod 31, and the
-- roots are 4, 7, and 20.
#guard splittingType 31 (ZPoly.modP 31 fCubic)
    = [(1, 1), (1, 1), (1, 1)]

def g31 : FpPoly 31 := #p[29, 0, 0, 1]
#guard ZPoly.modP 31 fCubic == g31
theorem g31_monic : DensePoly.Monic g31 := by rfl

-- The factors x - 4, x - 7, x - 20, stored as
-- x + 27, x + 24, x + 11.
#guard ((Berlekamp.berlekampFactor g31 g31_monic)
  |>.factors.map coeffNats)
    == [[27, 1], [24, 1], [11, 1]]

-- Whatever the shape, residue degrees weighted by
-- ramification indices sum to the field degree.
#guard ((splittingType 5 (ZPoly.modP 5 fCubic)).foldl
  (fun s df => s + df.1 * df.2) 0) = 3

end PrimeSplittingTutorial
```

The unramified shapes follow the cubic-residue arithmetic of `2`. For
`p ≡ 2 (mod 3)` cubing is a bijection on `𝔽ₚ`, so `x³ - 2` has
exactly one root and the shape is always a line times a conic, as at
`p = 5`. For `p ≡ 1 (mod 3)` the cubes form an index-three subgroup:
if `2` lands in it the polynomial splits completely, as at `p = 31`;
if not there are no roots at all and `p` is inert, as at `p = 7`.

There is a deeper pattern behind which shape occurs how often. The
splitting type of an unramified `p` is the cycle type of its Frobenius
element in the Galois group `S₃`, and the Chebotarev density theorem
says each conjugacy class is hit with frequency proportional to its
size: totally split with density `1/6`, the line-times-conic shape
with density `1/2`, inert with density `1/3`. The five primes above
are a small sample; the density statement is what the sample is drawn
from.

# Certified splittings
%%%
tag := "tutorial-prime-splitting-certified"
%%%

`splittingType` is compiled code checked by `#guard`. For a
kernel-checked account of the same factorizations, the `factor_poly`
and `irreducibility` elaborators from
{ref "hex-berlekamp"}[`HexBerlekamp`] emit certificate-backed proof
terms over `FpPoly p`, as described in
{ref "factor-tactics"}[the factor tactics chapter].

```lean
open Hex

namespace PrimeSplittingTutorial

/-- A certified factorization of `x² + 1` mod 13: the
`factors_mul` and `factors_irred` fields are proofs,
replayed by the kernel from Rabin certificates. -/
noncomputable def fac13 := factor_poly g13

example : fac13.factors = [#p[8, 1], #p[5, 1]] := by
  rfl
example : fac13.scalar = 1 := rfl

def g7 : FpPoly 7 := #p[5, 0, 0, 1]
#guard ZPoly.modP 7 fCubic == g7

/-- Kernel-certified inertness: `x³ - 2` stays
irreducible mod 7. -/
theorem g7_irred : FpPoly.Irreducible g7 :=
  irreducibility g7

end PrimeSplittingTutorial
```

A {name}`Hex.FpPoly.Factored` value is not a list of factors that some
compiled routine printed: its `factors_mul` field proves the product
reconstructs `g13` and its `factors_irred` field proves each listed
factor irreducible, so the mod-13 splitting data above `13` is backed
by a kernel-checked factorization. Likewise `g7_irred` is precisely
the "inert" claim for `7` in `ℚ(∛2)`, in certified form.

# The conductor caveat
%%%
tag := "tutorial-prime-splitting-conductor"
%%%

Kummer-Dedekind's hypothesis was stated above and now has to be taken
seriously: the dictionary reads factorizations of `f mod p` correctly
only when `p` does not divide the conductor of `ℤ[α]` in `𝒪`, the
largest ideal of `𝒪` contained in `ℤ[α]`. A prime dividing the
conductor also divides the index `(𝒪 : ℤ[α])`, and the discriminants
keep the books: `disc f = (𝒪 : ℤ[α])² · disc K`. When `ℤ[α]` is all
of `𝒪`, as for `ℤ[i]` and `ℤ[∛2]`, the conductor is `1` and every
prime is safe, which is why the sections above could proceed without
comment.

The caveat is not hypothetical, and Dedekind found the smallest
counterexample: `K = ℚ(θ)` for `θ` a root of `x³ - x² - 2x - 8`. Here
`disc f = -2012 = 2²·(-503)` while `disc K = -503`, so the index is
`2`, and at `p = 2` the dictionary misreads:

```lean
open Hex

namespace PrimeSplittingTutorial

/-- Dedekind's cubic `x³ - x² - 2x - 8`. -/
def fDedekind : ZPoly := #p[-8, -2, -1, 1]

#guard ZPoly.isIrreducible fDedekind

-- Mod 2 the polynomial is x²·(x + 1), which would
-- read as one ramified prime and one unramified one.
#guard splittingType 2 (ZPoly.modP 2 fDedekind)
    = [(1, 1), (1, 2)]

end PrimeSplittingTutorial
```

The computed factorization is perfectly correct *as a factorization
mod 2*; what fails is the dictionary. The true splitting, computed
with the full ring of integers, is that `2` splits completely: three
distinct primes of residue degree one, no ramification at all
(consistent with `2` not dividing `disc K = -503`). No better choice
of `θ` fixes it, and the obstruction is charmingly finite: three
distinct degree-one primes would require three distinct monic linear
polynomials over `𝔽₂`, and there are only two. So *every* generator
of this field has even index, `2` divides every conductor, and the
polynomial dictionary is silent at `2` no matter which defining
polynomial one factors. Primes like this are called common index
divisors, and they are the precise reason the theorem carries its
hypothesis.

# What was computed, and what was proved
%%%
tag := "tutorial-prime-splitting-boundary"
%%%

Three grades of evidence appear on this page, and the point of the
page is lost if they blur.

The `#guard`s, including everything `splittingType` produced, are
computations: evaluated when the manual builds, by the compiled
factorization code a caller would run, and checked by the evaluator
against expected values. They are tests, not theorems.

The `irreducibility` and `factor_poly` results (`fGauss_irred`,
`fCubic_irred`, `fac13`, `g7_irred`) are kernel-checked theorems about
polynomials: the kernel replays a certificate check on literal data,
and library soundness theorems convert the passing check into
irreducibility and product statements. What is certified is the
polynomial factorization, on both sides of the reduction mod `p`.

The dictionary between those factorizations and ideals, the
Kummer-Dedekind theorem itself, is imported number theory: this page
states it and instantiates it in prose, and nothing here formalizes
the ideal-theoretic side. That theorem does exist in formalized form,
as Mathlib's
{name}`KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk`,
a bijection between the primes above `p` and the irreducible factors
of the reduced minimal polynomial, conductor hypothesis and all.
Connecting hex's executable factor lists to that statement, through
the correspondence layers described in
{ref "hex-berlekamp-zassenhaus"}[the `HexBerlekampZassenhaus` chapter],
is exactly the kind of bridge the `*Mathlib` companion libraries
exist for; this page stops at the polynomial boundary and says so.

# Cross-references
%%%
tag := "tutorial-prime-splitting-cross-references"
%%%

* {ref "hex-berlekamp-zassenhaus"}[`HexBerlekampZassenhaus`] documents
  {name}`Hex.ZPoly.factorize`, the integer factorizer whose
  irreducibility checks anchor this page's number fields.
* {ref "hex-berlekamp"}[`HexBerlekamp`] is the mod-`p` factorization
  engine: Berlekamp's algorithm, Rabin's test, and the certificate
  checkers behind `factor_poly` and `irreducibility`.
* {ref "hex-poly-fp"}[`HexPolyFp`] provides the prime-field
  polynomials, including the square-free decomposition that detects
  ramification.
* {ref "factor-tactics"}[The factor tactics] chapter documents the
  elaborators used in the certified section, including their
  Mathlib-facing forms.
* {ref "tutorial-aes-modulus"}[Why the AES modulus works] is the same
  certificate story at a single prime, told slowly.
