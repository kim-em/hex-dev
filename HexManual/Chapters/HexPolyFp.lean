/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexPolyFp

import HexPolyFpMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolyFp: prime-field dense polynomials" =>
%%%
tag := "hex-poly-fp"
%%%

# Introduction
%%%
tag := "hex-poly-fp-intro"
%%%

`HexPolyFp` specializes the executable dense polynomials to
coefficients in `Hex.ZMod64 p`. Where {ref "hex-poly"}[`HexPoly`]
is generic over any coefficient type with a `Zero` and a `DecidableEq`,
`HexPolyFp` fixes the coefficients to machine-word residues modulo a
prime `p` and adds the operations that only make sense over `` `Fₚ` ``:
modular exponentiation and composition in `` `Fₚ[x] / (f)` ``, the
Frobenius-power maps `X ↦ X^(pᵏ)`, square-free (Yun) decomposition, and
the quotient by a modulus, which becomes a field exactly when the
modulus is irreducible.

{name}`Hex.FpPoly` is a thin `abbrev` over
{name}`Hex.DensePoly`, so the entire constructor, arithmetic, and
Euclidean API documented in the {ref "hex-poly"}[`HexPoly` chapter] is
available unchanged. This chapter covers only what the prime-field
specialization adds on top. `HexPolyFp` is Mathlib-free. It depends on
{ref "hex-poly"}[`HexPoly`] for the representation and on
{ref "hex-mod-arith"}[`HexModArith`] for the `ZMod64 p` coefficient
arithmetic. See {ref "hex-poly-fp-cross-references"}[Cross-references].

# The prime-field polynomial type
%%%
tag := "hex-poly-fp-type"
%%%

A prime-field polynomial is a dense polynomial whose coefficients are
`ZMod64 p` residues. The `ZMod64.Bounds p` instance carries the proof
that `p` fits in a machine word, so arithmetic stays in the fast path.

{docstring Hex.FpPoly}

Because {name}`Hex.FpPoly` unfolds to {name}`Hex.DensePoly`, the
`HexPolyFp` namespace re-exports the constructors and queries a caller
needs for the specialized type. {name}`Hex.FpPoly.ofCoeffs` builds a
polynomial from a coefficient array, {name}`Hex.FpPoly.X` is the
indeterminate, and {name}`Hex.FpPoly.modByMonic` reduces modulo a monic
divisor. The irreducibility predicate the field operations require as a
hypothesis is also stated here.

{docstring Hex.FpPoly.Irreducible}

# Principal operations
%%%
tag := "hex-poly-fp-operations"
%%%

The headline operations all work in the quotient ring
`` `Fₚ[x] / (f)` `` for a monic modulus `f`. Modular exponentiation
raises a base to a power and reduces, and modular composition
substitutes one polynomial into another and reduces. Both use
Horner-style loops that re-reduce at every step, so intermediate
results never grow past the modulus degree.

{docstring Hex.FpPoly.powModMonic}

{docstring Hex.FpPoly.composeModMonic}

The finite-field irreducibility and factorization tests are built on the
Frobenius-power maps. {name}`Hex.FpPoly.frobeniusXMod` computes
`X^p mod f`, and {name}`Hex.FpPoly.frobeniusXPowMod`
iterates it to `X^(pᵏ) mod f` for arbitrary `k`.

{docstring Hex.FpPoly.frobeniusXMod}

{docstring Hex.FpPoly.frobeniusXPowMod}

Square-free decomposition runs Yun's algorithm over `` `Fₚ` ``. The
result bundles a scalar unit with a list of square-free factors and
their multiplicities. The two record types name those pieces.

{docstring Hex.FpPoly.SquareFreeFactor}

{docstring Hex.FpPoly.SquareFreeDecomposition}

{docstring Hex.FpPoly.squareFreeDecomposition}

The inverse operation reassembles a polynomial from a decomposition by
raising each factor to its multiplicity and multiplying. It is the
reconstruction side of the correctness laws below.

{docstring Hex.FpPoly.weightedProduct}

# The quotient by a modulus
%%%
tag := "hex-poly-fp-quotient"
%%%

`HexPolyFp` packages the quotient `` `Fₚ[x] / (g)` `` as a type of
canonical representatives: each element stores the unique polynomial of
degree below the modulus, together with a proof of that bound.

{docstring Hex.FpPoly.Quotient}

The quotient is unconditionally a commutative ring. It becomes a
*field* only when `g` is irreducible, and `HexPolyFp` parametrizes
over that fact rather than deciding it. There is no unconditional
unconditional field instance. Instead the field-promoting laws are theorems that
take {name}`Hex.FpPoly.Irreducible` of `g` as an explicit hypothesis. A downstream
caller supplies an irreducibility witness (in practice a checkable
Rabin certificate from `HexBerlekamp`), and only then are inverses
available. The inverse-cancellation laws are stated in
{ref "hex-poly-fp-key-correctness"}[Key correctness theorems].

## Worked example: arithmetic over F₅
%%%
tag := "hex-poly-fp-worked-example"
%%%

The block below works over `FpPoly 5`. It fixes the monic quadratic
modulus `x² + 2` (whose reduction rule is `x² ≡ -2 ≡ 3 (mod 5)`) and a
linear modulus `x + 3`, then runs modular exponentiation, Frobenius,
composition, weighted products, and square-free decomposition. The
helper `coeffNats` converts a polynomial to a list of natural-number
coefficients. The expected values are the same ones pinned by the
library's conformance suite.

```lean
open Hex Hex.FpPoly

namespace HexPolyFpChapterExample

local instance boundsFive : ZMod64.Bounds 5 :=
  ⟨by decide, by decide⟩

private theorem prime_five : Hex.Nat.Prime 5 := by decide

private def coeffNats (f : FpPoly 5) : List Nat :=
  f.toArray.toList.map ZMod64.toNat

private def sfSummary
    (d : SquareFreeDecomposition 5) :
    Nat × List (List Nat × Nat) :=
  (d.unit.toNat,
    d.factors.map
      (fun sf => (coeffNats sf.factor, sf.multiplicity)))

private def sfReconstruction
    (d : SquareFreeDecomposition 5) : FpPoly 5 :=
  .C d.unit * weightedProduct d.factors

-- Monic modulus x² + 2 over F₅, with x² ≡ 3.
private def quadModulus : FpPoly 5 := #p[2, 0, 1]

private theorem quadModulus_monic :
    DensePoly.Monic quadModulus := by rfl

-- Monic linear modulus x + 3 over F₅.
private def linearModulus : FpPoly 5 := #p[3, 1]

private theorem linearModulus_monic :
    DensePoly.Monic linearModulus := by rfl

-- (x + 1)³ mod (x² + 2) ≡ x.
#guard
  coeffNats
    (powModMonic #p[1, 1] quadModulus
      quadModulus_monic 3) = [0, 1]
-- Exponent zero is the quotient-ring identity 1.
#guard
  coeffNats
    (powModMonic #p[0, 0, 1] quadModulus
      quadModulus_monic 0) = [1]
-- Frobenius generator X⁵ mod (x² + 2) ≡ 4x.
#guard
  coeffNats
    (frobeniusXMod quadModulus quadModulus_monic)
      = [0, 4]
-- X⁵ mod (x + 3) ≡ 2, a constant.
#guard
  coeffNats
    (frobeniusXMod linearModulus linearModulus_monic)
      = [2]
-- frobeniusXPowMod _ _ 0 reduces X.
#guard
  coeffNats
    (frobeniusXPowMod quadModulus quadModulus_monic 0)
      = [0, 1]
-- Compose (3 + 2x + x²) with (1 + x) mod (x² + 2).
#guard
  coeffNats
    (composeModMonic #p[3, 2, 1] #p[1, 1]
      quadModulus quadModulus_monic)
      = [4, 4]
-- The weighted product of (x + 1)² is x² + 2x + 1.
#guard
  coeffNats
    (weightedProduct
      [{ factor := #p[1, 1], multiplicity := 2 }])
      = [1, 2, 1]
-- The empty product is the constant 1.
#guard
  coeffNats
    (weightedProduct
      ([] : List (SquareFreeFactor 5)))
      = [1]
-- Square-free decomposition: x² + 2x + 1 = (x + 1)².
#guard
  sfSummary
    (squareFreeDecomposition prime_five
      #p[1, 2, 1])
      = (1, [([1, 1], 2)])
-- The decomposition reconstructs its input.
#guard
  let f : FpPoly 5 := #p[1, 2, 1]
  coeffNats
    (sfReconstruction
      (squareFreeDecomposition prime_five f))
      = coeffNats f

end HexPolyFpChapterExample
```

# Key correctness theorems
%%%
tag := "hex-poly-fp-key-correctness"
%%%

The executable operations are pinned to their mathematical meaning.
Modular composition agrees with the spelled-out "compose then take the
remainder" definition, and the Frobenius iterate reduces to
`X^(pᵏ) mod f`. That last identity is the one Rabin's
irreducibility test relies on.

{docstring Hex.FpPoly.composeModMonic_eq_mod}

{docstring Hex.FpPoly.frobeniusXPowMod_mod_eq_monomial_mod}

Square-free decomposition is correct in two senses: every emitted
factor is genuinely square-free, and the unit-times-weighted-product
reconstructs the original polynomial. The multiplicities are positive,
so the factor list carries no padding.

{docstring Hex.FpPoly.squareFreeDecomposition_factors_squareFree}

{docstring Hex.FpPoly.squareFreeDecomposition_weightedProduct}

{docstring Hex.FpPoly.squareFreeDecomposition_multiplicity_pos}

The field-promoting laws on the quotient are the inverse-cancellation
theorems. Each carries `FpPoly.Irreducible g` as a hypothesis: for an
irreducible modulus every nonzero quotient element has a genuine
two-sided multiplicative inverse, which is exactly what fails for a
reducible modulus (where a nonzero zero-divisor has no inverse).

{docstring Hex.FpPoly.Quotient.mul_inv_cancel}

{docstring Hex.FpPoly.Quotient.inv_mul_cancel}

# The Mathlib correspondence
%%%
tag := "hex-poly-fp-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexPolyFpMathlib` is
the companion that connects it to Mathlib, and this section is where
that library is documented. It is the crossing point for the whole
executable polynomial tower, not only for this chapter's library:
below it a reader is in Hex's own {name}`Hex.DensePoly` over
{name}`Hex.ZMod64`, and on the far side of it in Mathlib's
`Polynomial (ZMod p)`.

{docstring HexPolyFpMathlib.fpPolyEquiv}

The equivalence asks only for {name}`Hex.ZMod64.Bounds`, not for
primality. `FpPoly p` is a commutative ring for every admissible modulus,
meaning every `p` with `0 < p` and `p < 2 ^ 31`, which is what that class
requires; `Polynomial (ZMod p)` is one for any `p` at all; and nothing in
the correspondence divides. So there is no reason to demand more of `p`
than the representation itself does. Primality enters at exactly one
declaration, and as an explicit hypothesis.

{docstring HexPolyFpMathlib.primeModulus_of_fact}

That is the door from Mathlib's `Fact (Nat.Prime p)` to the executable
{name}`Hex.ZMod64.PrimeModulus` witness that the field-dependent
operations require: coefficient inversion, the Bezout gcd, and modular
division, and everything in
{ref "hex-poly-fp-quotient"}[The quotient by a modulus] built on them. A
caller who is already working in Mathlib supplies the `Fact` and gets the
witness; a caller staying on the executable side never needs the `Fact`.

## The forward map
%%%
tag := "hex-poly-fp-mathlib-forward"
%%%

Downstream statements are written against a named forward map rather
than against the equivalence, so that a goal about an executable
polynomial's Mathlib image carries no `RingEquiv` coercion.

{docstring HexPolyFpMathlib.toMathlibPolynomial}

{docstring HexPolyFpMathlib.coeff_toMathlibPolynomial}

The coefficient lemma is the normal form for the whole layer. Nearly
every transport below is proved by taking coefficients on both sides and
rewriting with it, and it is the `simp` rule a downstream proof reaches
for first.

{docstring HexPolyFpMathlib.toMathlibPolynomial_monic}

Monicity is the hypothesis the executable Euclidean operations carry, so
transporting it is what lets a Mathlib-side argument apply
`Polynomial.Monic` lemmas to a polynomial that came out of
{name}`Hex.FpPoly.modByMonic` or out of the square-free decomposition.

## The transport family
%%%
tag := "hex-poly-fp-mathlib-transport"
%%%

The forward map is a ring equivalence, so each of the following follows
from it. They are stated anyway: a caller reaching for one of them
should not have to rediscover which `RingEquiv` lemma to compose, and
the rewrite-friendly form is what the finite-field proofs actually use.

{docstring HexPolyFpMathlib.toMathlibPolynomial_add}

{docstring HexPolyFpMathlib.toMathlibPolynomial_sub}

{docstring HexPolyFpMathlib.toMathlibPolynomial_mul}

{docstring HexPolyFpMathlib.toMathlibPolynomial_derivative}

The derivative is the one that does not come free from the ring
structure; it is proved coefficientwise. It is also the one the
square-free correctness arguments need, since Yun's algorithm is stated
in terms of the gcd of a polynomial with its derivative.

The generators transport too, so a Mathlib-side computation can be
rewritten all the way down to `X` and constants.

{docstring HexPolyFpMathlib.toMathlibPolynomial_C}

{docstring HexPolyFpMathlib.toMathlibPolynomial_X}

{docstring HexPolyFpMathlib.toMathlibPolynomial_monomial_one}

{docstring HexPolyFpMathlib.toMathlibPolynomial_dvd}

That last one is the forward direction only: it is proved from a
multiplication witness and
{name}`HexPolyFpMathlib.toMathlibPolynomial_mul`, with no division and no
gcd. The equivalence can reflect such a witness backward just as well, so
the two-sided `dvd_iff` is a gap in the current API rather than a
property of the correspondence. It is tracked as
[hex-dev issue 9370](https://github.com/kim-em/hex-dev/issues/9370),
along with the rest of the inverse transport family. What genuinely does
not belong here is a
statement mentioning Berlekamp's basis size or Rabin's test, even when
its conclusion is about
{name}`HexPolyFpMathlib.toMathlibPolynomial`: that is a fact about a
factoring algorithm rather than about the representation, and it lives in
`HexBerlekampMathlib`.

## Mathlib algebraic structure
%%%
tag := "hex-poly-fp-mathlib-instances"
%%%

A `RingEquiv` does not install a `CommRing`. Without one,
`Hex.FpPoly p →+* R` is not a well-formed type, so the instance is a
prerequisite for every ring homomorphism out of the executable
polynomials rather than a convenience.

{docstring HexPolyFpMathlib.commRing}

The design point is worth restating, because the obvious alternative is
the wrong one. Transporting a `CommRing` along
{name}`HexPolyFpMathlib.fpPolyEquiv` would produce a correct instance
whose operations are Mathlib's: `f * g` would mean "map both sides into
`Polynomial (ZMod p)`, multiply there, map back", and none of the
executable convolution would run. Building the instance from the laws
`HexPolyFp` proves keeps the operations the executable ones, so
multiplication under it is still the schoolbook loop.

```lean
open Hex in
example {p : Nat} [ZMod64.Bounds p]
    (f g : FpPoly p) :
    f * g = DensePoly.mul f g := rfl
```

Mathlib's ring automation therefore applies directly to the fast
representation:

```lean
open Hex in
example {p : Nat} [ZMod64.Bounds p]
    (f g : FpPoly p) :
    (f + g) ^ 2 = f ^ 2 + 2 * (f * g) + g ^ 2 := by
  ring
```

One executable operation needs to be identified with its Mathlib
counterpart by hand, because `HexPolyFp` defines it by structural
recursion for kernel reduction while the `CommRing` above supplies
`npowRec`.

{docstring HexPolyFpMathlib.linearPow_eq_pow}

Finally, a naming note for readers of older code. The equivalence and
its transports lived in `HexBerlekampMathlib` while Berlekamp factoring
was their only consumer, and that library still re-exports the
correspondence names, so a call site spelling one of them
`HexBerlekampMathlib.toMathlibPolynomial` keeps resolving.

# Cross-references
%%%
tag := "hex-poly-fp-cross-references"
%%%

`HexPolyFp` builds on the generic dense polynomials and supplies
the prime-field specialization the finite-field libraries use:

* {ref "hex-poly"}[`HexPoly`] is the generic dense-polynomial library.
  {name}`Hex.FpPoly` is an `abbrev` over {name}`Hex.DensePoly`, so every
  constructor, arithmetic, evaluation, and Euclidean operation
  documented in that chapter is inherited at the specialized type. The
  concrete {name}`Hex.DensePoly.DivModLaws` and
  {name}`Hex.DensePoly.GcdLaws` the generic Euclidean laws are stated
  under are discharged here for {name}`Hex.ZMod64` at modulus `p`.
* {ref "hex-mod-arith"}[`HexModArith`] supplies {name}`Hex.ZMod64` at modulus `p`
  coefficient arithmetic: the machine-word modular add, multiply, and
  inverse that every operation in this chapter ultimately calls, along
  with the {name}`Hex.ZMod64.Bounds`/{name}`Hex.ZMod64.PrimeModulus` instances the
  prime-field operations require.

Downstream, the finite-field libraries consume `HexPolyFp` directly:
`HexGFqRing` builds the quotient ring `` `Fₚ[x] / (g)` `` and
{ref "hex-gfq-field"}[`HexGFqField`] promotes it to a field using the
inverse laws documented above, each conditioned on irreducibility of the
modulus, with the {name}`Hex.FpPoly.Irreducible` witness produced by a
checkable Rabin certificate from `HexBerlekamp`.

`HexPolyFp` is Mathlib-free. Its Mathlib correspondence is
`HexPolyFpMathlib`, documented in
{ref "hex-poly-fp-mathlib"}[The Mathlib correspondence] above, which
identifies {name}`Hex.FpPoly` with `Polynomial (ZMod p)` and carries the
`CommRing` instance that every ring homomorphism out of the executable
polynomials needs. Nothing in this chapter depends on it: the modular
exponentiation, the Frobenius maps, the square-free decomposition, and
the quotient are all executable and Mathlib-free.
