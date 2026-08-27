/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexPolyZ.Decomposition
import HexPolyZ.Mignotte
import HexPolyZMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolyZ: integer dense polynomials" =>
%%%
tag := "hex-poly-z"
%%%

# Introduction
%%%
tag := "hex-poly-z-intro"
%%%

`HexPolyZ` specializes {ref "hex-poly"}[HexPoly] to integer
coefficients and adds the integer-specific theory the factorization
algorithm needs. It contributes three things: the *content* and
*primitive part* (Gauss's-lemma factorization of an integer polynomial
into a scalar times a primitive polynomial), a *coefficientwise
congruence* predicate used by Hensel lifting, and a conservative
executable *Mignotte coefficient bound* on the coefficients of any
integer factor.

The library is Mathlib-free and depends only on `HexPoly`. `HexHensel`
and the integer-factorization libraries consume it in turn. The
mathematical justification of the Mignotte bound, that these executable
quantities really do bound the coefficients of a factor, is proved in
`HexPolyZMathlib`. See
{ref "hex-poly-z-cross-references"}[Cross-references].

# Integer polynomial type
%%%
tag := "hex-poly-z-type"
%%%

There is no new structure: an integer polynomial is just a normalized
dense polynomial with `Int` coefficients, so the whole `HexPoly` API
(constructors, arithmetic, evaluation, Euclidean division over `Rat`)
is available unchanged. `HexPolyZ` adds operations for {name}`Hex.ZPoly`.

{docstring Hex.ZPoly}

# Content and primitive part
%%%
tag := "hex-poly-z-content"
%%%

Every nonzero integer polynomial factors as a scalar (its content, the
nonnegative gcd of the coefficients) times a primitive polynomial whose
coefficients have gcd `1`. These two operations are the integer
analogue of normalizing to a monic polynomial over a field.

{docstring Hex.ZPoly.content}

{docstring Hex.ZPoly.primitivePart}

{docstring Hex.ZPoly.Primitive}

A related substitution, used when transferring a factor of a monic
transform back to the original polynomial, scales the variable rather
than the polynomial.

{docstring Hex.ZPoly.dilate}

{docstring Hex.ZPoly.coeff_dilate}

The unit polynomials are exactly the two constants `1` and `-1`, and
this is a decidable predicate.

{docstring Hex.ZPoly.IsUnit}

{docstring Hex.ZPoly.isUnit_iff}

## Worked example: content and primitive part
%%%
tag := "hex-poly-z-worked-content"
%%%

The block below builds `f = 2 + 4x + 6x²`, reads off its content and
primitive part, and checks the reconstruction law and a dilation.

```lean
open Hex Hex.DensePoly

namespace HexPolyZChapterContent

-- f = 2 + 4x + 6x²
private def f : ZPoly := #p[2, 4, 6]

-- The content is the nonnegative gcd of the
-- coefficients; the primitive part divides it out.
#guard ZPoly.content f = 2
#guard (ZPoly.primitivePart f).toArray.toList = [1, 2, 3]

-- Scaling the primitive part by the content
-- reconstructs f.
#guard scale (ZPoly.content f) (ZPoly.primitivePart f) = f

-- A polynomial whose coefficients are coprime is
-- already primitive: its content is 1.
#guard ZPoly.content #p[1, 2, 3] = 1

-- Dilation X ↦ 2·X scales coefficient i by 2ⁱ.
private def g : ZPoly := #p[1, 1, 1]
#guard (ZPoly.dilate 2 g).toArray.toList = [1, 2, 4]

end HexPolyZChapterContent
```

# Congruence for Hensel lifting
%%%
tag := "hex-poly-z-congruence"
%%%

Hensel lifting works modulo a prime power, so `HexPolyZ` carries a
coefficientwise congruence predicate and the notion of two polynomials
being coprime modulo `p`.

{docstring Hex.ZPoly.congr}

{docstring Hex.ZPoly.coprimeModP}

The congruence is an equivalence relation and is compatible with the
ring operations, so Hensel-step reasoning can rewrite under it.

{docstring Hex.ZPoly.congr_refl}

{docstring Hex.ZPoly.congr_symm}

{docstring Hex.ZPoly.congr_trans}

{docstring Hex.ZPoly.congr_add}

{docstring Hex.ZPoly.congr_mul}

# Content multiplicativity
%%%
tag := "hex-poly-z-content-laws"
%%%

The defining laws of the content/primitive-part decomposition are its
reconstruction identity and Gauss's lemma: content is multiplicative,
and the primitive part of a product is the product of the primitive
parts.

{docstring Hex.ZPoly.content_mul_primitivePart}

{docstring Hex.ZPoly.content_dvd_coeff}

{docstring Hex.ZPoly.content_mul}

{docstring Hex.ZPoly.primitivePart_mul}

{docstring Hex.ZPoly.primitive_mul}

# The Mignotte coefficient bound
%%%
tag := "hex-poly-z-mignotte"
%%%

When an integer polynomial is factored, the coefficients of each
factor are bounded a priori by the classical Mignotte bound: a
binomial coefficient times the Euclidean norm of the original
coefficient vector. `HexPolyZ` packages the executable pieces of that
bound. Because the exact Euclidean norm is irrational in general, the
norm is replaced by a conservative integer ceiling-square-root
overestimate, so every bound here is an upper bound on the true
quantity.

The pieces are an executable binomial coefficient and an integer
ceiling square root.

{docstring Hex.Nat.binom}

{docstring Hex.ZPoly.ceilSqrt}

{docstring Hex.ZPoly.le_ceilSqrt_sq}

From these the coefficient-norm bound and the per-coefficient Mignotte
bound are assembled, and a single uniform bound is taken over all
candidate factor degrees.

{docstring Hex.ZPoly.coeffNormSq}

{docstring Hex.ZPoly.coeffL2NormBound}

{docstring Hex.ZPoly.mignotteCoeffBound}

{docstring Hex.ZPoly.defaultFactorCoeffBound}

## Worked example: computing the bound
%%%
tag := "hex-poly-z-worked-mignotte"
%%%

The block below works over `g = 1 + x + x² + x³ + x⁴`, computes its
coefficient-norm bound, some binomial coefficients, a single Mignotte
bound, and the uniform default bound.

```lean
open Hex Hex.DensePoly

namespace HexPolyZChapterMignotte

-- g = 1 + x + x² + x³ + x⁴
private def g : ZPoly := #p[1, 1, 1, 1, 1]

-- Squared L2 norm of the coefficient vector is 5, and
-- its conservative integer bound is ceilSqrt 5 = 3.
#guard ZPoly.coeffNormSq g = 5
#guard ZPoly.coeffL2NormBound g = 3

-- Executable binomial coefficients.
#guard Nat.binom 4 2 = 6
#guard Nat.binom 5 2 = 10

-- Mignotte bound for the j=1 coefficient of a degree-2
-- factor: binom 2 1 * coeffL2NormBound g = 2 * 3.
#guard ZPoly.mignotteCoeffBound g 2 1 = 6

-- The uniform bound maximizes over all factor degrees
-- and coefficient indices up to deg g.
#guard ZPoly.defaultFactorCoeffBound g = 18

end HexPolyZChapterMignotte
```

# Key correctness theorems
%%%
tag := "hex-poly-z-key-correctness"
%%%

Two facts pin down the bound for downstream callers. First, the
conservative norm bound's square is at most twice the exact squared norm:
a bounded overestimate of the Euclidean norm.

{docstring Hex.ZPoly.coeffL2NormBound_sq_le_two_mul_coeffNormSq}

Second, every individual Mignotte bound within the ambient degree
range, and the norm bound itself, is dominated by the single uniform
{name}`Hex.ZPoly.defaultFactorCoeffBound`, so a caller can use one bound for all
factors.

{docstring Hex.ZPoly.mignotteCoeffBound_le_defaultFactorCoeffBound}

{docstring Hex.ZPoly.coeffL2NormBound_le_defaultFactorCoeffBound}

Finally, the uniform bound is strictly positive on any nonzero
polynomial, which the factorization driver needs to set a valid
precision modulus.

{docstring Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero}

# The Mathlib correspondence
%%%
tag := "hex-poly-z-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexPolyZMathlib` is
the proof-facing companion: it identifies {name}`Hex.ZPoly` with
Mathlib's `Polynomial ℤ`, transports the integer-polynomial operations
used by factorization, and proves the analytic bounds that justify the
executable estimates.

## Conversion and ring operations
%%%
tag := "hex-poly-z-mathlib-conversion"
%%%

The two conversion functions preserve coefficients and are mutually
inverse.

{docstring HexPolyZMathlib.toPolynomial}

{docstring HexPolyZMathlib.ofPolynomial}

{docstring HexPolyZMathlib.coeff_toPolynomial}

{docstring HexPolyZMathlib.toPolynomial_ofPolynomial}

{docstring HexPolyZMathlib.ofPolynomial_toPolynomial}

They are bundled as a ring equivalence, so zero, one, constants,
addition, multiplication, negation, and subtraction transport without
changing their meaning.

{docstring HexPolyZMathlib.equiv}

{docstring HexPolyZMathlib.toPolynomial_C}

{docstring HexPolyZMathlib.toPolynomial_add}

{docstring HexPolyZMathlib.toPolynomial_mul}

{docstring HexPolyZMathlib.toPolynomial_neg}

{docstring HexPolyZMathlib.toPolynomial_sub}

The following live example illustrates the usual proof pattern: cross
to `Polynomial ℤ`, use the simplification rules supplied by the bridge,
and cross back only if executable data is needed again.

```lean
open HexPolyZMathlib

namespace HexPolyZChapterCorrespondence

example (f g : Hex.ZPoly) :
    ofPolynomial (toPolynomial (f * g)) = f * g := by
  simp

example (f : Hex.ZPoly) (n : Nat) :
    (toPolynomial f).coeff n = f.coeff n := by
  simp

end HexPolyZChapterCorrespondence
```

## Integer-specific transports
%%%
tag := "hex-poly-z-mathlib-transports"
%%%

The bridge also names the transports that do not follow from the ring
equivalence alone. The Mathlib-free unit predicate agrees with
`IsUnit`; variable dilation becomes composition by `C c * X`; and the
executable content and primitive-part decomposition becomes Mathlib's
Gauss decomposition.

{docstring HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit}

{docstring HexPolyZMathlib.toPolynomial_dilate}

{docstring HexPolyZMathlib.toPolynomial_content}

{docstring HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart}

{docstring HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive}

Reduction modulo `p` crosses both representation boundaries: integer
coefficients are reduced into executable `ZMod64 p` values, then
identified with Mathlib's `ZMod p`. The coefficient theorem is the
rewrite rule used to prove the extensional map theorem and to transport
divisibility.

{docstring HexPolyZMathlib.coeff_toZMod_modP_eq_coeff_map_intCast}

{docstring HexPolyZMathlib.eq_map_intCast_of_coeff_eq_toZMod_modP}

{docstring HexPolyZMathlib.dvd_modP_of_dvd}

## Correctness theorems and the proof boundary
%%%
tag := "hex-poly-z-mathlib-correctness"
%%%

The executable library computes a natural-number squared coefficient
norm and a conservative integer bound. The companion identifies that
norm with the square of the real `l2norm`, identifies the executable
binomial coefficient with `Nat.choose`, and then applies Mathlib's
Mahler-measure theory to prove Mignotte's coefficient bound for every
factor of a nonzero integer polynomial.

{docstring HexPolyZMathlib.l2norm}

{docstring HexPolyZMathlib.l2norm_toPolynomial_sq_eq_coeffNormSq}

{docstring HexPolyZMathlib.binom_eq_choose}

{docstring HexPolyZMathlib.mignotte_bound}

The same boundary covers rational squarefreeness and the shared
root-separation foundations. The executable gcd test is related to
`Squarefree` after casting to `Polynomial ℚ`; discriminant,
Hadamard, Robinson-form, and Mahler-separation theorems remain entirely
on the Mathlib side for downstream certified factorization and root
isolation proofs.

{docstring HexPolyZMathlib.squareFreeRat_iff}

{docstring HexPolyZMathlib.one_le_mahlerDist}

Thus callers use {name}`Hex.ZPoly` and its natural-number bounds when
they need computation. They import `HexPolyZMathlib` only when a proof
must interpret those results as Mathlib polynomials or invoke
noncomputable algebraic and analytic theory. No Mathlib dependency
flows back into `HexPolyZ`.

# Cross-references
%%%
tag := "hex-poly-z-cross-references"
%%%

`HexPolyZ` builds on the base polynomial representation and feeds the
integer-factorization libraries:

* {ref "hex-poly"}[HexPoly] is the generic dense-polynomial library
  this one specializes. The constructors, arithmetic, and Euclidean
  operations used throughout this chapter (the `#p[...]` literal,
  {name}`Hex.DensePoly.scale`, and the rational division underlying
  {name}`Hex.ZPoly.primitiveSquareFreeDecomposition`) are documented
  there. `HexPolyZ` only fixes the coefficient type to `Int` and adds
  the content, congruence, and Mignotte operations.
* `HexPolyZMathlib` is the correspondence library: it identifies
  {name}`Hex.ZPoly` with Mathlib's `Polynomial ℤ` and proves the
  Mignotte bound as a theorem about the Mahler measure of the
  corresponding `Polynomial ℤ`. The executable quantities in this
  chapter compute the bound that theorem proves valid. The Mathlib
  dependency lives entirely there, never inside `HexPolyZ` itself.
* `HexHensel` consumes the congruence predicate and
  {name}`Hex.ZPoly.defaultFactorCoeffBound` to drive the Hensel-lifting and
  coefficient-recovery steps of integer polynomial factorization.
