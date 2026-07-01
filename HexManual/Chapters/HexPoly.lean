/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexPoly.Euclid
import HexPolyMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPoly: normalized dense polynomials" =>
%%%
tag := "hex-poly"
%%%

# Introduction
%%%
tag := "hex-poly-intro"
%%%

`HexPoly` stores an executable dense polynomial as an `Array` of
coefficients in ascending degree order: index `i` holds the
coefficient of `xⁱ`. The array carries a single structural invariant:
no trailing zeros. This *normalized* representation makes structural
equality coincide with semantic equality, so two `HexPoly` polynomials
are equal as Lean values exactly when they are equal as polynomials.

{name}`Hex.DensePoly` is generic over any coefficient type `R` with a
`Zero` and a `DecidableEq`. The arithmetic, evaluation, and Euclidean
operations require the further structure (`Add`, `Mul`, `Sub`, `Div`)
that each one needs. `HexPoly` is Mathlib-free and depends on no other `hex` library.
The integer library `HexPolyZ`, the prime-field library `HexPolyFp`,
and through them the factorization and finite-field libraries all
consume this representation. See
{ref "hex-poly-cross-references"}[Cross-references].

# Dense polynomial type
%%%
tag := "hex-poly-core-types"
%%%

The normalization invariant is a predicate on coefficient arrays, and
the polynomial type is the array bundled with a proof of that
predicate.

{docstring Hex.DensePolyNormalized}

{docstring Hex.DensePoly}

Because the invariant pins down a unique array for each polynomial
value, `HexPoly` derives a `DecidableEq` on {name}`Hex.DensePoly` and
proves the extensionality principle: two normalized
polynomials are equal as soon as their coefficient functions agree.

{docstring Hex.DensePoly.ext_coeff}

# Constructors and normalization
%%%
tag := "hex-poly-constructors"
%%%

Every constructor routes through normalization so the no-trailing-zeros
invariant holds by construction. Callers never trim by hand. The
primitive normalizer drops trailing zeros from a raw array, and
{name}`Hex.DensePoly.ofCoeffs` wraps it to build a polynomial.

{docstring Hex.DensePoly.trimTrailingZeros}

{docstring Hex.DensePoly.ofCoeffs}

{docstring Hex.DensePoly.ofList}

The remaining constructors build the common shapes directly. The zero
polynomial is the empty array; a constant collapses to zero when its
scalar is zero; a monomial collapses likewise.

{docstring Hex.DensePoly.zero}

{docstring Hex.DensePoly.C}

{docstring Hex.DensePoly.monomial}

# Structural queries
%%%
tag := "hex-poly-queries"
%%%

These queries read back the data a caller needs without exposing the
array invariant. {name}`Hex.DensePoly.size` is the stored coefficient
count: one more than the degree for a nonzero polynomial, and `0` for
the zero polynomial. {name}`Hex.DensePoly.degree?` turns that into an
optional degree.

{docstring Hex.DensePoly.size}

{docstring Hex.DensePoly.isZero}

{docstring Hex.DensePoly.coeff}

{docstring Hex.DensePoly.degree?}

{docstring Hex.DensePoly.support}

{docstring Hex.DensePoly.toArray}

The coefficient function is characterised against each constructor, so
proofs and `simp` can read coefficients off `ofCoeffs`, `C`, and
`monomial` without unfolding normalization:

{docstring Hex.DensePoly.coeff_ofCoeffs}

{docstring Hex.DensePoly.coeff_C}

{docstring Hex.DensePoly.coeff_monomial}

# Principal operations
%%%
tag := "hex-poly-operations"
%%%

Arithmetic is coefficientwise where it can be (addition, subtraction,
negation, scalar and monomial scaling) and a schoolbook convolution for
multiplication. Each operation re-normalizes its result, so the output
is again a canonical representative. The standard `Add`, `Sub`, `Neg`,
and `Mul` instances on {name}`Hex.DensePoly` dispatch to these, so
`p + q`, `p - q`, `-p`, and `p * q` notation works directly.

{docstring Hex.DensePoly.add}

{docstring Hex.DensePoly.sub}

{docstring Hex.DensePoly.neg}

{docstring Hex.DensePoly.scale}

{docstring Hex.DensePoly.shift}

{docstring Hex.DensePoly.mul}

Evaluation, composition, and the formal derivative complete the
operations. Evaluation and composition both use Horner's method.

{docstring Hex.DensePoly.eval}

{docstring Hex.DensePoly.compose}

{docstring Hex.DensePoly.derivative}

Each operation comes with a characterising coefficient law. These are
the lemmas downstream proofs rewrite with. The zero-absorption side
conditions (`hzero`) are discharged automatically over any semiring,
via the `*_semiring`/`*_ring` specializations.

{docstring Hex.DensePoly.coeff_add}

{docstring Hex.DensePoly.coeff_mul}

{docstring Hex.DensePoly.coeff_sub}

{docstring Hex.DensePoly.coeff_derivative}

## Worked example: integer arithmetic
%%%
tag := "hex-poly-worked-arithmetic"
%%%

The block below works over `DensePoly Int`. It builds a quadratic and a
monomial, then computes their sum and product, an evaluation, and a
derivative.

```lean
open Hex Hex.DensePoly

namespace HexPolyChapterArith

-- a = 1 + 2x + 3x²
private def a : DensePoly Int := ofCoeffs #[1, 2, 3]
-- b = x
private def b : DensePoly Int := monomial 1 1

-- The constructors normalize: trailing zeros are
-- dropped, and a monomial stores its one nonzero
-- coefficient at its degree.
#guard a.toArray.toList = [1, 2, 3]
#guard b.toArray.toList = [0, 1]
#guard a.degree? = some 2
#guard a.support = [0, 1, 2]
#guard a.coeff 2 = 3

-- A padded array collapses to the trimmed value.
#guard ofCoeffs #[1, 2, 3, 0, 0] = a
-- The zero constant is the zero polynomial.
#guard C (0 : Int) = (0 : DensePoly Int)

-- (1 + 2x + 3x²) + x = 1 + 3x + 3x²
#guard (a + b).toArray.toList = [1, 3, 3]
-- (1 + 2x + 3x²) · x = x + 2x² + 3x³
#guard (a * b).toArray.toList = [0, 1, 2, 3]
-- Evaluation by Horner: a(2) = 1 + 4 + 12 = 17.
#guard eval a 2 = 17
-- d/dx (1 + 2x + 3x²) = 2 + 6x.
#guard (derivative a).toArray.toList = [2, 6]

end HexPolyChapterArith
```

# Euclidean operations
%%%
tag := "hex-poly-euclid"
%%%

Over a field the dense representation supports division with remainder,
quotient and remainder operators, and gcd. The entry points are the
leading coefficient and the monic predicate.

{docstring Hex.DensePoly.leadingCoeff}

{docstring Hex.DensePoly.Monic}

{docstring Hex.DensePoly.monic_iff_leadingCoeff_eq_one}

Division has two flavours. {name}`Hex.DensePoly.divModMonic` divides by
a monic divisor over any commutative ring. No division of coefficients
is needed because the leading coefficient is `1`.
{name}`Hex.DensePoly.divMod` is the field version: it scales by the
inverse of the divisor's leading coefficient and so requires a `Div` on
the coefficient type.

{docstring Hex.DensePoly.divModMonic}

{docstring Hex.DensePoly.divMod}

The `Div`, `Mod`, and `Dvd` instances expose the field quotient and
remainder as `p / q`, `p % q`, and `q ∣ p`, and the extended algorithm
returns the gcd with its Bezout coefficients.

{docstring Hex.DensePoly.div}

{docstring Hex.DensePoly.mod}

{docstring Hex.DensePoly.modByMonic}

{docstring Hex.DensePoly.gcd}

{docstring Hex.DensePoly.xgcd}

## Worked example: division over the rationals
%%%
tag := "hex-poly-worked-euclid"
%%%

This block works over `DensePoly Rat`. It divides `x² - 1` by `x - 1`,
reads off the quotient and remainder, checks the Euclidean
reconstruction, and computes a gcd.

```lean
open Hex Hex.DensePoly

namespace HexPolyChapterEuclid

-- p = x² - 1, q = x - 1
private def p : DensePoly Rat := ofCoeffs #[-1, 0, 1]
private def q : DensePoly Rat := ofCoeffs #[-1, 1]

-- x² - 1 = (x - 1)(x + 1), so the division is exact.
-- Quotient x + 1, remainder 0.
#guard (divMod p q).1.toArray.toList = [1, 1]
#guard (divMod p q).2 = (0 : DensePoly Rat)
#guard (p / q).toArray.toList = [1, 1]
#guard p % q = (0 : DensePoly Rat)

-- Euclidean reconstruction: (p / q) · q + (p % q) = p.
#guard (p / q) * q + (p % q) = p

-- q is monic, so it also divides p through the
-- ring-only path.
#guard q.leadingCoeff = 1
#guard modByMonic p q (by rfl) = (0 : DensePoly Rat)

-- gcd(x² - 1, x + 1) = x + 1: a monic gcd.
#guard gcd p (ofCoeffs #[1, 1]) = ofCoeffs #[1, 1]

end HexPolyChapterEuclid
```

# Key correctness theorems
%%%
tag := "hex-poly-key-correctness"
%%%

The Euclidean operators are pinned down by a small set of laws. The
quotient-remainder identity reconstructs the dividend, and the
remainder has strictly smaller degree than a positive-degree divisor.
Together these are the defining properties of Euclidean division. They
are stated under the `DivModLaws` hypothesis bundling the per-field
proof obligations, which `HexPolyFp` discharges for the concrete prime
fields.

{docstring Hex.DensePoly.divMod_spec}

{docstring Hex.DensePoly.div_mul_add_mod}

{docstring Hex.DensePoly.mod_degree_lt_of_pos_degree}

A polynomial of smaller degree is its own remainder, and a divisor
divides its dividend exactly when the remainder is zero.

{docstring Hex.DensePoly.mod_eq_self_of_degree_lt}

{docstring Hex.DensePoly.mod_eq_zero_of_dvd}

The gcd divides both arguments and is divisible by every common
divisor (its universal property), and the extended coefficients
satisfy the Bezout identity. These are bundled under the `GcdLaws`
hypothesis, again discharged downstream.

{docstring Hex.DensePoly.gcd_dvd_left}

{docstring Hex.DensePoly.gcd_dvd_right}

{docstring Hex.DensePoly.dvd_gcd}

{docstring Hex.DensePoly.xgcd_bezout}

# The Mathlib correspondence
%%%
tag := "hex-poly-mathlib"
%%%

Everything above is executable and Mathlib-free. `HexPolyMathlib`
connects it to Mathlib: every {name}`Hex.DensePoly` corresponds to a
Mathlib `Polynomial` with the same coefficients. The two transfer maps
go each way.

{docstring HexPolyMathlib.toPolynomial}

{docstring HexPolyMathlib.ofPolynomial}

They are mutually inverse:

{docstring HexPolyMathlib.toPolynomial_ofPolynomial}

{docstring HexPolyMathlib.ofPolynomial_toPolynomial}

`toPolynomial` is a degree-preserving ring homomorphism. Addition,
multiplication, and the degree transfer:

{docstring HexPolyMathlib.toPolynomial_add}

{docstring HexPolyMathlib.toPolynomial_mul}

{docstring HexPolyMathlib.natDegree_toPolynomial}

The maps and laws bundle into a ring equivalence, and divisibility
transfers through it:

{docstring HexPolyMathlib.equiv}

{docstring HexPolyMathlib.toPolynomial_dvd_iff}

# Cross-references
%%%
tag := "hex-poly-cross-references"
%%%

`HexPoly` depends on no other `hex` library. Downstream of it:

* `HexPolyZ` specializes the coefficient type to `Int` and adds the
  integer-specific theory (content, primitive parts), and `HexPolyFp`
  specializes to the prime fields `ZMod64 p`, supplying the concrete
  `DivModLaws` and `GcdLaws` instances that turn the
  {ref "hex-poly-key-correctness"}[Euclidean laws] above into usable
  facts. The finite-field and factorization libraries, including `HexGFqRing`
  and `HexBerlekamp`, reach this representation transitively through
  `HexPolyFp`.
