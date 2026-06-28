/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import VersoManual

import HexPolyMathlib

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "HexPolyMathlib: DensePoly ↔ Polynomial correspondence" =>
%%%
tag := "hex-poly-mathlib"
%%%

# Introduction
%%%
tag := "hex-poly-mathlib-intro"
%%%

`HexPolyMathlib` is the Mathlib correspondence layer for the executable
dense-polynomial representation {name}`Hex.DensePoly`. The executable
library `HexPoly` stores a polynomial as a normalized coefficient array
and computes the ring operations directly on that array; this bridge
transfers those polynomials to Mathlib's canonical {name}`Polynomial`
and proves that every operation is carried across faithfully.

What a Mathlib-side caller gets is the ability to treat an executable
{name}`Hex.DensePoly` value as an honest element of {name}`Polynomial`:
the two are connected by a bundled ring equivalence, so any algebraic
identity proved on one side transfers to the other. A computation run in
the fast coefficient-array representation can therefore be given meaning
as a statement about `Polynomial R`, and a `Polynomial R` identity from
Mathlib can be pulled back to constrain the executable result.

The whole surface lives in namespace `HexPolyMathlib` and is
`noncomputable`: it exists only to justify the executable theory, not to
be evaluated. The conversions are documented here by signature,
docstring, and theorem statement rather than by worked `#eval` output;
the executable computations themselves belong to the
{ref "hex-poly"}[`HexPoly` chapter].

# Transfer maps
%%%
tag := "hex-poly-mathlib-transfer-maps"
%%%

The two primitive conversions are {name}`HexPolyMathlib.toPolynomial`,
which reads an executable dense polynomial as a Mathlib polynomial by
summing its stored coefficients as monomials, and
{name}`HexPolyMathlib.ofPolynomial`, which rebuilds an executable dense
polynomial from the coefficients of a Mathlib polynomial up to its
degree.

{docstring HexPolyMathlib.toPolynomial}

{docstring HexPolyMathlib.ofPolynomial}

The bridge's lowest-level facts read each conversion off coefficient by
coefficient: the `n`th coefficient of a converted polynomial is exactly
the `n`th coefficient of its source on either side, so a caller reasoning
about a single coefficient never needs to unfold the conversion.

{docstring HexPolyMathlib.coeff_toPolynomial}

{docstring HexPolyMathlib.coeff_ofPolynomial}

# Round-trip laws
%%%
tag := "hex-poly-mathlib-round-trip"
%%%

The two transfer maps are mutually inverse, which is what makes the
bundled {ref "hex-poly-mathlib-equiv"}[ring equivalence] below
well-defined. Each composite collapses to the identity on its respective
type.

{docstring HexPolyMathlib.toPolynomial_ofPolynomial}

{docstring HexPolyMathlib.ofPolynomial_toPolynomial}

# Ring-homomorphism transport
%%%
tag := "hex-poly-mathlib-ring-hom"
%%%

{name}`HexPolyMathlib.toPolynomial` is a ring homomorphism: it carries
the executable constants and operations to the matching `Polynomial R`
constants and operations. These are the lemmas a caller rewrites with to
push the conversion through an expression and so move an identity across
the bridge.

The constants and monomials transfer:

{docstring HexPolyMathlib.toPolynomial_zero}

{docstring HexPolyMathlib.toPolynomial_one}

{docstring HexPolyMathlib.toPolynomial_C}

{docstring HexPolyMathlib.toPolynomial_monomial}

Addition, negation, subtraction, and multiplication all commute with
{name}`HexPolyMathlib.toPolynomial`, and the derivative is intertwined
with Mathlib's:

{docstring HexPolyMathlib.toPolynomial_add}

{docstring HexPolyMathlib.toPolynomial_neg}

{docstring HexPolyMathlib.toPolynomial_sub}

{docstring HexPolyMathlib.toPolynomial_mul}

{docstring HexPolyMathlib.toPolynomial_derivative}

The inverse map {name}`HexPolyMathlib.ofPolynomial` carries the same
structure the other way, so identities can be pulled back from Mathlib to
the executable representation:

{docstring HexPolyMathlib.ofPolynomial_C}

{docstring HexPolyMathlib.ofPolynomial_add}

{docstring HexPolyMathlib.ofPolynomial_mul}

Because every transfer lemma above is a `@[simp]` rewrite, `simp` alone
discharges the routine homomorphism obligations. Since the surface is
`noncomputable`, the worked examples below type-check a transported
statement rather than evaluate it — pushing the conversion through a
product or round-tripping a value is immediate:

```lean
open HexPolyMathlib

variable {R : Type _} [CommRing R] [DecidableEq R]
variable (p q : Hex.DensePoly R)

example :
    toPolynomial (p * q)
      = toPolynomial p * toPolynomial q := by
  simp

-- Round trip through `ofPolynomial` is the identity.
example :
    ofPolynomial (toPolynomial p) = p := by
  simp
```

# Degree and leading coefficient
%%%
tag := "hex-poly-mathlib-degree"
%%%

The conversion also matches the executable degree and leading-coefficient
notions against Mathlib's, so a caller can read off `natDegree` and
`leadingCoeff` of the transported polynomial without recomputing them.

{docstring HexPolyMathlib.natDegree_toPolynomial}

{docstring HexPolyMathlib.leadingCoeff_toPolynomial}

# Divisibility transport
%%%
tag := "hex-poly-mathlib-divisibility"
%%%

Divisibility transfers in both directions, and because the maps are
mutually inverse it is also reflected: executable polynomials divide one
another exactly when their Mathlib images do. This is the form a
factorization argument uses to move a divisibility obligation onto
whichever side has the lemma it needs.

{docstring HexPolyMathlib.toPolynomial_dvd}

{docstring HexPolyMathlib.ofPolynomial_dvd}

{docstring HexPolyMathlib.toPolynomial_dvd_iff}

# The ring equivalence
%%%
tag := "hex-poly-mathlib-equiv"
%%%

The capstone packages the transfer maps and the homomorphism laws into a
single bundled ring equivalence {name}`HexPolyMathlib.equiv` of type
`Hex.DensePoly R ≃+* Polynomial R`. Its forward map is
{name}`HexPolyMathlib.toPolynomial` and its inverse is
{name}`HexPolyMathlib.ofPolynomial`; the mutual-inverse and
additive/multiplicative homomorphism fields are exactly the lemmas above.

{docstring HexPolyMathlib.equiv}

Two unfolding lemmas connect the bundled equivalence back to the bare
conversions, so the transport `@[simp]` lemmas continue to fire on
`equiv` and `equiv.symm` applications:

{docstring HexPolyMathlib.equiv_apply}

{docstring HexPolyMathlib.equiv_symm_apply}

With {name}`HexPolyMathlib.equiv` in hand a downstream Mathlib-side caller
transports the full `CommRing` theory of {name}`Polynomial` onto the
executable type for free, and reads results back through the same
equivalence.

# Euclidean-algorithm transport
%%%
tag := "hex-poly-mathlib-euclid"
%%%

`HexPolyMathlib/Euclid.lean` carries the executable gcd and extended-gcd
surface across the equivalence to Mathlib's Euclidean-domain API for
polynomials over a field. The correspondence is stated up to
`Associated` rather than equality: {name}`Hex.DensePoly.gcd` returns the
last Euclidean remainder, whereas Mathlib's `EuclideanDomain.gcd` is
normalized, so the two agree only up to a unit.

{docstring HexPolyMathlib.toPolynomial_gcd_associated}

{docstring HexPolyMathlib.toPolynomial_xgcd_gcd_associated}

The extended gcd transports the Bezout identity. The raw form is an exact
equality against the executable raw gcd component; the associated form
relates that combination to Mathlib's normalized gcd.

{docstring HexPolyMathlib.toPolynomial_xgcd_bezout_raw}

{docstring HexPolyMathlib.toPolynomial_xgcd_bezout_associated}

The same three facts are restated through the bundled equivalence, so a
caller working with `equiv` rather than the bare {name}`HexPolyMathlib.toPolynomial` has the gcd universal property and the Bezout identity directly to hand:

{docstring HexPolyMathlib.equiv_gcd_associated}

{docstring HexPolyMathlib.equiv_xgcd_bezout_raw}

{docstring HexPolyMathlib.equiv_xgcd_bezout_associated}

# Cross-references
%%%
tag := "hex-poly-mathlib-cross-references"
%%%

`HexPolyMathlib` is the Mathlib bridge for one executable library:

* `HexPoly` is the computational counterpart; see
  {ref "hex-poly"}[the `HexPoly` chapter]. It defines the dense
  representation {name}`Hex.DensePoly` — a normalized coefficient array —
  and supplies the ring operations, the degree and leading-coefficient
  readers, and the gcd/xgcd Euclidean surface that this chapter
  transfers. The executable side carries the runtime evaluation paths and
  the normalization invariant; the bridge re-expresses those same
  operations as theorems about `Polynomial R`. The transfer lemmas here
  are the proof-side justification that the fast executable polynomial
  arithmetic computes the mathematically intended results.
