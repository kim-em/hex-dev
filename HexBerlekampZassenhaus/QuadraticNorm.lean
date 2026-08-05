/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPolyZ.IntegerPolynomial

public section

/-!
# Iterated quadratic norms and their irreducibility certificates

For `d : ℤ` and `g ∈ ℤ[X]`, the *quadratic norm* `N_d(g)` is the norm of
`g(X - t)` along `ℤ[t]/(t² - d) → ℤ`, that is `N_d(g)(X) = g(X - t) · g(X + t)`
with `t² = d`. It is again an integer polynomial, of twice the degree when `g` is
monic, and its roots are `β ± √d` as `β` runs over the roots of `g`. Iterating
from `X - c` gives `F(c; d₁, …, dₙ)`, the product of `X - c - ∑ᵢ εᵢ √dᵢ` over all
`2ⁿ` sign patterns `ε ∈ {±1}ⁿ`.

A `QuadraticNormCertificate` is the translation `c` together with the
radicands `d₁, …, dₙ`, and `QuadraticNormCertificate.check` verifies
two things: *independence*, that no nonempty subproduct of the radicands is a
perfect square, which is exactly multiplicative independence of the `dᵢ` in
`ℚ*/(ℚ*)²`; and *identification*, that `F(c; d)` equals the input polynomial
coefficientwise up to the unit `-1`.

Together those imply the input is irreducible: independence forces
`[ℚ(√d₁, …, √dₙ) : ℚ] = 2ⁿ`, the element `c + ∑ᵢ √dᵢ` generates that field, and
`F(c; d)` is its minimal polynomial. The paper proof of that implication is in
`reports/hexbz-quadratic-norm-certificate.md`. Its two halves are separate
developments: `HexBerlekampZassenhausMathlib.QuadraticNorm` identifies what these
definitions compute with `F(c; d)` as a `Polynomial`, and the multiquadratic
tower theorem, which is not yet in Lean, supplies the field theory.

The independence check needs no factorization of the radicands: an integer is a
rational square exactly when it is a perfect square, so `2ⁿ - 1` integer square
tests settle it. That, with the polynomial identity, is the whole arithmetic
trust surface of the check.
-/

namespace Hex

/-! ## The quadratic norm -/

/-- One synthetic-shift step in `(ℤ[t]/(t² - d))[X]`: from the pair of
`h = p + q · t` and the next coefficient `a`, the pair of `a + (X - t) · h`.

Since `t² = d`, `(X - t) · (p + q t) = (X p - d q) + (X q - p) t`, so the step
reads both components of `h` and writes both components of the result. -/
@[expose]
def quadStep (d a : Int) (h : ZPoly × ZPoly) : ZPoly × ZPoly :=
  (DensePoly.shift 1 h.1 - DensePoly.scale d h.2 + DensePoly.C a,
    DensePoly.shift 1 h.2 - h.1)

/-- The coefficient pair of `g(X - t)` in `(ℤ[t]/(t² - d))[X]`, read off the
ascending coefficient list of `g`: {name}`Hex.quadShift` returns `(p, q)` with
`g(X - t) = p + q · t`.

This is the synthetic Taylor shift with shift constant `-t`, carrying the
coefficient pair through Horner's rule from the top coefficient down. -/
@[expose]
def quadShift (d : Int) (coeffs : List Int) : ZPoly × ZPoly :=
  coeffs.foldr (quadStep d) (0, 0)

/-- `N_d(g) = g(X - t) · g(X + t)` with `t² = d`, an integer polynomial.

Writing `g(X - t) = p + q t`, the conjugate is `p - q t` and the product is
`p² - d q²`: the `t` component cancels by antisymmetry, so only the rational part
is ever materialized. -/
@[expose]
def quadNorm (d : Int) (g : ZPoly) : ZPoly :=
  let h := quadShift d g.toArray.toList
  h.1 * h.1 - DensePoly.scale d (h.2 * h.2)

/-- The empty coefficient list is the zero polynomial. -/
theorem quadShift_nil (d : Int) : quadShift d [] = (0, 0) := rfl

/-- Reading one more coefficient off the front is one {name}`Hex.quadStep`. -/
theorem quadShift_cons (d a : Int) (as : List Int) :
    quadShift d (a :: as) = quadStep d a (quadShift d as) := rfl

/-- The norm in terms of the shifted pair, with the `t` component already
cancelled. -/
theorem quadNorm_eq (d : Int) (g : ZPoly) :
    quadNorm d g
      = (quadShift d g.toArray.toList).1 * (quadShift d g.toArray.toList).1
        - DensePoly.scale d
            ((quadShift d g.toArray.toList).2 * (quadShift d g.toArray.toList).2) := rfl

/-- `F(c; ds) = N_{dₖ}(⋯ N_{d₁}(X - c) ⋯)`, the iterated quadratic norm of the
translation `c` along the radicands `ds`. -/
@[expose]
def iteratedNorm (c : Int) (ds : Array Int) : ZPoly :=
  ds.foldl (fun g d => quadNorm d g) (DensePoly.ofCoeffs #[-c, 1])

/-! ## The independence test -/

/-- Is `m` the square of an integer? -/
@[expose]
def isPerfectSquare (m : Int) : Bool :=
  match m with
  | .ofNat n => let r := n.sqrt; r * r == n
  | .negSucc _ => false

/-- The `2ⁿ - 1` products of the nonempty sublists of `ds`.

The head contributes its own singleton and doubles every product from the tail,
once with and once without it. -/
@[expose]
def squareClassProducts : List Int → List Int
  | [] => []
  | d :: ds => d :: (squareClassProducts ds).flatMap (fun m => [m, d * m])

/-- Are the radicands multiplicatively independent in `ℚ*/(ℚ*)²`?

Equivalently: is no nonempty subproduct a perfect square? A zero radicand and a
repeated radicand are both rejected by this, as they must be. -/
@[expose]
def independentSquareClasses (ds : Array Int) : Bool :=
  (squareClassProducts ds.toList).all (fun m => !isPerfectSquare m)

/-! ## The certificate -/

/-- Translation and radicands for one iterated quadratic norm. -/
structure QuadraticNormCertificate where
  /-- The translation: the certified polynomial is `∏_ε (X - c - ∑ εᵢ √dᵢ)`. -/
  translation : Int
  /-- The radicands, in the order the norms are taken. -/
  radicands : Array Int
deriving Repr, Inhabited

/-- Does the certificate prove `f` irreducible?

A `true` result asserts both halves: the radicands are independent, and `f` is,
up to the unit `-1`, exactly the iterated quadratic norm they describe.

Every `F(c; d)` is monic and `-1` is a unit of `ℤ[X]`, so `f` and `-f` are
irreducible together; that sign is the whole normalization the identification
needs. There is no scaling and no content division, since a primitive integer
polynomial with leading coefficient outside `{1, -1}` is never `± F(c; d)`. -/
@[expose]
def QuadraticNormCertificate.check (cert : QuadraticNormCertificate) (f : ZPoly) : Bool :=
  independentSquareClasses cert.radicands &&
    iteratedNorm cert.translation cert.radicands == ZPoly.normalizePrimitiveSign f

end Hex
