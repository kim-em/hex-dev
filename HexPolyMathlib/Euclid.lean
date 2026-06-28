/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexPolyMathlib.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
Euclidean-algorithm correspondence for `HexPolyMathlib`.

This module transfers the executable `Hex.DensePoly` gcd and extended-gcd
surface across the `HexPolyMathlib.equiv` ring equivalence to Mathlib's
`Polynomial` Euclidean-domain API.
-/

namespace HexPolyMathlib

universe u

variable {R : Type u}

noncomputable section

private theorem toPolynomial_dvd_of_dense_dvd [CommSemiring R] [DecidableEq R]
    {p q : Hex.DensePoly R} :
    p ∣ q → toPolynomial p ∣ toPolynomial q := by
  intro hpq
  rcases hpq with ⟨r, rfl⟩
  exact ⟨toPolynomial r, by simp⟩

private theorem dense_dvd_of_toPolynomial_dvd [CommRing R] [DecidableEq R]
    {p : Hex.DensePoly R} {q : Polynomial R} :
    q ∣ toPolynomial p → ofPolynomial q ∣ p := by
  intro hqp
  rcases hqp with ⟨r, hr⟩
  refine ⟨ofPolynomial r, ?_⟩
  calc
    p = ofPolynomial (toPolynomial p) := (ofPolynomial_toPolynomial p).symm
    _ = ofPolynomial (q * r) := by rw [hr]
    _ = ofPolynomial q * ofPolynomial r := by simp

private theorem toPolynomial_dvd_of_dense_ofPolynomial_dvd [CommRing R] [DecidableEq R]
    {p : Hex.DensePoly R} {q : Polynomial R} :
    ofPolynomial q ∣ p → q ∣ toPolynomial p := by
  intro hqp
  rcases hqp with ⟨r, hr⟩
  refine ⟨toPolynomial r, ?_⟩
  calc
    toPolynomial p = toPolynomial (ofPolynomial q * r) := by rw [hr]
    _ = q * toPolynomial r := by simp

/--
The raw executable dense-polynomial gcd is associated to Mathlib's normalized
polynomial gcd under `toPolynomial`. It is not generally equal before normalization:
`Hex.DensePoly.gcd` returns the last Euclidean remainder, while
`EuclideanDomain.gcd` for polynomials over a field is normalized.
-/
theorem toPolynomial_gcd_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated (toPolynomial (Hex.DensePoly.gcd p q))
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  apply associated_of_dvd_dvd
  · apply EuclideanDomain.dvd_gcd
    · exact toPolynomial_dvd_of_dense_dvd (Hex.DensePoly.gcd_dvd_left p q)
    · exact toPolynomial_dvd_of_dense_dvd (Hex.DensePoly.gcd_dvd_right p q)
  · apply toPolynomial_dvd_of_dense_ofPolynomial_dvd
    apply Hex.DensePoly.dvd_gcd
    · exact dense_dvd_of_toPolynomial_dvd (EuclideanDomain.gcd_dvd_left (toPolynomial p) (toPolynomial q))
    · exact dense_dvd_of_toPolynomial_dvd (EuclideanDomain.gcd_dvd_right (toPolynomial p) (toPolynomial q))

/--
The raw gcd component of `Hex.DensePoly.xgcd` is associated to Mathlib's
normalized polynomial gcd. This is the xgcd-facing form of
`toPolynomial_gcd_associated`, not a literal equality of raw outputs.
-/
theorem toPolynomial_xgcd_gcd_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated (toPolynomial (Hex.DensePoly.xgcd p q).gcd)
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  simpa [Hex.DensePoly.xgcd_gcd_eq_gcd] using toPolynomial_gcd_associated (R := R) p q

/--
The executable Bezout identity transports across `toPolynomial`.
The right hand side is the executable raw gcd component, not Mathlib's
normalized polynomial gcd. The `@[simp]` direction collapses the transported
Bezout combination to the named raw gcd; the matching pattern only fires when
the goal mentions `Hex.DensePoly.xgcd p q` literally with both coefficient
projections, so the rule is narrow.
-/
@[simp, grind =]
theorem toPolynomial_xgcd_bezout_raw [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).left * toPolynomial p +
      toPolynomial (Hex.DensePoly.xgcd p q).right * toPolynomial q =
        toPolynomial (Hex.DensePoly.xgcd p q).gcd := by
  let r := Hex.DensePoly.xgcd p q
  have h : r.left * p + r.right * q = r.gcd := by
    simpa [r] using Hex.DensePoly.xgcd_bezout p q
  have ht := congrArg (fun x => toPolynomial x) h
  simpa [r] using ht

/--
The transported executable Bezout combination is associated to Mathlib's
normalized polynomial gcd. This is the normalization-aware xgcd correspondence
surface: executable coefficients certify the raw gcd, whose transport is
associated to Mathlib's canonical gcd.
-/
theorem toPolynomial_xgcd_bezout_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated
      (toPolynomial (Hex.DensePoly.xgcd p q).left * toPolynomial p +
        toPolynomial (Hex.DensePoly.xgcd p q).right * toPolynomial q)
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  rw [toPolynomial_xgcd_bezout_raw (R := R) p q]
  exact toPolynomial_xgcd_gcd_associated (R := R) p q

/--
The ring equivalence sends the executable raw gcd to a polynomial associated to
Mathlib's normalized gcd. Use this theorem when the caller only needs the
gcd universal property; do not assume raw executable gcd outputs are normalized.
-/
theorem equiv_gcd_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated (equiv (Hex.DensePoly.gcd p q)) (EuclideanDomain.gcd (equiv p) (equiv q)) := by
  simpa using toPolynomial_gcd_associated (R := R) p q

/-- The ring equivalence transports the executable raw Bezout identity. -/
theorem equiv_xgcd_bezout_raw [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    equiv (Hex.DensePoly.xgcd p q).left * equiv p +
      equiv (Hex.DensePoly.xgcd p q).right * equiv q =
        equiv (Hex.DensePoly.xgcd p q).gcd := by
  simp

/--
The ring-equivalence form of the normalization-aware xgcd correspondence:
the executable Bezout combination is associated to Mathlib's normalized gcd.
-/
theorem equiv_xgcd_bezout_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated
      (equiv (Hex.DensePoly.xgcd p q).left * equiv p +
        equiv (Hex.DensePoly.xgcd p q).right * equiv q)
      (EuclideanDomain.gcd (equiv p) (equiv q)) := by
  simpa using toPolynomial_xgcd_bezout_associated (R := R) p q

end

end HexPolyMathlib
