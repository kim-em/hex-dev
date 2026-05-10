import HexPolyMathlib.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
Euclidean-algorithm correspondence for `HexPolyMathlib`.

This module transfers the executable `Hex.DensePoly` gcd and extended-gcd
surface across the `HexPolyMathlib.equiv` bridge to Mathlib's
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
    _ = ofPolynomial q * ofPolynomial r := by
      simpa [equiv_symm_apply] using (equiv.symm.map_mul q r)

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
polynomial gcd under the bridge. It is not generally equal before normalization:
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

/-- The left Bezout coefficient from `Hex.DensePoly.xgcd` transports to Mathlib's `gcdA`. -/
theorem toPolynomial_xgcd_left [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).left =
      EuclideanDomain.gcdA (toPolynomial p) (toPolynomial q) := by
  sorry

/-- The right Bezout coefficient from `Hex.DensePoly.xgcd` transports to Mathlib's `gcdB`. -/
theorem toPolynomial_xgcd_right [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).right =
      EuclideanDomain.gcdB (toPolynomial p) (toPolynomial q) := by
  sorry

/--
The raw gcd component of `Hex.DensePoly.xgcd` is associated to Mathlib's
normalized polynomial gcd. This is the xgcd-facing form of
`toPolynomial_gcd_associated`, not a literal equality of raw outputs.
-/
theorem toPolynomial_xgcd_gcd_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated (toPolynomial (Hex.DensePoly.xgcd p q).gcd)
      (EuclideanDomain.gcd (toPolynomial p) (toPolynomial q)) := by
  simpa [Hex.DensePoly.gcd] using toPolynomial_gcd_associated (R := R) p q

/--
The executable Bezout identity transports to Mathlib's extended-gcd coefficients under the bridge.
-/
theorem toPolynomial_xgcd_bezout [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    toPolynomial (Hex.DensePoly.xgcd p q).left * toPolynomial p +
      toPolynomial (Hex.DensePoly.xgcd p q).right * toPolynomial q =
        EuclideanDomain.gcd (toPolynomial p) (toPolynomial q) := by
  sorry

/--
The ring equivalence sends the executable raw gcd to a polynomial associated to
Mathlib's normalized gcd. Use this theorem when the consumer only needs the
gcd universal property; do not assume raw executable gcd outputs are normalized.
-/
theorem equiv_gcd_associated [Field R] [DecidableEq R] [Hex.DensePoly.GcdLaws R]
    (p q : Hex.DensePoly R) :
    Associated (equiv (Hex.DensePoly.gcd p q)) (EuclideanDomain.gcd (equiv p) (equiv q)) := by
  simpa using toPolynomial_gcd_associated (R := R) p q

/-- The ring equivalence sends the executable left Bezout coefficient to Mathlib's `gcdA`. -/
theorem equiv_xgcd_left [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    equiv (Hex.DensePoly.xgcd p q).left = EuclideanDomain.gcdA (equiv p) (equiv q) := by
  simpa using toPolynomial_xgcd_left (R := R) p q

/-- The ring equivalence sends the executable right Bezout coefficient to Mathlib's `gcdB`. -/
theorem equiv_xgcd_right [Field R] [DecidableEq R] (p q : Hex.DensePoly R) :
    equiv (Hex.DensePoly.xgcd p q).right = EuclideanDomain.gcdB (equiv p) (equiv q) := by
  simpa using toPolynomial_xgcd_right (R := R) p q

end

end HexPolyMathlib
