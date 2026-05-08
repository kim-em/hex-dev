import HexBerlekampZassenhaus
import HexPolyZMathlib.Basic
import HexPolyZMathlib.Mignotte
import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-!
Mathlib-facing correctness surface for `HexBerlekampZassenhaus`.

This module states the unconditional integer factorization and irreducibility
certificate theorems after transporting executable `Hex.ZPoly` values to
Mathlib polynomials over `ℤ`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

private def isUnitFactor (g : Hex.ZPoly) : Bool :=
  match g.degree? with
  | some 0 => g.coeff 0 == 1 || g.coeff 0 == -1
  | _ => false

private def nonUnitFactorCount (φ : Hex.Factorization) : Nat :=
  (φ.factors.toList.filter fun entry => !isUnitFactor entry.1).length

/--
The transported degree of an executable divisor is bounded by the executable
degree of the ambient nonzero polynomial.
-/
theorem natDegree_toPolynomial_le_degree_getD_of_dvd
    (f g : Hex.ZPoly) (hf : f ≠ 0) (hgf : g ∣ f) :
    (HexPolyZMathlib.toPolynomial g).natDegree ≤ f.degree?.getD 0 := by
  sorry

/--
The executable natural L2 bound dominates the real coefficient-vector norm used
by the Mathlib Mignotte theorem.
-/
theorem l2norm_toPolynomial_le_coeffL2NormBound (f : Hex.ZPoly) :
    HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f) ≤
      (Hex.ZPoly.coeffL2NormBound f : ℝ) := by
  sorry

/--
The default executable factorization bound is strong enough for every
coefficient of every executable divisor of a nonzero input.
-/
theorem defaultFactorCoeffBound_valid
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∀ g : Hex.ZPoly, g ∣ f → ∀ i, (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound f := by
  intro g hgf i
  have hf_poly : HexPolyZMathlib.toPolynomial f ≠ 0 := by
    sorry
  have hgf_poly : HexPolyZMathlib.toPolynomial g ∣ HexPolyZMathlib.toPolynomial f := by
    sorry
  have hmignotte :=
    HexPolyZMathlib.mignotte_bound
      (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial g)
      hf_poly hgf_poly i
  have hdegree :
      (HexPolyZMathlib.toPolynomial g).natDegree ≤ f.degree?.getD 0 :=
    natDegree_toPolynomial_le_degree_getD_of_dvd f g hf hgf
  have hl2 :
      HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f) ≤
        (Hex.ZPoly.coeffL2NormBound f : ℝ) :=
    l2norm_toPolynomial_le_coeffL2NormBound f
  have huniform :
      Hex.ZPoly.mignotteCoeffBound f (HexPolyZMathlib.toPolynomial g).natDegree i ≤
        Hex.ZPoly.defaultFactorCoeffBound f :=
    Hex.ZPoly.mignotteCoeffBound_le_defaultFactorCoeffBound f hdegree
      (by sorry)
  sorry

/--
Executable irreducibility predicate for transported integer polynomials.

Constant polynomials are decided by integer primality. Nonconstant
polynomials must have unit content and exactly one nonunit factor in the
default executable Berlekamp-Zassenhaus factorization.
-/
def irreducibleByFactorization (f : Polynomial ℤ) : Bool :=
  let fz := HexPolyZMathlib.ofPolynomial f
  match fz.degree? with
  | none => false
  | some 0 => decide (Nat.Prime (fz.coeff 0).natAbs)
  | some (_ + 1) =>
      decide ((Hex.ZPoly.content fz).natAbs = 1) &&
        nonUnitFactorCount (Hex.factor fz) == 1

/--
The executable factorization predicate agrees with Mathlib irreducibility over
`Polynomial ℤ`.
-/
theorem irreducibleByFactorization_iff (f : Polynomial ℤ) :
    irreducibleByFactorization f = true ↔ Irreducible f := by
  sorry

/--
Mathlib irreducibility over `Polynomial ℤ` is decidable through the executable
Berlekamp-Zassenhaus factorization surface.
-/
instance irreducibleDecidablePred :
    DecidablePred (fun f : Polynomial ℤ => Irreducible f) :=
  fun f =>
    if h : irreducibleByFactorization f = true then
      isTrue ((irreducibleByFactorization_iff f).mp h)
    else
      isFalse (fun hf => h ((irreducibleByFactorization_iff f).mpr hf))

/-- The default executable factorization multiplies back to the input. -/
theorem factor_product (f : Hex.ZPoly) :
    Hex.Factorization.product (Hex.factor f) = f := by
  sorry

/--
Every factor emitted by the default executable factorization is irreducible
after transport to Mathlib's polynomial model.
-/
theorem factor_irreducible (f : Hex.ZPoly) :
    ∀ entry ∈ (Hex.factor f).factors,
      Irreducible (HexPolyZMathlib.toPolynomial entry.1) := by
  sorry

/--
Two irreducible executable factorizations of the same polynomial have the same
transported Mathlib factors up to units and permutation.
-/
theorem factor_unique (f : Hex.ZPoly) (gs hs : Array Hex.ZPoly) :
    Array.foldl (· * ·) 1 gs = f →
    Array.foldl (· * ·) 1 hs = f →
    (∀ g ∈ gs, Irreducible (HexPolyZMathlib.toPolynomial g)) →
    (∀ h ∈ hs, Irreducible (HexPolyZMathlib.toPolynomial h)) →
    List.Perm
      (gs.toList.map fun g => Associates.mk (HexPolyZMathlib.toPolynomial g))
      (hs.toList.map fun h => Associates.mk (HexPolyZMathlib.toPolynomial h)) := by
  sorry

/--
The executable integer-polynomial irreducibility checker is sound after
transport to Mathlib's polynomial model.
-/
theorem checkIrreducibleCert_sound
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate) :
    Hex.checkIrreducibleCert f cert = true → Irreducible (HexPolyZMathlib.toPolynomial f) := by
  sorry

end

end HexBerlekampZassenhausMathlib
