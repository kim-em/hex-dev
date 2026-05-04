import HexBerlekampZassenhaus
import HexPolyZMathlib.Basic
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

/-- The default executable factorization multiplies back to the input. -/
theorem factor_product (f : Hex.ZPoly) :
    Array.foldl (· * ·) 1 (Hex.factor f) = f := by
  sorry

/--
Every factor emitted by the default executable factorization is irreducible
after transport to Mathlib's polynomial model.
-/
theorem factor_irreducible (f : Hex.ZPoly) :
    ∀ g ∈ Hex.factor f, Irreducible (HexPolyZMathlib.toPolynomial g) := by
  sorry

/--
Two irreducible executable factorizations of the same polynomial have the same
factor list, up to the equality relation used by `List.Perm`.
-/
theorem factor_unique (f : Hex.ZPoly) (gs hs : Array Hex.ZPoly) :
    Array.foldl (· * ·) 1 gs = f →
    Array.foldl (· * ·) 1 hs = f →
    (∀ g ∈ gs, Irreducible (HexPolyZMathlib.toPolynomial g)) →
    (∀ h ∈ hs, Irreducible (HexPolyZMathlib.toPolynomial h)) →
    List.Perm gs.toList hs.toList := by
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
