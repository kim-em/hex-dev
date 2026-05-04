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

private def isUnitFactor (g : Hex.ZPoly) : Bool :=
  match g.degree? with
  | some 0 => g.coeff 0 == 1 || g.coeff 0 == -1
  | _ => false

private def nonUnitFactorCount (factors : Array Hex.ZPoly) : Nat :=
  (factors.toList.filter fun g => !isUnitFactor g).length

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
