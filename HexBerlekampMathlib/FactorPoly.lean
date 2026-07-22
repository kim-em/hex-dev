/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampMathlib.Basic
public import HexBerlekamp.IrreducibleDecide

public section

/-!
The Mathlib-side result type of `factor_poly` for `Polynomial R` inputs, and
the kernel-decidable assemblers the `Polynomial (ZMod q)` provider emits.

`FactoredPoly P` is the `Polynomial`-level counterpart of
`Hex.FpPoly.Factored` / `Hex.ZPoly.Factored`. The assemblers `FactoredPoly.ofFp`
and `irreducible_ofFp` take only Boolean checks on reified executable literals
(discharged by `Eq.refl true`/`Eq.refl false` in emitted terms) plus one bridge
equation `toMathlibPolynomial f = P` built by the provider's parser, so the
kernel verifies emitted factorizations by reduction plus the named transport
lemmas alone — the factorizer and certificate generator never appear in
emitted terms.
-/

namespace Hex

/-- A certified irreducible factorization of `P : Polynomial R`; Mathlib-side
counterpart of `FpPoly.Factored`/`ZPoly.Factored`. Produced by the
`factor_poly` elaborator via the Mathlib bridge providers. -/
structure FactoredPoly {R : Type*} [CommRing R] (P : Polynomial R) where
  /-- The unit scalar (the leading coefficient for nonzero `P`). -/
  scalar : R
  /-- The irreducible factors, with repetition. -/
  factors : List (Polynomial R)
  /-- The scalar times the factor product reconstructs `P`. -/
  factors_mul : Polynomial.C scalar * factors.prod = P
  /-- Every listed factor is irreducible. -/
  factors_irred : ∀ q ∈ factors, Irreducible q

end Hex

namespace HexBerlekampMathlib

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- The Mathlib-free `Hex.Nat.Prime` witness yields Mathlib's `Nat.Prime`. -/
theorem nat_prime_of_hex {p : Nat} (hp : Hex.Nat.Prime p) : Nat.Prime p :=
  Nat.prime_def.mpr ⟨hp.1, hp.2⟩

/-- The executable constant `1` transports to the Mathlib constant `1`.
(`map_one` through `fpPolyEquiv` needs a `MulOneClass` instance `FpPoly` does
not carry, so this is proved through `DensePoly.C`.) -/
theorem toMathlibPolynomial_one :
    toMathlibPolynomial (1 : Hex.FpPoly p) = 1 := by
  have h : (1 : Hex.FpPoly p) = Hex.DensePoly.C 1 := rfl
  rw [h, toMathlibPolynomial_C, HexModArithMathlib.ZMod64.toZMod_one, Polynomial.C_1]

/-- Negation commutes with the finite-field polynomial transport. -/
theorem toMathlibPolynomial_neg (f : Hex.FpPoly p) :
    toMathlibPolynomial (-f) = -toMathlibPolynomial f := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_neg, coeff_toMathlibPolynomial, coeff_toMathlibPolynomial,
    Hex.DensePoly.coeff_neg f n (by show (0 : Hex.ZMod64 p) - 0 = 0; grind),
    HexModArithMathlib.ZMod64.toZMod_sub]
  calc HexModArithMathlib.ZMod64.toZMod (0 : Hex.ZMod64 p) -
        HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.coeff f n)
      = 0 - HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.coeff f n) := by
        rw [HexModArithMathlib.ZMod64.toZMod_zero]
    _ = -HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.coeff f n) := zero_sub _

/-- List products commute with the finite-field polynomial transport. -/
theorem toMathlibPolynomial_listProd (l : List (Hex.FpPoly p)) :
    toMathlibPolynomial l.prod = (l.map toMathlibPolynomial).prod := by
  induction l with
  | nil => exact toMathlibPolynomial_one
  | cons a t ih =>
      rw [List.prod_cons, List.map_cons, List.prod_cons, toMathlibPolynomial_mul, ih]

end HexBerlekampMathlib

namespace Hex

open HexBerlekampMathlib

/-- One-shot assembler for the `factor_poly` provider on `Polynomial (ZMod p)`:
every certification slot is a Boolean check on reified literal data (filled by
`Eq.refl true` in emitted terms), and `hP` is the parser-built bridge equation
tying the reified executable polynomial to the user's Mathlib polynomial. -/
@[expose]
noncomputable def FactoredPoly.ofFp {p : Nat} [inst : Hex.ZMod64.Bounds p]
    (P : Polynomial (ZMod p)) (f : Hex.FpPoly p) (s : Hex.ZMod64 p)
    (factors : List (Hex.FpPoly p))
    (certified : List (Hex.FpPoly p × Hex.ZMod64 p × Hex.Berlekamp.IrreducibilityCertificate))
    (hp : Hex.Nat.isPrimeTrial p = true)
    (hmul : Hex.DensePoly.beqCoeffs (Hex.DensePoly.C s * factors.prod) f = true)
    (hdeg : factors.all (fun g => decide (0 < g.degree?.getD 0)) = true)
    (hcheck : Hex.Berlekamp.checkIrredCover factors certified = true)
    (hP : toMathlibPolynomial f = P) : Hex.FactoredPoly P where
  scalar := HexModArithMathlib.ZMod64.toZMod s
  factors := factors.map toMathlibPolynomial
  factors_mul := by
    calc Polynomial.C (HexModArithMathlib.ZMod64.toZMod s) *
          (factors.map toMathlibPolynomial).prod
        = toMathlibPolynomial (Hex.DensePoly.C s) * toMathlibPolynomial factors.prod := by
          rw [toMathlibPolynomial_C, toMathlibPolynomial_listProd]
      _ = toMathlibPolynomial (Hex.DensePoly.C s * factors.prod) :=
          (toMathlibPolynomial_mul _ _).symm
      _ = toMathlibPolynomial f := by rw [Hex.DensePoly.eq_of_beqCoeffs hmul]
      _ = P := hP
  factors_irred := by
    haveI : Fact (_root_.Nat.Prime p) := ⟨nat_prime_of_hex (Hex.Nat.isPrimeTrial_isPrime hp)⟩
    intro q hq
    rw [List.mem_map] at hq
    obtain ⟨g, hg, rfl⟩ := hq
    have hirr := Hex.Berlekamp.irreducible_of_checkIrredCover hp factors certified hcheck g hg
    have hdeg' := List.all_eq_true.mp hdeg g hg
    exact irreducible_toMathlibPolynomial_of_fpPolyIrreducible
      (natDegree_toMathlibPolynomial_pos_of_degree?_pos (of_decide_eq_true hdeg')) hirr

end Hex

namespace HexBerlekampMathlib

/-- Kernel-decidable irreducibility endpoint for the `irreducibility` provider
on `Polynomial (ZMod p)`: the executable side is
`Berlekamp.irreducible_of_checkMonicCert_scale` on reified literals, the
positive degree transports the statement out of the vacuous-constant regime,
and `hP` is the parser-built bridge equation. -/
theorem irreducible_ofFp {p : Nat} [Hex.ZMod64.Bounds p]
    (P : Polynomial (ZMod p)) (f m : Hex.FpPoly p) (c : Hex.ZMod64 p)
    (cert : Hex.Berlekamp.IrreducibilityCertificate)
    (hp : Hex.Nat.isPrimeTrial p = true)
    (hc : decide (c = 0) = false)
    (hfm : Hex.DensePoly.beqCoeffs (Hex.DensePoly.scale c m) f = true)
    (hcheck : Hex.Berlekamp.checkMonicCert m cert = true)
    (hdeg : decide (0 < f.degree?.getD 0) = true)
    (hP : toMathlibPolynomial f = P) : Irreducible P := by
  haveI : Fact (Nat.Prime p) := ⟨nat_prime_of_hex (Hex.Nat.isPrimeTrial_isPrime hp)⟩
  have hf := Hex.Berlekamp.irreducible_of_checkMonicCert_scale f m c cert hp hc hfm hcheck
  have h := irreducible_toMathlibPolynomial_of_fpPolyIrreducible
    (natDegree_toMathlibPolynomial_pos_of_degree?_pos (of_decide_eq_true hdeg)) hf
  rwa [hP] at h

end HexBerlekampMathlib
