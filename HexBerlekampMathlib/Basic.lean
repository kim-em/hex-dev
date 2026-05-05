import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility
import HexModArithMathlib
import HexPolyMathlib
import Mathlib.FieldTheory.Finite.GaloisField

/-!
Mathlib-facing correctness surface for `HexBerlekamp`.

This module transfers executable `FpPoly p` values to Mathlib polynomials over
`ZMod p` and states the initial Berlekamp-factor and Rabin-test correctness
theorems used by downstream finite-field factorization proofs.
-/

namespace HexBerlekampMathlib

universe u

noncomputable section

open Polynomial

variable {p : Nat} [Hex.ZMod64.Bounds p]

/-- Interpret an executable `FpPoly p` as a Mathlib polynomial over `ZMod p`. -/
def fpPolyToPolynomial (f : Hex.FpPoly p) : Polynomial (ZMod p) :=
  Finset.sum (Finset.range f.size) fun i =>
    Polynomial.monomial i (HexModArithMathlib.ZMod64.toZMod (f.coeff i))

/-- Rebuild an executable `FpPoly p` from a Mathlib polynomial over `ZMod p`. -/
def polynomialToFpPoly (f : Polynomial (ZMod p)) : Hex.FpPoly p :=
  Hex.DensePoly.ofCoeffs <|
    ((List.range (f.natDegree + 1)).map fun i =>
      HexModArithMathlib.ZMod64.equiv.symm (f.coeff i)).toArray

/--
The executable finite-field polynomial representation is ring-equivalent to
Mathlib polynomials over `ZMod p`.
-/
def fpPolyEquiv : Hex.FpPoly p ≃+* Polynomial (ZMod p) where
  toFun := fpPolyToPolynomial
  invFun := polynomialToFpPoly
  left_inv := by
    sorry
  right_inv := by
    sorry
  map_mul' := by
    sorry
  map_add' := by
    sorry

/-- Interpret an executable `FpPoly p` as a Mathlib polynomial over `ZMod p`. -/
def toMathlibPolynomial (f : Hex.FpPoly p) : Polynomial (ZMod p) :=
  fpPolyEquiv f

@[simp]
theorem fpPolyEquiv_apply (f : Hex.FpPoly p) :
    fpPolyEquiv f = toMathlibPolynomial f := by
  rfl

@[simp]
theorem fpPolyEquiv_symm_apply (f : Polynomial (ZMod p)) :
    fpPolyEquiv.symm f = polynomialToFpPoly f := by
  rfl

@[simp]
theorem coeff_toMathlibPolynomial (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.toZMod (f.coeff n) := by
  sorry

@[simp]
theorem coeff_toMathlibPolynomial_equiv (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.equiv (f.coeff n) := by
  sorry

/-- Coefficient view supplied by the general dense-polynomial bridge. -/
theorem hexPolyMathlib_coeff_bridge
    {R : Type u} [Semiring R] [DecidableEq R] (f : Hex.DensePoly R) (n : Nat) :
    (HexPolyMathlib.toPolynomial f).coeff n = f.coeff n := by
  simp

/--
The direct finite-field transport is the coefficientwise lift along
`ZMod64.equiv`, matching the coefficient view supplied by the generic
dense-polynomial bridge.
-/
theorem toMathlibPolynomial_coeff_bridge (f : Hex.FpPoly p) (n : Nat) :
    (toMathlibPolynomial f).coeff n = HexModArithMathlib.ZMod64.equiv (f.coeff n) :=
  coeff_toMathlibPolynomial_equiv f n

/-- Monicity of executable finite-field polynomials transfers to Mathlib. -/
theorem toMathlibPolynomial_monic (f : Hex.FpPoly p) :
    Hex.DensePoly.Monic f → (toMathlibPolynomial f).Monic := by
  sorry

/-- The executable Berlekamp basis size is the Mathlib natural degree after transport. -/
theorem natDegree_toMathlibPolynomial_eq_basisSize
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f) :
    (toMathlibPolynomial f).natDegree = Hex.Berlekamp.basisSize f := by
  sorry

/-- Formal derivatives commute with the finite-field polynomial transport. -/
theorem toMathlibPolynomial_derivative (f : Hex.FpPoly p) :
    toMathlibPolynomial (Hex.DensePoly.derivative f) =
      Polynomial.derivative (toMathlibPolynomial f) := by
  sorry

namespace Rabin

/-- The Mathlib polynomial `X^(p^n) - X` used by Rabin's divisibility leg. -/
abbrev frobeniusPolynomial (p n : Nat) : Polynomial (ZMod p) :=
  X ^ (p ^ n) - X

/-
Divisibility by the modulus is exactly vanishing in the corresponding
`AdjoinRoot` quotient.
-/
omit [Hex.ZMod64.Bounds p] in
theorem adjoinRoot_mk_eq_zero_of_dvd
    (g P : Polynomial (ZMod p)) :
    AdjoinRoot.mk g P = 0 ↔ g ∣ P := by
  exact AdjoinRoot.mk_eq_zero

/--
If an irreducible `g` divides `X^(p^n) - X`, its quotient root maps into the
degree-`n` Galois field over `ZMod p`.
-/
theorem exists_algHom_adjoinRoot_to_galoisField
    [Fact (Nat.Prime p)] {n : Nat} (hn : n ≠ 0)
    {g : Polynomial (ZMod p)}
    (hg_irreducible : Irreducible g)
    (hg_dvd : g ∣ frobeniusPolynomial p n) :
    Nonempty (AdjoinRoot g →ₐ[ZMod p] GaloisField p n) := by
  sorry

/--
The finite-dimensional rank of an `AdjoinRoot` quotient by a nonzero
polynomial is its natural degree.
-/
theorem finrank_adjoinRoot_eq_natDegree
    [Fact (Nat.Prime p)] {g : Polynomial (ZMod p)} (hg : g ≠ 0) :
    Module.finrank (ZMod p) (AdjoinRoot g) = g.natDegree := by
  sorry

/--
The Rabin finite-field degree lemma in the local `ZMod p` form used by the
contrapositive proof.
-/
theorem natDegree_dvd_of_irreducible_dvd_frobeniusPolynomial
    [Fact (Nat.Prime p)] {n : Nat} {g : Polynomial (ZMod p)}
    (hg_irreducible : Irreducible g)
    (hg_dvd : g ∣ frobeniusPolynomial p n) :
    g.natDegree ∣ n := by
  sorry

/--
For an irreducible polynomial, any nontrivial gcd/coprimality failure with
`P` forces divisibility by `P`.
-/
theorem irreducible_dvd_of_not_isCoprime
    [Fact (Nat.Prime p)] {g P : Polynomial (ZMod p)}
    (hg_irreducible : Irreducible g)
    (hnot_coprime : ¬ IsCoprime g P) :
    g ∣ P := by
  sorry

/--
Divisor arithmetic used by Rabin's reducible contrapositive: a proper divisor
`d` of `n` yields a prime `q` such that `q ∣ n` and `d ∣ n / q`.
-/
theorem exists_prime_divisor_with_divisor_quotient
    {d n : Nat} (hd_pos : 0 < d) (hd_dvd : d ∣ n) (hd_lt : d < n) :
    ∃ q : Nat, Nat.Prime q ∧ q ∣ n / d ∧ q ∣ n ∧ d ∣ n / q := by
  sorry

/--
The executable Rabin test passing entails the exact Mathlib divisibility and
coprimality checks appearing in Rabin's criterion.
-/
theorem rabinTest_true_to_mathlib_checks
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] {n : Nat}
    (hdegree : Hex.Berlekamp.basisSize f = n)
    (htest : Hex.Berlekamp.rabinTest f hmonic = true) :
    0 < n ∧
      toMathlibPolynomial f ∣ frobeniusPolynomial p n ∧
      ∀ d ∈ Hex.Berlekamp.maximalProperDivisors n,
        IsCoprime (toMathlibPolynomial f) (frobeniusPolynomial p d) := by
  sorry

/--
The Mathlib Rabin checks imply the executable test surface once the transport
lemmas connect executable remainders and gcds to `Polynomial (ZMod p)`.
-/
theorem rabinTest_true_of_mathlib_checks
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] {n : Nat}
    (hdegree : Hex.Berlekamp.basisSize f = n)
    (hchecks :
      0 < n ∧
        toMathlibPolynomial f ∣ frobeniusPolynomial p n ∧
        ∀ d ∈ Hex.Berlekamp.maximalProperDivisors n,
          IsCoprime (toMathlibPolynomial f) (frobeniusPolynomial p d)) :
    Hex.Berlekamp.rabinTest f hmonic = true := by
  sorry

end Rabin

/-- Executable gcd transfers to Mathlib's gcd after coefficient transport. -/
theorem toMathlibPolynomial_gcd
    [Fact (Nat.Prime p)] (f g : Hex.FpPoly p) :
    toMathlibPolynomial (Hex.DensePoly.gcd f g) =
      gcd (toMathlibPolynomial f) (toMathlibPolynomial g) := by
  sorry

/--
The executable square-free hypothesis used by Berlekamp is the corresponding
Mathlib coprimality condition between the transported polynomial and its
formal derivative.
-/
theorem toMathlibPolynomial_squareFree_coprime
    [Fact (Nat.Prime p)] (f : Hex.FpPoly p)
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    IsCoprime (toMathlibPolynomial f) (Polynomial.derivative (toMathlibPolynomial f)) := by
  sorry

/--
Every factor emitted by executable Berlekamp factorization is irreducible after
transport to Mathlib's polynomial model.
-/
theorem irreducible_of_mem_berlekampFactor
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Lean.Grind.Field (Hex.ZMod64 p)]
    (_hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    ∀ g ∈ (Hex.Berlekamp.berlekampFactor f hmonic).factors,
      Irreducible (toMathlibPolynomial g) := by
  sorry

/--
Rabin's executable test is equivalent to Mathlib irreducibility for the
transported polynomial.
-/
theorem rabin_irreducible
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] (n : Nat) (_hdegree : Hex.Berlekamp.basisSize f = n) :
    Hex.Berlekamp.rabinTest f hmonic = true ↔ Irreducible (toMathlibPolynomial f) := by
  sorry

/--
Rabin's executable test is equivalent to Mathlib irreducibility with the
explicit positive-degree hypothesis used by the finite-field proof.
-/
theorem rabin_irreducible_of_positive_degree
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] {n : Nat}
    (_hdegree : Hex.Berlekamp.basisSize f = n) (_hpos : 0 < n) :
    Hex.Berlekamp.rabinTest f hmonic = true ↔ Irreducible (toMathlibPolynomial f) := by
  sorry

/--
Accepted executable irreducibility certificates imply Mathlib irreducibility
after transporting the checked polynomial to `Polynomial (ZMod p)`.
-/
theorem checkIrreducibilityCertificate_irreducible
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Hex.ZMod64.PrimeModulus p] [Fact (Nat.Prime p)]
    (cert : Hex.Berlekamp.IrreducibilityCertificate) :
    Hex.Berlekamp.checkIrreducibilityCertificate f hmonic cert = true →
      Irreducible (toMathlibPolynomial f) := by
  intro hcheck
  exact (rabin_irreducible f hmonic (Hex.Berlekamp.basisSize f) rfl).mp
    (Hex.Berlekamp.checkIrreducibilityCertificate_rabinTest f hmonic cert hcheck)

/-- Mathlib irreducibility over `Polynomial (ZMod p)` is classically decidable. -/
instance irreducibleDecidablePred (p : Nat) [Fact (Nat.Prime p)] :
    DecidablePred (fun f : Polynomial (ZMod p) => Irreducible f) :=
  Classical.decPred _

end

end HexBerlekampMathlib
