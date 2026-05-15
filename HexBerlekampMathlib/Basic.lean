import HexBerlekamp.Factor
import HexBerlekamp.Irreducibility
import HexBerlekamp.RabinSoundness
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
The Rabin backward direction in the local `ZMod p` form: every irreducible
polynomial of degree dividing `N` divides `X^(p^N) - X`.

Used by the contrapositive direction of `rabinTest_true_irreducible` to lift
divisibility of an irreducible factor `g` from the basis-size Frobenius
polynomial down to the Frobenius polynomial at a maximal proper divisor.
-/
theorem irreducible_dvd_frobeniusPolynomial_of_natDegree_dvd
    [Fact (Nat.Prime p)] {g : Polynomial (ZMod p)}
    (hg_irreducible : Irreducible g) {N : Nat}
    (hdvd : g.natDegree ∣ N) :
    g ∣ frobeniusPolynomial p N := by
  haveI : Fact (Irreducible g) := ⟨hg_irreducible⟩
  have hg_ne_zero : g ≠ 0 := hg_irreducible.ne_zero
  haveI : Module.Finite (ZMod p) (AdjoinRoot g) :=
    (AdjoinRoot.powerBasis hg_ne_zero).finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite (ZMod p)
  haveI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcard : Fintype.card (AdjoinRoot g) = p ^ g.natDegree := by
    rw [← Nat.card_eq_fintype_card,
        ← FiniteField.pow_finrank_eq_natCard p (AdjoinRoot g),
        PowerBasis.finrank (AdjoinRoot.powerBasis hg_ne_zero),
        AdjoinRoot.powerBasis_dim hg_ne_zero]
  have hroot_pow : (AdjoinRoot.root g) ^ (p ^ N) = AdjoinRoot.root g := by
    obtain ⟨k, rfl⟩ := hdvd
    rw [pow_mul]
    have hpow := FiniteField.pow_card_pow (K := AdjoinRoot g) k (AdjoinRoot.root g)
    rwa [hcard] at hpow
  have hgoal : (AdjoinRoot.mk g) (frobeniusPolynomial p N) = 0 := by
    show (AdjoinRoot.mk g) (X ^ p ^ N - X) = 0
    rw [← AdjoinRoot.aeval_eq, map_sub, map_pow, Polynomial.aeval_X, hroot_pow, sub_self]
  exact AdjoinRoot.mk_eq_zero.mp hgoal

/-- Maximal proper divisors are positive. -/
theorem maximalProperDivisors_pos {n d : Nat}
    (hmem : d ∈ Hex.Berlekamp.maximalProperDivisors n) :
    0 < d := by
  unfold Hex.Berlekamp.maximalProperDivisors Hex.Berlekamp.properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range] at hmem
  rcases hmem with ⟨⟨⟨k, _hk, rfl⟩, _hdvd⟩, _hmax⟩
  exact Nat.succ_pos k

/-- Maximal proper divisors are strictly below the ambient degree. -/
theorem maximalProperDivisors_lt {n d : Nat}
    (hmem : d ∈ Hex.Berlekamp.maximalProperDivisors n) :
    d < n := by
  unfold Hex.Berlekamp.maximalProperDivisors Hex.Berlekamp.properDivisors at hmem
  simp only [List.mem_filter, List.mem_map, List.mem_range] at hmem
  rcases hmem with ⟨⟨⟨k, hk, rfl⟩, _hdvd⟩, _hmax⟩
  omega

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
If executable Berlekamp factorization cannot split a monic square-free input,
then the input itself is irreducible after transport to Mathlib.

The executable factor list is never empty; with length at most one, its head is
therefore a member of the Berlekamp output, so the existing per-emitted-factor
irreducibility theorem applies directly.
-/
theorem irreducible_of_berlekampFactor_factors_length_le_one
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Lean.Grind.Field (Hex.ZMod64 p)] [Hex.ZMod64.PrimeModulus p]
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1)
    (hsmall : (Hex.Berlekamp.berlekampFactor f hmonic).factors.length ≤ 1) :
    Irreducible (toMathlibPolynomial f) := by
  cases hfactors : (Hex.Berlekamp.berlekampFactor f hmonic).factors with
  | nil =>
      exact False.elim
        (Hex.Berlekamp.berlekampFactor_factors_ne_nil f hmonic hfactors)
  | cons g rest =>
      cases rest with
      | nil =>
          have hg_eq : g = f := by
            have hprod := Hex.Berlekamp.prod_berlekampFactor f hmonic hsquareFree
            rw [Hex.Berlekamp.Factorization.product_def] at hprod
            simp [hfactors, Hex.Berlekamp.factorProduct_cons] at hprod
            exact hprod
          have hirr_g :
              Irreducible (toMathlibPolynomial g) :=
            irreducible_of_mem_berlekampFactor f hmonic hsquareFree g (by simp [hfactors])
          simpa [hg_eq] using hirr_g
      | cons h rest =>
          simp [hfactors] at hsmall

/--
Forward Rabin soundness: when the executable Rabin test accepts, the
transported Mathlib polynomial is irreducible.
-/
theorem rabinTest_true_irreducible
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] :
    Hex.Berlekamp.rabinTest f hmonic = true →
      Irreducible (toMathlibPolynomial f) := by
  intro htest
  set fM := toMathlibPolynomial f
  set n := Hex.Berlekamp.basisSize f
  obtain ⟨hpos, hf_dvd, hcoprime⟩ :=
    Rabin.rabinTest_true_to_mathlib_checks f hmonic rfl htest
  have hfM_monic : fM.Monic := toMathlibPolynomial_monic f hmonic
  have hfM_natDegree : fM.natDegree = n :=
    natDegree_toMathlibPolynomial_eq_basisSize f hmonic
  have hfM_pos : 0 < fM.natDegree := hfM_natDegree.symm ▸ hpos
  refine ⟨fun hunit => by
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega, ?_⟩
  intro a b hab
  by_contra hcontr
  push Not at hcontr
  obtain ⟨ha_not_unit, hb_not_unit⟩ := hcontr
  have hfM_ne_zero : fM ≠ 0 := hfM_monic.ne_zero
  have ha_ne_zero : a ≠ 0 := fun h => by
    subst h; simp [zero_mul] at hab; exact hfM_ne_zero hab
  have hb_ne_zero : b ≠ 0 := fun h => by
    subst h; simp [mul_zero] at hab; exact hfM_ne_zero hab
  -- Both factors are nonconstant divisors of a monic polynomial.
  have hb_natDegree_pos : 0 < b.natDegree :=
    Polynomial.natDegree_pos_of_not_isUnit_of_dvd_monic hfM_monic hb_not_unit
      (hab ▸ dvd_mul_left b a)
  have ha_natDegree_lt : a.natDegree < n := by
    have hsum : a.natDegree + b.natDegree = n := by
      rw [← hfM_natDegree, hab, Polynomial.natDegree_mul ha_ne_zero hb_ne_zero]
    omega
  -- Pick an irreducible factor `g` of `a`; then `g ∣ fM` and `g ∣ X^(p^n) - X`.
  obtain ⟨g, hg_irr, hg_dvd_a⟩ :=
    WfDvdMonoid.exists_irreducible_factor ha_not_unit ha_ne_zero
  have hg_dvd_fM : g ∣ fM := hg_dvd_a.trans (hab ▸ dvd_mul_right a b)
  have hg_natDegree_dvd_n : g.natDegree ∣ n :=
    Rabin.natDegree_dvd_of_irreducible_dvd_frobeniusPolynomial
      hg_irr (hg_dvd_fM.trans hf_dvd)
  -- `natDegree g < n` because `natDegree g ≤ natDegree a < n`.
  have hg_natDegree_lt : g.natDegree < n :=
    lt_of_le_of_lt
      (Polynomial.natDegree_le_of_dvd hg_dvd_a ha_ne_zero) ha_natDegree_lt
  -- Route `natDegree g` through some maximal proper divisor of `n`.
  obtain ⟨m, hm_mem, hg_natDegree_dvd_m⟩ :=
    Hex.Berlekamp.exists_maximalProperDivisor_dvd
      hg_irr.natDegree_pos hg_natDegree_dvd_n hg_natDegree_lt
  -- The Rabin coprimality leg at `m` and the new substrate combine to force
  -- `g` to be a unit, contradicting irreducibility.
  exact hg_irr.not_isUnit ((hcoprime m hm_mem).isUnit_of_dvd' hg_dvd_fM
    (Rabin.irreducible_dvd_frobeniusPolynomial_of_natDegree_dvd
      hg_irr hg_natDegree_dvd_m))

/--
Rabin's executable test is equivalent to Mathlib irreducibility for the
transported polynomial.
-/
theorem rabin_irreducible
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] (n : Nat) (hdegree : Hex.Berlekamp.basisSize f = n) :
    Hex.Berlekamp.rabinTest f hmonic = true ↔ Irreducible (toMathlibPolynomial f) := by
  constructor
  · exact rabinTest_true_irreducible f hmonic
  · intro hirr
    set fM := toMathlibPolynomial f
    have hfM_monic : fM.Monic := toMathlibPolynomial_monic f hmonic
    have hfM_natDegree : fM.natDegree = n := by
      simpa [fM, hdegree] using natDegree_toMathlibPolynomial_eq_basisSize f hmonic
    have hn_pos : 0 < n := by
      have hpos : 0 < fM.natDegree :=
        hfM_monic.natDegree_pos_of_not_isUnit hirr.not_isUnit
      simpa [hfM_natDegree] using hpos
    refine Rabin.rabinTest_true_of_mathlib_checks f hmonic hdegree ?_
    refine ⟨hn_pos, ?_, ?_⟩
    · have hdiv : fM.natDegree ∣ n := by
        rw [hfM_natDegree]
      simpa [fM] using
        Rabin.irreducible_dvd_frobeniusPolynomial_of_natDegree_dvd
          (p := p) (g := fM) hirr hdiv
    · intro d hd_mem
      by_contra hnot_coprime
      have hdiv_d : fM ∣ Rabin.frobeniusPolynomial p d :=
        Rabin.irreducible_dvd_of_not_isCoprime hirr hnot_coprime
      have hn_dvd_d : n ∣ d := by
        have hdeg_dvd :
            fM.natDegree ∣ d :=
          Rabin.natDegree_dvd_of_irreducible_dvd_frobeniusPolynomial
            hirr hdiv_d
        simpa [hfM_natDegree] using hdeg_dvd
      have hd_pos : 0 < d := Rabin.maximalProperDivisors_pos hd_mem
      have hn_le_d : n ≤ d := Nat.le_of_dvd hd_pos hn_dvd_d
      have hd_lt_n : d < n := Rabin.maximalProperDivisors_lt hd_mem
      exact (not_lt_of_ge hn_le_d) hd_lt_n

/--
Rabin's executable test is equivalent to Mathlib irreducibility with the
explicit positive-degree hypothesis used by the finite-field proof.
-/
theorem rabin_irreducible_of_positive_degree
    (f : Hex.FpPoly p) (hmonic : Hex.DensePoly.Monic f)
    [Fact (Nat.Prime p)] {n : Nat}
    (hdegree : Hex.Berlekamp.basisSize f = n) (_hpos : 0 < n) :
    Hex.Berlekamp.rabinTest f hmonic = true ↔ Irreducible (toMathlibPolynomial f) := by
  exact rabin_irreducible f hmonic n hdegree

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
  exact rabinTest_true_irreducible f hmonic
    (Hex.Berlekamp.checkIrreducibilityCertificate_rabinTest f hmonic cert hcheck)

/-- Mathlib irreducibility over `Polynomial (ZMod p)` is classically decidable. -/
instance irreducibleDecidablePred (p : Nat) [Fact (Nat.Prime p)] :
    DecidablePred (fun f : Polynomial (ZMod p) => Irreducible f) :=
  Classical.decPred _

end

end HexBerlekampMathlib
