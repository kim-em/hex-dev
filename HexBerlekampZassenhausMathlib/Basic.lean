import HexBerlekampZassenhaus
import HexBerlekampZassenhausMathlib.UFDPartition
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
  have hf_poly : HexPolyZMathlib.toPolynomial f ≠ 0 := by
    intro h
    apply hf
    apply HexPolyZMathlib.equiv.injective
    simpa using h
  have hgf_poly :
      HexPolyZMathlib.toPolynomial g ∣ HexPolyZMathlib.toPolynomial f :=
    HexPolyMathlib.toPolynomial_dvd hgf
  have hbound :=
    Polynomial.natDegree_le_of_dvd hgf_poly hf_poly
  rw [HexPolyMathlib.natDegree_toPolynomial f] at hbound
  exact hbound

/--
The executable natural L2 bound dominates the real coefficient-vector norm used
by the Mathlib Mignotte theorem.
-/
theorem l2norm_toPolynomial_le_coeffL2NormBound (f : Hex.ZPoly) :
    HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f) ≤
      (Hex.ZPoly.coeffL2NormBound f : ℝ) := by
  have hsq :=
    HexPolyZMathlib.l2norm_toPolynomial_sq_le_coeffNormSq f
  have hceil_nat :
      Hex.ZPoly.coeffNormSq f ≤ (Hex.ZPoly.coeffL2NormBound f) ^ 2 := by
    simpa [Hex.ZPoly.coeffL2NormBound_eq_ceilSqrt_coeffNormSq] using
      Hex.ZPoly.le_ceilSqrt_sq (Hex.ZPoly.coeffNormSq f)
  have hceil_real :
      (Hex.ZPoly.coeffNormSq f : ℝ) ≤
        (Hex.ZPoly.coeffL2NormBound f : ℝ) ^ 2 := by
    exact_mod_cast hceil_nat
  exact le_of_sq_le_sq (hsq.trans hceil_real) (by positivity)

/--
The default executable factorization bound is strong enough for every
coefficient of every executable divisor of a nonzero input.
-/
theorem defaultFactorCoeffBound_valid
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∀ g : Hex.ZPoly, g ∣ f → ∀ i, (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound f := by
  intro g hgf i
  have hf_poly : HexPolyZMathlib.toPolynomial f ≠ 0 := by
    intro h
    apply hf
    exact HexPolyZMathlib.equiv.injective (by simpa using h)
  have hgf_poly : HexPolyZMathlib.toPolynomial g ∣ HexPolyZMathlib.toPolynomial f :=
    HexPolyMathlib.toPolynomial_dvd hgf
  have hdegree :
      (HexPolyZMathlib.toPolynomial g).natDegree ≤ f.degree?.getD 0 :=
    natDegree_toPolynomial_le_degree_getD_of_dvd f g hf hgf
  have hcoeff_eq : (HexPolyZMathlib.toPolynomial g).coeff i = g.coeff i :=
    HexPolyZMathlib.coeff_toPolynomial g i
  by_cases hi : i ≤ (HexPolyZMathlib.toPolynomial g).natDegree
  · -- The interesting case: i is within the factor's natural degree.
    have hmignotte :=
      HexPolyZMathlib.mignotte_bound
        (HexPolyZMathlib.toPolynomial f) (HexPolyZMathlib.toPolynomial g)
        hf_poly hgf_poly i
    rw [hcoeff_eq] at hmignotte
    have hl2 :
        HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f) ≤
          (Hex.ZPoly.coeffL2NormBound f : ℝ) :=
      l2norm_toPolynomial_le_coeffL2NormBound f
    have hchoose_nonneg :
        (0 : ℝ) ≤ Nat.choose (HexPolyZMathlib.toPolynomial g).natDegree i :=
      Nat.cast_nonneg _
    have hstep :
        ((g.coeff i).natAbs : ℝ) ≤
          (Nat.choose (HexPolyZMathlib.toPolynomial g).natDegree i : ℝ) *
            (Hex.ZPoly.coeffL2NormBound f : ℝ) :=
      hmignotte.trans (mul_le_mul_of_nonneg_left hl2 hchoose_nonneg)
    have hbinom :
        (Nat.choose (HexPolyZMathlib.toPolynomial g).natDegree i : ℝ) =
          (Hex.ZPoly.binom (HexPolyZMathlib.toPolynomial g).natDegree i : ℝ) := by
      rw [HexPolyZMathlib.binom_eq_choose]
    rw [hbinom] at hstep
    have huniform_nat :=
      Hex.ZPoly.mignotteCoeffBound_le_defaultFactorCoeffBound
        f (k := (HexPolyZMathlib.toPolynomial g).natDegree) (j := i) hdegree hi
    have hmig_eq :
        Hex.ZPoly.mignotteCoeffBound f
            (HexPolyZMathlib.toPolynomial g).natDegree i =
          Hex.ZPoly.binom (HexPolyZMathlib.toPolynomial g).natDegree i *
            Hex.ZPoly.coeffL2NormBound f :=
      Hex.ZPoly.mignotteCoeffBound_eq f _ _
    have huniform_real :
        (Hex.ZPoly.binom (HexPolyZMathlib.toPolynomial g).natDegree i : ℝ) *
          (Hex.ZPoly.coeffL2NormBound f : ℝ) ≤
          (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) := by
      have := huniform_nat
      rw [hmig_eq] at this
      exact_mod_cast this
    have hfinal :
        ((g.coeff i).natAbs : ℝ) ≤ (Hex.ZPoly.defaultFactorCoeffBound f : ℝ) :=
      hstep.trans huniform_real
    exact_mod_cast hfinal
  · -- Outside the factor's natural degree the coefficient is zero.
    have hi' : (HexPolyZMathlib.toPolynomial g).natDegree < i := Nat.lt_of_not_le hi
    have hcoeff_zero : (HexPolyZMathlib.toPolynomial g).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt hi'
    have hgcoeff_zero : g.coeff i = 0 := hcoeff_eq ▸ hcoeff_zero
    simp [hgcoeff_zero]

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
@[simp]
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
@[simp]
theorem factor_product (f : Hex.ZPoly) :
    Hex.Factorization.product (Hex.factor f) = f := by
  exact Hex.factorWithBound_product f (Hex.ZPoly.defaultFactorCoeffBound f)

/--
The Mathlib-free executable irreducibility predicate agrees with Mathlib's
irreducibility predicate after transport to `Polynomial ℤ`.
-/
theorem Hex.ZPoly.Irreducible_iff_polynomialIrreducible (f : Hex.ZPoly) :
    Hex.ZPoly.Irreducible f ↔ Irreducible (HexPolyZMathlib.toPolynomial f) := by
  constructor
  · intro hf
    refine ⟨?_, ?_⟩
    · intro hunit
      exact hf.not_unit ((HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mpr hunit)
    · intro a b hfactor
      have hfactor_hex :
          f = HexPolyZMathlib.ofPolynomial a * HexPolyZMathlib.ofPolynomial b := by
        apply HexPolyZMathlib.equiv.injective
        simpa [HexPolyZMathlib.equiv_apply] using hfactor
      rcases hf.no_factors _ _ hfactor_hex with hunit | hunit
      · left
        simpa using
          (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit
            (HexPolyZMathlib.ofPolynomial a)).mp hunit
      · right
        simpa using
          (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit
            (HexPolyZMathlib.ofPolynomial b)).mp hunit
  · intro hf
    refine
      { not_zero := ?_
        not_unit := ?_
        no_factors := ?_ }
    · intro hzero
      exact hf.ne_zero (by simp [hzero])
    · intro hunit
      exact hf.not_isUnit ((HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mp hunit)
    · intro a b hfactor
      have hfactor_poly :
          HexPolyZMathlib.toPolynomial f =
            HexPolyZMathlib.toPolynomial a * HexPolyZMathlib.toPolynomial b := by
        simpa using congrArg HexPolyZMathlib.toPolynomial hfactor
      rcases hf.isUnit_or_isUnit hfactor_poly with hunit | hunit
      · left
        exact (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit a).mpr hunit
      · right
        exact (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit b).mpr hunit

/--
Mathlib irreducibility of the transported polynomial is equivalent to the
Mathlib-free executable irreducibility predicate.
-/
theorem Hex.ZPoly.polynomialIrreducible_iff_irreducible (f : Hex.ZPoly) :
    Irreducible (HexPolyZMathlib.toPolynomial f) ↔ Hex.ZPoly.Irreducible f :=
  (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).symm

/--
Every polynomial factor emitted by the default executable factorization is
irreducible in the executable `Hex.ZPoly` sense.
-/
theorem factor_irreducible_of_nonUnit (f : Hex.ZPoly) :
    ∀ entry ∈ (Hex.factor f).factors, Hex.ZPoly.Irreducible entry.1 := by
  sorry

/--
Every polynomial factor emitted by the default executable factorization is
irreducible after transport to `Polynomial ℤ`.
-/
theorem factor_polynomialIrreducible_of_nonUnit (f : Hex.ZPoly) :
    ∀ entry ∈ (Hex.factor f).factors,
      Irreducible (HexPolyZMathlib.toPolynomial entry.1) := by
  intro entry hentry
  exact
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible entry.1).mp
      (factor_irreducible_of_nonUnit f entry hentry)

/--
Two irreducible executable factorizations of the same polynomial have the same
signed scalar and the same polynomial factors with multiplicities.
-/
theorem factor_unique (f : Hex.ZPoly) (φ ψ : Hex.Factorization) :
    Hex.Factorization.product φ = f →
    Hex.Factorization.product ψ = f →
    (∀ entry ∈ φ.factors, Hex.ZPoly.Irreducible entry.1) →
    (∀ entry ∈ ψ.factors, Hex.ZPoly.Irreducible entry.1) →
    φ.scalar = ψ.scalar ∧ List.Perm φ.factors.toList ψ.factors.toList := by
  sorry

/--
Uniqueness specialised against the default executable factorization, so callers
only provide the competing product and irreducibility facts.
-/
theorem factor_unique_of_product
    (f : Hex.ZPoly) (φ : Hex.Factorization)
    (hproduct : Hex.Factorization.product φ = f)
    (hirr : ∀ entry ∈ φ.factors, Hex.ZPoly.Irreducible entry.1) :
    φ.scalar = (Hex.factor f).scalar ∧
      List.Perm φ.factors.toList (Hex.factor f).factors.toList :=
  factor_unique f φ (Hex.factor f) hproduct (factor_product f) hirr
    (factor_irreducible_of_nonUnit f)

/--
The executable integer-polynomial irreducibility checker is sound after
transport to Mathlib's polynomial model.
-/
theorem checkIrreducibleCert_sound
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate) :
    Hex.checkIrreducibleCert f cert = true → Irreducible (HexPolyZMathlib.toPolynomial f) := by
  sorry

/--
The executable integer-polynomial irreducibility checker is sound for the
Mathlib-free irreducibility predicate as well.
-/
theorem checkIrreducibleCert_sound_zpoly
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate) :
    Hex.checkIrreducibleCert f cert = true → Hex.ZPoly.Irreducible f := by
  intro hcert
  exact
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).mpr
      (checkIrreducibleCert_sound f cert hcert)

private theorem toPolynomial_foldl_mul (lst : List Hex.ZPoly) (init : Hex.ZPoly) :
    HexPolyZMathlib.toPolynomial (lst.foldl (· * ·) init) =
      (lst.map HexPolyZMathlib.toPolynomial).foldl (· * ·)
        (HexPolyZMathlib.toPolynomial init) := by
  induction lst generalizing init with
  | nil => simp
  | cons head tail ih =>
      simp only [List.foldl_cons, List.map_cons]
      rw [ih (init * head), HexPolyZMathlib.toPolynomial_mul]

/-- The executable `Array.polyProduct` agrees with Mathlib's `List.prod`
after pushing each factor through the `toPolynomial` bridge.  This is the
algorithm-to-Mathlib translation needed to feed `Hex.ZPoly` factor lists
into UFD arguments over `Polynomial ℤ`. -/
private theorem toPolynomial_one_zpoly :
    HexPolyZMathlib.toPolynomial (1 : Hex.ZPoly) = 1 := by
  show HexPolyZMathlib.toPolynomial (Hex.DensePoly.C (1 : Int)) = 1
  rw [HexPolyZMathlib.toPolynomial_C]
  simp

theorem polyProduct_toPolynomial (factors : Array Hex.ZPoly) :
    HexPolyZMathlib.toPolynomial (Array.polyProduct factors) =
      (factors.toList.map HexPolyZMathlib.toPolynomial).prod := by
  show HexPolyZMathlib.toPolynomial (Array.foldl (· * ·) 1 factors) = _
  rw [← Array.foldl_toList, toPolynomial_foldl_mul factors.toList 1,
    toPolynomial_one_zpoly]
  exact List.prod_eq_foldl.symm

/-- A `Hex.ZPoly` factor that passes the executable `shouldRecordPolynomialFactor`
check is non-zero and not a unit after transport to `Polynomial ℤ`.  The
executable check rejects `0`, `1`, and `-1`, which are exactly the zero
and unit constants on the Mathlib side. -/
theorem toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
    {f : Hex.ZPoly} (h : Hex.shouldRecordPolynomialFactor f = true) :
    HexPolyZMathlib.toPolynomial f ≠ 0 ∧
      ¬ IsUnit (HexPolyZMathlib.toPolynomial f) := by
  rw [Hex.shouldRecordPolynomialFactor] at h
  -- `h : (f ≠ 0 && f ≠ 1 && f ≠ DensePoly.C (-1)) = true`
  rw [Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨⟨hne_zero, hne_one⟩, hne_neg_one⟩ := h
  have hne_zero' : f ≠ 0 := by simpa using hne_zero
  have hne_one' : f ≠ 1 := by simpa using hne_one
  have hne_neg_one' : f ≠ Hex.DensePoly.C (-1) := by simpa using hne_neg_one
  refine ⟨?_, ?_⟩
  · intro hpoly
    apply hne_zero'
    apply HexPolyZMathlib.equiv.injective
    simpa using hpoly
  · intro hunit
    have hisUnit : Hex.ZPoly.IsUnit f :=
      (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mpr hunit
    rcases hisUnit with hone | hneg_one
    · exact hne_one' (by simpa using hone)
    · exact hne_neg_one' hneg_one

/-- Algorithm-side packaging for the BHKS fast-core success branch in
the form needed by UFD arguments over `Polynomial ℤ`.  Combines the
existing product, divisibility, and `shouldRecord` invariants exposed
in `HexBerlekampZassenhaus/Basic.lean` with the `toPolynomial` bridge.
The remaining count-equality hypothesis is the open obligation of
#4022 — once supplied, this lemma feeds directly into
`HexBerlekampZassenhausMathlib.UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card`. -/
theorem factorFastCoreWithBound_some_factor_irreducible_of_count
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hcount :
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList,
      Irreducible (HexPolyZMathlib.toPolynomial factor) := by
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  have hf_ne : f ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa using hzero
  set gs : List (Polynomial ℤ) :=
    coreFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hprod : Associated gs.prod f := by
    have hp_core : Array.polyProduct coreFactors = core :=
      Hex.factorFastCoreWithBound_product core B primeData k fuel coreFactors h
    have hp_poly :
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial core := by
      rw [← polyProduct_toPolynomial, hp_core]
    rw [hgs_def, hp_poly, hf_def]
  have hdvd_all :
      ∀ factor ∈ coreFactors.toList, factor ∣ core :=
    Hex.factorFastCoreWithBound_some_dvd core B primeData k fuel coreFactors h
  have hrecord_all :
      ∀ factor ∈ coreFactors.toList,
        Hex.shouldRecordPolynomialFactor factor = true :=
    Hex.factorFastCoreWithBound_some_shouldRecord h
  have hne_all : ∀ g ∈ gs, g ≠ 0 := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
        (hrecord_all factor hfactor_mem)).1
  have hnonunit_all : ∀ g ∈ gs, ¬ IsUnit g := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord
        (hrecord_all factor hfactor_mem)).2
  intro factor hfactor_mem
  have hpolyfactor_mem :
      HexPolyZMathlib.toPolynomial factor ∈ gs := by
    rw [hgs_def, List.mem_map]
    exact ⟨factor, hfactor_mem, rfl⟩
  exact
    HexBerlekampZassenhausMathlib.UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card
      hf_ne gs hne_all hnonunit_all hprod hcount _ hpolyfactor_mem

end

end HexBerlekampZassenhausMathlib
