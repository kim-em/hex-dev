import HexBerlekampZassenhaus
import HexBerlekampMathlib.Basic
import HexBerlekampZassenhausMathlib.UFDPartition
import HexHenselMathlib.Correctness
import HexPolyZMathlib.Basic
import HexPolyZMathlib.Mignotte
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
Mathlib-facing correctness surface for `HexBerlekampZassenhaus`.

This module states the unconditional integer factorization and irreducibility
certificate theorems after transporting executable `Hex.ZPoly` values to
Mathlib polynomials over `ℤ`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

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

/-- The default factor coefficient bound dominates the natural absolute value
of the leading coefficient of any nonzero executable polynomial. Standard
packaging of `defaultFactorCoeffBound_valid` at
`g := f, hgf := f ∣ f, i := f.size - 1` paired with
`leadingCoeff_eq_coeff_last`. -/
theorem defaultFactorCoeffBound_leadingCoeff_natAbs_le
    {f : Hex.ZPoly} (hf : f ≠ 0) :
    (Hex.DensePoly.leadingCoeff f).natAbs ≤
      Hex.ZPoly.defaultFactorCoeffBound f := by
  have hsize_pos : 0 < f.size := Hex.ZPoly.size_pos_of_ne_zero _ hf
  have hf_dvd_self : f ∣ f :=
    ⟨(1 : Hex.ZPoly), (Hex.DensePoly.mul_one_right_poly f).symm⟩
  rw [Hex.DensePoly.leadingCoeff_eq_coeff_last f hsize_pos]
  exact defaultFactorCoeffBound_valid f hf f hf_dvd_self (f.size - 1)

/--
Executable irreducibility predicate for transported integer polynomials.

The checker delegates to the Mathlib-free `Hex.ZPoly` executable predicate
after transporting the Mathlib polynomial into the project representation.
-/
def irreducibleByFactorization (f : Polynomial ℤ) : Bool :=
  Hex.ZPoly.isIrreducible (HexPolyZMathlib.ofPolynomial f)

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
The executable factorization predicate agrees with Mathlib irreducibility over
`Polynomial ℤ`.
-/
@[simp]
theorem irreducibleByFactorization_iff (f : Polynomial ℤ) :
    irreducibleByFactorization f = true ↔ Irreducible f := by
  rw [irreducibleByFactorization]
  constructor
  · intro h
    have hhex :
        Hex.ZPoly.Irreducible (HexPolyZMathlib.ofPolynomial f) :=
      (Hex.ZPoly.isIrreducible_iff _).mp h
    simpa [HexPolyZMathlib.toPolynomial_ofPolynomial] using
      (Hex.ZPoly.Irreducible_iff_polynomialIrreducible
        (HexPolyZMathlib.ofPolynomial f)).mp hhex
  · intro h
    exact (Hex.ZPoly.isIrreducible_iff _).mpr <|
      (Hex.ZPoly.Irreducible_iff_polynomialIrreducible
        (HexPolyZMathlib.ofPolynomial f)).mpr <| by
          simpa [HexPolyZMathlib.toPolynomial_ofPolynomial] using h

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
Bundled public contract currently available for the default executable
factorization surface.

This packages the clauses that are already exposed by the Mathlib-free and
Mathlib bridge layers: product preservation, Mathlib irreducibility of each
recorded polynomial factor, positive multiplicities, syntactic absence of
duplicate polynomial keys, and the signed-content scalar convention. The
remaining HO-1 headline strengthening is to replace the syntactic distinct-key
clause with non-association and to add the primitive-factor clause.
-/
theorem factor_headline_contract_core (f : Hex.ZPoly) :
    Hex.Factorization.product (Hex.factor f) = f ∧
      (∀ entry ∈ (Hex.factor f).factors,
        Irreducible (HexPolyZMathlib.toPolynomial entry.1)) ∧
      (∀ entry ∈ (Hex.factor f).factors, 0 < entry.2) ∧
      List.Pairwise (fun a b : Hex.ZPoly × Nat => a.1 ≠ b.1)
        (Hex.factor f).factors.toList ∧
      (Hex.factor f).scalar =
        if f = 0 then
          0
        else if Hex.DensePoly.leadingCoeff f < 0 then
          -Hex.ZPoly.content f
        else
          Hex.ZPoly.content f := by
  refine ⟨factor_product f, ?_, ?_, Hex.factor_pairwise_first f, Hex.factor_scalar f⟩
  · intro entry hentry
    exact factor_polynomialIrreducible_of_nonUnit f entry hentry
  · intro entry hentry
    exact Hex.factor_entry_multiplicity_pos f entry (Array.mem_toList_iff.mpr hentry)

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
after pushing each factor through the `toPolynomial` map.  This is the
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

/-- Expand factorization entries by multiplicity, forgetting their packed
array shape. -/
def flattenedFactorEntries (entries : List (Hex.ZPoly × Nat)) : List Hex.ZPoly :=
  entries.flatMap fun entry => List.replicate entry.2 entry.1

/-- Expand the polynomial entries of a `Hex.Factorization` by multiplicity. -/
def factorizationFlattenedFactors (φ : Hex.Factorization) : List Hex.ZPoly :=
  flattenedFactorEntries φ.factors.toList

theorem factorPower_toPolynomial (f : Hex.ZPoly) (k : Nat) :
    HexPolyZMathlib.toPolynomial (Hex.Factorization.factorPower f k) =
      HexPolyZMathlib.toPolynomial f ^ k := by
  induction k with
  | zero =>
      rw [Hex.Factorization.factorPower_zero, toPolynomial_one_zpoly]
      simp
  | succ k ih =>
      rw [Hex.Factorization.factorPower_succ, HexPolyZMathlib.toPolynomial_mul, ih]
      exact (pow_succ (HexPolyZMathlib.toPolynomial f) k).symm

theorem map_toPolynomial_replicate_prod (f : Hex.ZPoly) (k : Nat) :
    ((List.replicate k f).map HexPolyZMathlib.toPolynomial).prod =
      HexPolyZMathlib.toPolynomial f ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [List.replicate_succ, List.map_cons, List.prod_cons, ih]
      exact (pow_succ' (HexPolyZMathlib.toPolynomial f) k).symm

private theorem factorizationProduct_toPolynomial_foldl
    (entries : List (Hex.ZPoly × Nat)) (init : Hex.ZPoly) :
    HexPolyZMathlib.toPolynomial
        (entries.foldl
          (fun acc entry => acc * Hex.Factorization.factorPower entry.1 entry.2)
          init) =
      HexPolyZMathlib.toPolynomial init *
        ((flattenedFactorEntries entries).map HexPolyZMathlib.toPolynomial).prod := by
  induction entries generalizing init with
  | nil =>
      simp [flattenedFactorEntries]
  | cons entry entries ih =>
      rw [List.foldl_cons, ih (init * Hex.Factorization.factorPower entry.1 entry.2)]
      rw [HexPolyZMathlib.toPolynomial_mul, factorPower_toPolynomial]
      simp [flattenedFactorEntries]
      ring

/-- Transport `Hex.Factorization.product` to Mathlib as the scalar times the
product of the multiplicity-flattened transported factors. -/
theorem factorizationProduct_toPolynomial (φ : Hex.Factorization) :
    HexPolyZMathlib.toPolynomial φ.product =
      Polynomial.C φ.scalar *
        ((factorizationFlattenedFactors φ).map HexPolyZMathlib.toPolynomial).prod := by
  rw [Hex.Factorization.product_eq_foldl_factorPower]
  show HexPolyZMathlib.toPolynomial
      (φ.factors.foldl
        (fun acc factor => acc * Hex.Factorization.factorPower factor.1 factor.2)
        (Hex.DensePoly.C φ.scalar)) = _
  rw [← Array.foldl_toList]
  rw [factorizationProduct_toPolynomial_foldl φ.factors.toList (Hex.DensePoly.C φ.scalar)]
  rw [HexPolyZMathlib.toPolynomial_C]
  rfl

/--
A nonzero executable integer polynomial fixed by `Hex.normalizeFactorSign`
transports to a `normalize`-fixed polynomial over `ℤ`.

This is the reusable sign-normalization lemma for Mathlib-side factorization
arguments over `Hex.ZPoly` factors.
-/
theorem normalize_toPolynomial_of_normalizeFactorSign_id
    {f : Hex.ZPoly} (hne : f ≠ 0)
    (h : Hex.normalizeFactorSign f = f) :
    normalize (HexPolyZMathlib.toPolynomial f) = HexPolyZMathlib.toPolynomial f := by
  have hlc_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff f := by
    by_contra hneg
    rw [not_le] at hneg
    apply hne
    unfold Hex.normalizeFactorSign at h
    rw [if_pos hneg] at h
    apply Hex.DensePoly.ext_coeff
    intro n
    have hzero_mul : (-1 : Int) * (Zero.zero : Int) = (Zero.zero : Int) :=
      mul_zero _
    have hscale :
        (Hex.DensePoly.scale (-1 : Int) f).coeff n = (-1 : Int) * f.coeff n :=
      Hex.DensePoly.coeff_scale (-1 : Int) f n hzero_mul
    have hcoeff_eq :
        (Hex.DensePoly.scale (-1 : Int) f).coeff n = f.coeff n :=
      congrArg (fun p => Hex.DensePoly.coeff p n) h
    rw [hscale] at hcoeff_eq
    rw [Hex.DensePoly.coeff_zero]
    omega
  have hlc_poly : 0 ≤ (HexPolyZMathlib.toPolynomial f).leadingCoeff := by
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]
    exact hlc_nonneg
  rw [normalize_apply, Polynomial.coe_normUnit, Int.normUnit_eq, if_pos hlc_poly,
    Units.val_one, Polynomial.C_1, mul_one]

/--
Primitive executable integer polynomials with positive leading coefficient are
the canonical representatives of their Mathlib `Associated` class after
transport to `Polynomial ℤ`.
-/
theorem zpoly_eq_of_toPolynomial_associated_of_primitive_pos_leading
    {p q : Hex.ZPoly}
    (hp_primitive : Hex.ZPoly.Primitive p)
    (hq_primitive : Hex.ZPoly.Primitive q)
    (hp_lc : 0 < Hex.DensePoly.leadingCoeff p)
    (hq_lc : 0 < Hex.DensePoly.leadingCoeff q)
    (hassoc :
      Associated (HexPolyZMathlib.toPolynomial p)
        (HexPolyZMathlib.toPolynomial q)) :
    p = q := by
  have hp_ne : p ≠ 0 := Hex.ZPoly.ne_zero_of_primitive p hp_primitive
  have hq_ne : q ≠ 0 := Hex.ZPoly.ne_zero_of_primitive q hq_primitive
  have hp_norm_sign : Hex.normalizeFactorSign p = p := by
    unfold Hex.normalizeFactorSign
    rw [if_neg]
    omega
  have hq_norm_sign : Hex.normalizeFactorSign q = q := by
    unfold Hex.normalizeFactorSign
    rw [if_neg]
    omega
  have hp_norm :
      normalize (HexPolyZMathlib.toPolynomial p) =
        HexPolyZMathlib.toPolynomial p :=
    normalize_toPolynomial_of_normalizeFactorSign_id hp_ne hp_norm_sign
  have hq_norm :
      normalize (HexPolyZMathlib.toPolynomial q) =
        HexPolyZMathlib.toPolynomial q :=
    normalize_toPolynomial_of_normalizeFactorSign_id hq_ne hq_norm_sign
  have hpoly :
      HexPolyZMathlib.toPolynomial p = HexPolyZMathlib.toPolynomial q :=
    hassoc.eq_of_normalized hp_norm hq_norm
  exact HexPolyZMathlib.equiv.injective hpoly

/--
Distinct primitive executable integer polynomials with positive leading
coefficient are not associated after transport to `Polynomial ℤ`.
-/
theorem zpoly_not_associated_of_ne_of_primitive_pos_leading
    {p q : Hex.ZPoly}
    (hp_primitive : Hex.ZPoly.Primitive p)
    (hq_primitive : Hex.ZPoly.Primitive q)
    (hp_lc : 0 < Hex.DensePoly.leadingCoeff p)
    (hq_lc : 0 < Hex.DensePoly.leadingCoeff q)
    (hpq : p ≠ q) :
    ¬ Associated
      (HexPolyZMathlib.toPolynomial p)
      (HexPolyZMathlib.toPolynomial q) := by
  intro hassoc
  have hpeq : p = q :=
    zpoly_eq_of_toPolynomial_associated_of_primitive_pos_leading
      hp_primitive hq_primitive hp_lc hq_lc hassoc
  exact hpq hpeq

set_option maxHeartbeats 3000000

/--
Recorded entries of the default executable factorization are pairwise
non-associated after transport to `Polynomial ℤ`, assuming the selected raw
factor branch is primitive entrywise.
-/
theorem factor_entries_not_associated
    (f : Hex.ZPoly)
    (h_raw :
      ∀ rawFactors : Array Hex.ZPoly,
        (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
            some rawFactors ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            rawFactors =
              Hex.factorSlowFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f))) →
        ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Primitive raw) :
    List.Pairwise
      (fun a b : Hex.ZPoly × Nat =>
        ¬ Associated (HexPolyZMathlib.toPolynomial a.1)
          (HexPolyZMathlib.toPolynomial b.1))
      (Hex.factor f).factors.toList := by
  exact List.Pairwise.imp_of_mem
    (fun {a b} ha hb hab =>
      zpoly_not_associated_of_ne_of_primitive_pos_leading
        (Hex.factor_entries_primitive f h_raw a (Array.mem_toList_iff.mp ha))
        (Hex.factor_entries_primitive f h_raw b (Array.mem_toList_iff.mp hb))
        (Hex.factor_entry_leadingCoeff_pos f a ha)
        (Hex.factor_entry_leadingCoeff_pos f b hb)
        hab)
    (Hex.factor_pairwise_first f)

set_option maxHeartbeats 200000

private theorem mem_factorizationFlattenedFactors_iff
    {φ : Hex.Factorization} {f : Hex.ZPoly} :
    f ∈ factorizationFlattenedFactors φ ↔
      ∃ entry ∈ φ.factors.toList, entry.2 ≠ 0 ∧ entry.1 = f := by
  unfold factorizationFlattenedFactors flattenedFactorEntries
  simp only [List.mem_flatMap, List.mem_replicate]
  constructor
  · rintro ⟨entry, hentry, hne_mul, rfl⟩
    exact ⟨entry, hentry, hne_mul, rfl⟩
  · rintro ⟨entry, hentry, hne_mul, rfl⟩
    exact ⟨entry, hentry, hne_mul, rfl⟩

/--
The transport coercion of `factorizationFlattenedFactors` to a multiset
equals the issue-spec multiplicity sum over the original entry list. -/
private theorem coe_factorizationFlattenedFactors_eq
    (φ : Hex.Factorization) :
    (factorizationFlattenedFactors φ : Multiset Hex.ZPoly) =
      (φ.factors.toList.map (fun e => Multiset.replicate e.2 e.1)).sum := by
  unfold factorizationFlattenedFactors flattenedFactorEntries
  induction φ.factors.toList with
  | nil => simp
  | cons head tail ih =>
    show ((List.replicate head.2 head.1 ++
          tail.flatMap (fun e => List.replicate e.2 e.1) : List Hex.ZPoly) :
        Multiset Hex.ZPoly) =
      Multiset.replicate head.2 head.1 +
        (tail.map (fun e => Multiset.replicate e.2 e.1)).sum
    rw [← Multiset.coe_add, Multiset.coe_replicate, ih]

/--
Two irreducible executable factorizations of the same nonzero polynomial
have the same signed scalar and the same multiplicity-flattened multiset of
polynomial factors. The corrected statement compares flattened normalized
factors rather than raw `List.Perm`, since `Hex.Factorization` does not
constrain factor sign, multiplicity packing, or constant factors. The
`normalizeFactorSign` and `nonconst` hypotheses rule out the corresponding
counterexamples.
-/
theorem factor_unique
    (φ ψ : Hex.Factorization)
    (hφ_norm : ∀ entry ∈ φ.factors, Hex.normalizeFactorSign entry.1 = entry.1)
    (hψ_norm : ∀ entry ∈ ψ.factors, Hex.normalizeFactorSign entry.1 = entry.1)
    (hφ_nonconst : ∀ entry ∈ φ.factors, 0 < entry.1.degree?.getD 0)
    (hψ_nonconst : ∀ entry ∈ ψ.factors, 0 < entry.1.degree?.getD 0)
    (hφ_irr : ∀ entry ∈ φ.factors, Hex.ZPoly.Irreducible entry.1)
    (hψ_irr : ∀ entry ∈ ψ.factors, Hex.ZPoly.Irreducible entry.1)
    (hφ_prod_ne : Hex.Factorization.product φ ≠ 0)
    (hprod : Hex.Factorization.product φ = Hex.Factorization.product ψ) :
    φ.scalar = ψ.scalar ∧
      (φ.factors.toList.map (fun e => Multiset.replicate e.2 e.1)).sum =
        (ψ.factors.toList.map (fun e => Multiset.replicate e.2 e.1)).sum := by
  -- Derive flat-list properties from packed entry hypotheses.
  have hφ_flat_ne :
      ∀ f ∈ factorizationFlattenedFactors φ, f ≠ 0 := by
    intro f hf
    obtain ⟨entry, hentry, _, rfl⟩ := mem_factorizationFlattenedFactors_iff.mp hf
    exact (hφ_irr entry (Array.mem_toList_iff.mp hentry)).not_zero
  have hψ_flat_ne :
      ∀ f ∈ factorizationFlattenedFactors ψ, f ≠ 0 := by
    intro f hf
    obtain ⟨entry, hentry, _, rfl⟩ := mem_factorizationFlattenedFactors_iff.mp hf
    exact (hψ_irr entry (Array.mem_toList_iff.mp hentry)).not_zero
  have hφ_flat_irr :
      ∀ p ∈ (factorizationFlattenedFactors φ).map HexPolyZMathlib.toPolynomial,
        Irreducible p := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    obtain ⟨entry, hentry, _, rfl⟩ := mem_factorizationFlattenedFactors_iff.mp hf
    exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible entry.1).mp
      (hφ_irr entry (Array.mem_toList_iff.mp hentry))
  have hψ_flat_irr :
      ∀ p ∈ (factorizationFlattenedFactors ψ).map HexPolyZMathlib.toPolynomial,
        Irreducible p := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    obtain ⟨entry, hentry, _, rfl⟩ := mem_factorizationFlattenedFactors_iff.mp hf
    exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible entry.1).mp
      (hψ_irr entry (Array.mem_toList_iff.mp hentry))
  have hφ_flat_norm :
      ∀ p ∈ (factorizationFlattenedFactors φ).map HexPolyZMathlib.toPolynomial,
        normalize p = p := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    obtain ⟨entry, hentry, _, rfl⟩ := mem_factorizationFlattenedFactors_iff.mp hf
    have hns := hφ_norm entry (Array.mem_toList_iff.mp hentry)
    have hne := (hφ_irr entry (Array.mem_toList_iff.mp hentry)).not_zero
    exact normalize_toPolynomial_of_normalizeFactorSign_id hne hns
  have hψ_flat_norm :
      ∀ p ∈ (factorizationFlattenedFactors ψ).map HexPolyZMathlib.toPolynomial,
        normalize p = p := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    obtain ⟨entry, hentry, _, rfl⟩ := mem_factorizationFlattenedFactors_iff.mp hf
    have hns := hψ_norm entry (Array.mem_toList_iff.mp hentry)
    have hne := (hψ_irr entry (Array.mem_toList_iff.mp hentry)).not_zero
    exact normalize_toPolynomial_of_normalizeFactorSign_id hne hns
  have hφ_flat_nonconst :
      ∀ p ∈ (factorizationFlattenedFactors φ).map HexPolyZMathlib.toPolynomial,
        p.natDegree ≠ 0 := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    obtain ⟨entry, hentry, _, rfl⟩ := mem_factorizationFlattenedFactors_iff.mp hf
    rw [HexPolyMathlib.natDegree_toPolynomial entry.1]
    have h := hφ_nonconst entry (Array.mem_toList_iff.mp hentry)
    omega
  have hψ_flat_nonconst :
      ∀ p ∈ (factorizationFlattenedFactors ψ).map HexPolyZMathlib.toPolynomial,
        p.natDegree ≠ 0 := by
    intro p hp
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hp
    obtain ⟨entry, hentry, _, rfl⟩ := mem_factorizationFlattenedFactors_iff.mp hf
    rw [HexPolyMathlib.natDegree_toPolynomial entry.1]
    have h := hψ_nonconst entry (Array.mem_toList_iff.mp hentry)
    omega
  -- Transport the product equality to Polynomial ℤ.
  have hprod_poly :
      Polynomial.C φ.scalar *
          ((factorizationFlattenedFactors φ).map HexPolyZMathlib.toPolynomial).prod =
        Polynomial.C ψ.scalar *
          ((factorizationFlattenedFactors ψ).map HexPolyZMathlib.toPolynomial).prod := by
    have h := congrArg HexPolyZMathlib.toPolynomial hprod
    rw [factorizationProduct_toPolynomial, factorizationProduct_toPolynomial] at h
    exact h
  -- The transported product is nonzero, so the scalar `φ.scalar` is nonzero.
  have hφ_scalar_ne : φ.scalar ≠ 0 := by
    intro hzero
    apply hφ_prod_ne
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply]
    rw [factorizationProduct_toPolynomial, hzero, Polynomial.C_0, zero_mul,
      HexPolyZMathlib.toPolynomial_zero]
  -- Apply the polynomial UFD helper from `UFDPartition`.
  obtain ⟨hscalar, hflat_eq⟩ :=
    UFDPartition.scalar_eq_and_coe_eq_of_normalize_fixed_nonconst_irreducible_product_eq
      φ.scalar ψ.scalar
      ((factorizationFlattenedFactors φ).map HexPolyZMathlib.toPolynomial)
      ((factorizationFlattenedFactors ψ).map HexPolyZMathlib.toPolynomial)
      hφ_scalar_ne hφ_flat_irr hψ_flat_irr hφ_flat_norm hψ_flat_norm
      hφ_flat_nonconst hψ_flat_nonconst hprod_poly
  refine ⟨hscalar, ?_⟩
  -- Lift multiset equality back to `Hex.ZPoly`.
  rw [← coe_factorizationFlattenedFactors_eq, ← coe_factorizationFlattenedFactors_eq]
  -- Goal: (factorizationFlattenedFactors φ : Multiset _) = (factorizationFlattenedFactors ψ : Multiset _)
  have hcoe_map_φ :
      ((factorizationFlattenedFactors φ).map HexPolyZMathlib.toPolynomial :
          Multiset (Polynomial ℤ)) =
        ((factorizationFlattenedFactors φ : Multiset Hex.ZPoly)).map
          HexPolyZMathlib.toPolynomial := by
    simp [Multiset.map_coe]
  have hcoe_map_ψ :
      ((factorizationFlattenedFactors ψ).map HexPolyZMathlib.toPolynomial :
          Multiset (Polynomial ℤ)) =
        ((factorizationFlattenedFactors ψ : Multiset Hex.ZPoly)).map
          HexPolyZMathlib.toPolynomial := by
    simp [Multiset.map_coe]
  rw [hcoe_map_φ, hcoe_map_ψ] at hflat_eq
  exact Multiset.map_injective HexPolyZMathlib.equiv.injective hflat_eq

/--
Uniqueness specialised against the default executable factorization, so callers
only provide the competing product, irreducibility, sign-normalization, and
nonconstant-factor facts, plus that the input is nonzero. The default
factorization's own well-formedness is supplied by
`factor_irreducible_of_nonUnit` and forthcoming sibling lemmas.
-/
theorem factor_unique_of_product
    (f : Hex.ZPoly) (φ : Hex.Factorization) (hf_ne : f ≠ 0)
    (hproduct : Hex.Factorization.product φ = f)
    (hφ_norm : ∀ entry ∈ φ.factors, Hex.normalizeFactorSign entry.1 = entry.1)
    (hψ_norm : ∀ entry ∈ (Hex.factor f).factors,
      Hex.normalizeFactorSign entry.1 = entry.1)
    (hφ_nonconst : ∀ entry ∈ φ.factors, 0 < entry.1.degree?.getD 0)
    (hψ_nonconst : ∀ entry ∈ (Hex.factor f).factors,
      0 < entry.1.degree?.getD 0)
    (hirr : ∀ entry ∈ φ.factors, Hex.ZPoly.Irreducible entry.1) :
    φ.scalar = (Hex.factor f).scalar ∧
      (φ.factors.toList.map (fun e => Multiset.replicate e.2 e.1)).sum =
        ((Hex.factor f).factors.toList.map
          (fun e => Multiset.replicate e.2 e.1)).sum :=
  factor_unique φ (Hex.factor f) hφ_norm hψ_norm hφ_nonconst hψ_nonconst hirr
    (factor_irreducible_of_nonUnit f)
    (by rw [hproduct]; exact hf_ne)
    (by rw [hproduct, factor_product f])

/-! ### Mathlib-side correspondence for executable certificate factor-product equalities

These lemmas identify the executable `Hex.PrimeFactorData.factorProduct` with
the Mathlib `Polynomial.map (Int.castRingHom (ZMod p))` image of the underlying
integer polynomial and with the explicit product of recorded factor transports.
Both shapes are consumed by the integer irreducibility certificate soundness
composition.
-/

/-- Executable `FpPoly p` multiplication transports to Mathlib multiplication
through `HexBerlekampMathlib.fpPolyEquiv`. -/
theorem toMathlibPolynomial_mul {p : Nat} [Hex.ZMod64.Bounds p]
    (a b : Hex.FpPoly p) :
    HexBerlekampMathlib.toMathlibPolynomial (a * b) =
      HexBerlekampMathlib.toMathlibPolynomial a *
        HexBerlekampMathlib.toMathlibPolynomial b :=
  map_mul HexBerlekampMathlib.fpPolyEquiv a b

/-- The executable `1 : FpPoly p` transports to Mathlib's `1`. -/
theorem toMathlibPolynomial_one {p : Nat} [Hex.ZMod64.Bounds p] :
    HexBerlekampMathlib.toMathlibPolynomial (1 : Hex.FpPoly p) = 1 := by
  ext n
  rw [HexBerlekampMathlib.coeff_toMathlibPolynomial, Polynomial.coeff_one]
  show HexModArithMathlib.ZMod64.toZMod
      ((Hex.DensePoly.C (1 : Hex.ZMod64 p)).coeff n) =
    if n = 0 then 1 else 0
  rw [Hex.DensePoly.coeff_C]
  by_cases hn : n = 0
  · simp [hn, HexModArithMathlib.ZMod64.toZMod_one]
  · simp only [hn, ↓reduceIte]
    exact HexModArithMathlib.ZMod64.toZMod_zero

/-- The executable constant polynomial `DensePoly.C c` transports to Mathlib's
`Polynomial.C` of the `ZMod p` cast of `c`. -/
theorem toMathlibPolynomial_C {p : Nat} [Hex.ZMod64.Bounds p]
    (c : Hex.ZMod64 p) :
    HexBerlekampMathlib.toMathlibPolynomial (Hex.DensePoly.C c) =
      Polynomial.C (HexModArithMathlib.ZMod64.toZMod c) := by
  ext n
  rw [HexBerlekampMathlib.coeff_toMathlibPolynomial, Hex.DensePoly.coeff_C,
      Polynomial.coeff_C]
  by_cases hn : n = 0
  · simp [hn]
  · simp only [hn, ↓reduceIte]
    exact HexModArithMathlib.ZMod64.toZMod_zero

/-- Coefficientwise scaling on `FpPoly p` transports across
`HexBerlekampMathlib.toMathlibPolynomial` to multiplication by the
corresponding `Polynomial.C` of the `ZMod p` cast. -/
theorem toMathlibPolynomial_scale {p : Nat} [Hex.ZMod64.Bounds p]
    (c : Hex.ZMod64 p) (f : Hex.FpPoly p) :
    HexBerlekampMathlib.toMathlibPolynomial (Hex.DensePoly.scale c f) =
      Polynomial.C (HexModArithMathlib.ZMod64.toZMod c) *
        HexBerlekampMathlib.toMathlibPolynomial f := by
  ext n
  rw [HexBerlekampMathlib.coeff_toMathlibPolynomial,
      Polynomial.coeff_C_mul, HexBerlekampMathlib.coeff_toMathlibPolynomial]
  have hzero : c * (Zero.zero : Hex.ZMod64 p) = (Zero.zero : Hex.ZMod64 p) := by
    show c * (0 : Hex.ZMod64 p) = (0 : Hex.ZMod64 p)
    grind
  rw [Hex.DensePoly.coeff_scale c f n hzero]
  exact HexModArithMathlib.ZMod64.toZMod_mul c (f.coeff n)

/--
List `foldl (· * ·)` of executable `FpPoly p` factors transports across
`HexBerlekampMathlib.toMathlibPolynomial` to the explicit Mathlib `List.prod`
of the per-factor transports.
-/
theorem toMathlibPolynomial_listFoldlMul_one {p : Nat} [Hex.ZMod64.Bounds p]
    (xs : List (Hex.FpPoly p)) :
    HexBerlekampMathlib.toMathlibPolynomial (xs.foldl (· * ·) 1) =
      (xs.map HexBerlekampMathlib.toMathlibPolynomial).prod := by
  suffices h : ∀ (acc : Hex.FpPoly p),
      HexBerlekampMathlib.toMathlibPolynomial (xs.foldl (· * ·) acc) =
        HexBerlekampMathlib.toMathlibPolynomial acc *
          (xs.map HexBerlekampMathlib.toMathlibPolynomial).prod by
    have hh := h 1
    rw [toMathlibPolynomial_one] at hh
    simpa using hh
  intro acc
  induction xs generalizing acc with
  | nil => simp
  | cons head tail ih =>
      rw [List.foldl_cons, ih (acc * head), List.map_cons, List.prod_cons,
        toMathlibPolynomial_mul]
      ring

/--
The Mathlib transport of `Hex.PrimeFactorData.factorProduct` is the Mathlib
`List.prod` of the recorded factor transports.
-/
theorem toMathlibPolynomial_factorProduct (primeData : Hex.PrimeFactorData) :
    letI := primeData.bounds
    HexBerlekampMathlib.toMathlibPolynomial primeData.factorProduct =
      (primeData.factorPolys.toList.map
        HexBerlekampMathlib.toMathlibPolynomial).prod := by
  letI := primeData.bounds
  show HexBerlekampMathlib.toMathlibPolynomial
      (primeData.factorPolys.foldl (· * ·) 1) = _
  rw [← Array.foldl_toList]
  exact toMathlibPolynomial_listFoldlMul_one _

/--
Coefficientwise reduction `Hex.ZPoly.modP` transports to Mathlib's coefficient
map from `ℤ[X]` to `(ZMod p)[X]`. Mirrors `IntReductionMod` with the same
underlying primitive, exposed in `Basic.lean` so that downstream certificate
soundness proofs do not need to depend on the small-mod singleton branch.
-/
theorem toMathlibPolynomial_modP_eq_map_intCast_zmod
    {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.ZPoly) :
    HexBerlekampMathlib.toMathlibPolynomial (Hex.ZPoly.modP p f) =
      (HexPolyZMathlib.toPolynomial f).map (Int.castRingHom (ZMod p)) :=
  HexPolyZMathlib.eq_map_intCast_of_coeff_eq_toZMod_modP p f
    (fun n => HexBerlekampMathlib.coeff_toMathlibPolynomial _ n)

/--
A successful `PrimeFactorData.checkForPolynomial` block exposes the Mathlib
factor-product / modular-image alignment: the Mathlib transport of the
recorded `factorProduct` equals the Mathlib `Polynomial.map (Int.castRingHom (ZMod p))`
image of the underlying integer polynomial.
-/
theorem toMathlibPolynomial_factorProduct_eq_map_intCast_zmod
    (f : Hex.ZPoly) (primeData : Hex.PrimeFactorData)
    (hcheck : primeData.checkForPolynomial f = true) :
    letI := primeData.bounds
    HexBerlekampMathlib.toMathlibPolynomial primeData.factorProduct =
      (HexPolyZMathlib.toPolynomial f).map
        (Int.castRingHom (ZMod primeData.p)) := by
  letI := primeData.bounds
  have hprod : primeData.factorProduct = Hex.ZPoly.modP primeData.p f := by
    simp [Hex.PrimeFactorData.checkForPolynomial] at hcheck
    exact hcheck.1.2
  rw [hprod]
  exact toMathlibPolynomial_modP_eq_map_intCast_zmod f

/--
A successful `PrimeFactorData.checkForPolynomial` block exposes the Mathlib
modular image of the underlying integer polynomial as the explicit product of
recorded factor transports.

This is the shape used by the integer irreducibility certificate soundness
composition: the Mathlib `(toPolynomial f).map (Int.castRingHom (ZMod p))`
factors through the explicit Mathlib `List.prod` of executable monic factor
transports, enabling UFD-level identification of factor degrees against
`factorDegrees`.
-/
theorem map_intCast_zmod_toPolynomial_eq_factorPolys_product
    (f : Hex.ZPoly) (primeData : Hex.PrimeFactorData)
    (hcheck : primeData.checkForPolynomial f = true) :
    letI := primeData.bounds
    (HexPolyZMathlib.toPolynomial f).map
        (Int.castRingHom (ZMod primeData.p)) =
      (primeData.factorPolys.toList.map
        HexBerlekampMathlib.toMathlibPolynomial).prod := by
  letI := primeData.bounds
  rw [← toMathlibPolynomial_factorProduct_eq_map_intCast_zmod f primeData hcheck]
  exact toMathlibPolynomial_factorProduct primeData

/--
`hasSubsetDegreeAux` is the recursive subset-sum check used by
`Hex.PrimeFactorData.hasSubsetDegree`. If some sub-multiset of `L` sums to
`target`, the recursive procedure detects it.
-/
private theorem hasSubsetDegreeAux_eq_true_of_exists_subMultiset
    {L : List Nat} {target : Nat}
    {S : Multiset Nat} (hS : S ≤ (L : Multiset Nat)) (hsum : S.sum = target) :
    Hex.PrimeFactorData.hasSubsetDegreeAux L target = true := by
  induction L generalizing target S with
  | nil =>
    have hS_zero : S = 0 := by
      have : S ≤ 0 := by simpa using hS
      exact Multiset.le_zero.mp this
    rw [hS_zero] at hsum
    simp [Hex.PrimeFactorData.hasSubsetDegreeAux, ← hsum]
  | cons d L ih =>
    rw [← Multiset.cons_coe] at hS
    by_cases hd_mem : d ∈ S
    · -- d ∈ S; remove it and recurse on (target - d)
      have hd_le_target : d ≤ target := by
        rw [← hsum]
        exact Multiset.single_le_sum (fun _ _ => Nat.zero_le _) d hd_mem
      have hS_eq : S = d ::ₘ S.erase d := (Multiset.cons_erase hd_mem).symm
      have hT_le_L : S.erase d ≤ (L : Multiset Nat) := by
        have herase : S.erase d ≤ (d ::ₘ (L : Multiset Nat)).erase d :=
          Multiset.erase_le_erase d hS
        rwa [Multiset.erase_cons_head] at herase
      have hT_sum : (S.erase d).sum = target - d := by
        have hsum' : (d ::ₘ S.erase d).sum = target := hS_eq ▸ hsum
        rw [Multiset.sum_cons] at hsum'
        omega
      have hrec := ih (S := S.erase d) hT_le_L hT_sum
      simp [Hex.PrimeFactorData.hasSubsetDegreeAux, hd_le_target, hrec]
    · -- d ∉ S; reduce to L
      have hS_le_L : S ≤ (L : Multiset Nat) := (Multiset.le_cons_of_notMem hd_mem).mp hS
      have hrec := ih (S := S) hS_le_L hsum
      simp [Hex.PrimeFactorData.hasSubsetDegreeAux, hrec]

/-- Helper: extract `checkCertAtFactor` at a specific index from `checkFactorCerts`. -/
private theorem checkCertAtFactor_of_checkFactorCerts
    (primeData : Hex.PrimeFactorData)
    (hcheck : primeData.checkFactorCerts = true)
    (i : Nat) (hi_deg : i < primeData.factorDegrees.size)
    (hi_polys : i < primeData.factorPolys.size)
    (hi_certs : i < primeData.factorCerts.size) :
    Hex.PrimeFactorData.checkCertAtFactor primeData
      primeData.factorDegrees[i] primeData.factorPolys[i] primeData.factorCerts[i] = true := by
  simp only [Hex.PrimeFactorData.checkFactorCerts, Bool.and_eq_true, beq_iff_eq,
    List.all_eq_true] at hcheck
  obtain ⟨_, hall⟩ := hcheck
  have hmem :
      (primeData.factorDegrees[i],
        (primeData.factorPolys[i], primeData.factorCerts[i])) ∈
      primeData.factorDegrees.toList.zip
        (primeData.factorPolys.toList.zip primeData.factorCerts.toList) := by
    rw [List.mem_iff_getElem]
    refine ⟨i, ?_, ?_⟩
    · simp only [List.length_zip, Array.length_toList]
      omega
    · simp only [List.getElem_zip, Array.getElem_toList]
  exact hall _ hmem

/--
The Mathlib transport of an executable monic factor recorded in a
`PrimeFactorData` block has natural degree equal to the recorded factor
degree. Uses the executable `degree?` slot, the recorded monicity, and the
Mathlib basisSize identification.
-/
private theorem natDegree_toMathlibPolynomial_factorPolys_eq
    (primeData : Hex.PrimeFactorData)
    (hcheck : primeData.checkFactorCerts = true)
    (i : Nat) (hi_polys : i < primeData.factorPolys.size)
    (hi_deg : i < primeData.factorDegrees.size)
    (hi_certs : i < primeData.factorCerts.size) :
    letI := primeData.bounds
    (HexBerlekampMathlib.toMathlibPolynomial primeData.factorPolys[i]).natDegree =
      primeData.factorDegrees[i] := by
  letI := primeData.bounds
  have hpair :=
    checkCertAtFactor_of_checkFactorCerts primeData hcheck i hi_deg hi_polys hi_certs
  -- factor.leadingCoeff = 1, factor.degree? = some primeData.factorDegrees[i]
  have hmonic : Hex.DensePoly.Monic primeData.factorPolys[i] := by
    by_cases hmon : primeData.factorPolys[i].leadingCoeff = 1
    · exact hmon
    · exfalso
      simp [Hex.PrimeFactorData.checkCertAtFactor, hmon] at hpair
  have hdegree :
      primeData.factorPolys[i].degree? = some primeData.factorDegrees[i] := by
    simp only [Hex.PrimeFactorData.checkCertAtFactor, Bool.and_eq_true, beq_iff_eq,
      decide_eq_true_eq] at hpair
    exact hpair.1.2
  rw [HexBerlekampMathlib.natDegree_toMathlibPolynomial_eq_basisSize _ hmonic]
  show primeData.factorPolys[i].degree?.getD 0 = _
  rw [hdegree]
  rfl

/--
The executable integer-polynomial irreducibility checker is sound after
transport to Mathlib's polynomial model, under the standard certificate
side-conditions: each per-prime block uses a prime modulus, the input is
primitive, and the input is non-constant. Primality is needed for Rabin
irreducibility lifting and `(ZMod p)[X]` UFD reasoning; primitivity and
non-constancy rule out trivially reducible inputs whose recorded obstructions
would otherwise be vacuous.
-/
theorem checkIrreducibleCert_sound
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : ∀ primeData ∈ cert.perPrime.toList, Nat.Prime primeData.p)
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive)
    (hpos : 0 < (HexPolyZMathlib.toPolynomial f).natDegree) :
    Hex.checkIrreducibleCert f cert = true →
      Irreducible (HexPolyZMathlib.toPolynomial f) := by
  intro hcert
  set F := HexPolyZMathlib.toPolynomial f with hF_def
  have hF_ne : F ≠ 0 := fun h => by
    rw [h, Polynomial.natDegree_zero] at hpos; exact absurd hpos (lt_irrefl 0)
  refine ⟨?_, ?_⟩
  · intro hunit
    have := Polynomial.natDegree_eq_zero_of_isUnit hunit
    omega
  · intro a b hab
    by_contra hcontra
    push Not at hcontra
    obtain ⟨ha_not_unit, hb_not_unit⟩ := hcontra
    have ha_ne : a ≠ 0 := fun h => hF_ne (by rw [hab, h, zero_mul])
    have hb_ne : b ≠ 0 := fun h => hF_ne (by rw [hab, h, mul_zero])
    have ha_dvd : a ∣ F := ⟨b, hab⟩
    have hb_dvd : b ∣ F := ⟨a, by rw [hab]; ring⟩
    have ha_prim : a.IsPrimitive := isPrimitive_of_dvd hprim ha_dvd
    have hb_prim : b.IsPrimitive := isPrimitive_of_dvd hprim hb_dvd
    have hdegSum : a.natDegree + b.natDegree = F.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha_ne hb_ne]
    -- Helper: from a non-unit primitive divisor with positive natDegree, contradict.
    have hcontradict :
        ∀ (c d : Polynomial ℤ), c * d = F → c ≠ 0 → d ≠ 0 →
          c.IsPrimitive → ¬ IsUnit c →
          c.natDegree ≤ d.natDegree → False := by
      intro c d hcd_eq hc_ne hd_ne hc_prim hc_not_unit hcd_le
      -- c has positive natDegree (non-unit primitive)
      have hc_natDeg_pos : 0 < c.natDegree := by
        rcases Nat.eq_zero_or_pos c.natDegree with hzero | hposc
        · exfalso
          have hc_const : c = Polynomial.C (c.coeff 0) :=
            Polynomial.eq_C_of_natDegree_eq_zero hzero
          have hc_coeff_unit : IsUnit (c.coeff 0) := by
            apply hc_prim
            rw [← hc_const]
          rw [hc_const] at hc_not_unit
          exact hc_not_unit (Polynomial.isUnit_C.mpr hc_coeff_unit)
        · exact hposc
      -- natDegree c ≤ F.natDegree / 2
      have hcd_sum : c.natDegree + d.natDegree = F.natDegree := by
        rw [← hcd_eq, Polynomial.natDegree_mul hc_ne hd_ne]
      have hc_le_half : c.natDegree ≤ F.natDegree / 2 := by omega
      -- c.natDegree ∈ candidateFactorDegrees f
      have hF_natDeg : F.natDegree = f.degree?.getD 0 :=
        HexPolyMathlib.natDegree_toPolynomial f
      have htarget_mem :
          c.natDegree ∈ Hex.ZPolyIrreducibilityCertificate.candidateFactorDegrees f := by
        unfold Hex.ZPolyIrreducibilityCertificate.candidateFactorDegrees
        rw [List.mem_map]
        refine ⟨c.natDegree - 1, ?_, ?_⟩
        · rw [List.mem_range, ← hF_natDeg]
          omega
        · omega
      -- Extract obstruction → primeData with hasSubsetDegree false
      have hobsFor :=
        Hex.checkIrreducibleCert_obstructs_candidate_degrees f cert hcert _ htarget_mem
      simp only [Hex.ZPolyIrreducibilityCertificate.hasObstructionFor, List.any_eq_true,
        Bool.and_eq_true, beq_iff_eq] at hobsFor
      obtain ⟨obs, _, ⟨hobs_target_eq, hobs_valid⟩⟩ := hobsFor
      -- Get the primeData referenced by this obstruction
      have hobs_primeIndex :
          ∃ primeData : Hex.PrimeFactorData,
            cert.primeDataAt? obs.primeIndex = some primeData := by
        simp only [Hex.DegreeObstruction.checkForCertificate, Bool.and_eq_true,
          decide_eq_true_eq] at hobs_valid
        rcases hpa : cert.primeDataAt? obs.primeIndex with _ | primeData
        · simp [hpa] at hobs_valid
        · exact ⟨primeData, rfl⟩
      obtain ⟨primeData, hpa⟩ := hobs_primeIndex
      have hno_subset :
          primeData.hasSubsetDegree obs.targetDegree = false :=
        Hex.degreeObstruction_no_subset_degree f cert obs primeData hobs_valid hpa
      -- primeData is in cert.perPrime.toList
      have hpd_mem : primeData ∈ cert.perPrime.toList := by
        have hpa' := hpa
        unfold Hex.ZPolyIrreducibilityCertificate.primeDataAt? at hpa'
        rcases hdrop : cert.perPrime.toList.drop obs.primeIndex with _ | ⟨head, tail⟩
        · rw [hdrop] at hpa'; simp at hpa'
        · rw [hdrop] at hpa'
          rw [Option.some.injEq] at hpa'
          have hmem_drop : head ∈ cert.perPrime.toList.drop obs.primeIndex := by
            rw [hdrop]; exact List.mem_cons_self
          rw [← hpa']
          exact List.mem_of_mem_drop hmem_drop
      -- Extract `Nat.Prime primeData.p` from hypothesis
      have hp_prime : Nat.Prime primeData.p := hprime primeData hpd_mem
      haveI : Fact (Nat.Prime primeData.p) := ⟨hp_prime⟩
      letI := primeData.bounds
      -- Extract checkForPolynomial fact
      have hcheckPoly := Hex.checkIrreducibleCert_prime_data f cert hcert primeData hpd_mem
      have hgood := Hex.checkIrreducibleCert_isGoodPrime f cert hcert primeData hpd_mem
      have hfacts_align :=
        Hex.checkIrreducibleCert_certificate_alignment f cert hcert primeData hpd_mem
      -- leading coefficient ≠ 0 mod p (from isGoodPrime)
      have hlc_modP_ne : Hex.ZPoly.leadingCoeffModP f primeData.p ≠ 0 := by
        have := Hex.isGoodPrime_leadingCoeffAdmissible f primeData.p hgood
        unfold Hex.leadingCoeffAdmissible at this
        exact this
      -- Identify `(Int.castRingHom (ZMod p)) F.leadingCoeff = toZMod (leadingCoeffModP f p)`
      have hF_lc_eq :
          (Int.castRingHom (ZMod primeData.p)) F.leadingCoeff =
            HexModArithMathlib.ZMod64.toZMod (Hex.ZPoly.leadingCoeffModP f primeData.p) := by
        rw [HexPolyMathlib.leadingCoeff_toPolynomial]
        show ((Hex.DensePoly.leadingCoeff f : ℤ) : ZMod primeData.p) = _
        rw [← HexPolyZMathlib.toZMod_ZMod64_ofNat_intModNat_eq_intCast primeData.p
              (Hex.DensePoly.leadingCoeff f)]
        rfl
      have hF_lc_map_ne :
          (Int.castRingHom (ZMod primeData.p)) F.leadingCoeff ≠ 0 := by
        rw [hF_lc_eq]
        intro heq
        apply hlc_modP_ne
        have hinj := (HexModArithMathlib.ZMod64.equiv (p := primeData.p)).injective
        apply hinj
        simpa using heq.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
      -- F.leadingCoeff = a.leadingCoeff * b.leadingCoeff (over Z, integral domain)
      have hlc_F : F.leadingCoeff = a.leadingCoeff * b.leadingCoeff := by
        rw [hab, Polynomial.leadingCoeff_mul]
      -- Then c.leadingCoeff mod p ≠ 0 (using p prime → ZMod p domain)
      have hc_lc_map_ne :
          (Int.castRingHom (ZMod primeData.p)) c.leadingCoeff ≠ 0 := by
        haveI : IsDomain (ZMod primeData.p) := inferInstance
        intro heq
        apply hF_lc_map_ne
        have : F.leadingCoeff = c.leadingCoeff * d.leadingCoeff := by
          rw [← hcd_eq, Polynomial.leadingCoeff_mul]
        rw [this, map_mul, heq, zero_mul]
      -- natDegree c is preserved mod p
      have hc_natDeg_modP :
          (c.map (Int.castRingHom (ZMod primeData.p))).natDegree = c.natDegree :=
        Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hc_lc_map_ne
      -- c divides F, so (c mod p) divides (F mod p)
      have hc_modP_dvd_F_modP :
          c.map (Int.castRingHom (ZMod primeData.p)) ∣
            F.map (Int.castRingHom (ZMod primeData.p)) := by
        refine ⟨d.map (Int.castRingHom (ZMod primeData.p)), ?_⟩
        rw [← Polynomial.map_mul, hcd_eq]
      -- (F mod p) = (factorPolys list).prod
      have hF_modP_eq :=
        map_intCast_zmod_toPolynomial_eq_factorPolys_product f primeData hcheckPoly
      rw [hF_modP_eq] at hc_modP_dvd_F_modP
      -- Construct Hex.ZMod64.PrimeModulus from Mathlib primality
      haveI hpm : Hex.ZMod64.PrimeModulus primeData.p :=
        Hex.ZMod64.primeModulusOfPrime
          ⟨hp_prime.two_le, fun m hdvd => hp_prime.eq_one_or_self_of_dvd m hdvd⟩
      -- Each factor in factorPolys is irreducible (via Rabin)
      have hfactor_irr :
          ∀ q ∈ (primeData.factorPolys.toList.map
                  HexBerlekampMathlib.toMathlibPolynomial),
            Irreducible q := by
        intro q hq
        rw [List.mem_map] at hq
        obtain ⟨factor, hfactor_mem, rfl⟩ := hq
        rw [List.mem_iff_getElem] at hfactor_mem
        obtain ⟨i, hi, hfactor_eq⟩ := hfactor_mem
        have hi_polys : i < primeData.factorPolys.size := by simpa using hi
        have hfactor_eq' : primeData.factorPolys[i] = factor := by
          rw [← hfactor_eq]; simp
        have hsizes :
            primeData.factorDegrees.size = primeData.factorCerts.size ∧
              primeData.factorDegrees.size = primeData.factorPolys.size := by
          simp only [Hex.PrimeFactorData.checkFactorCerts, Bool.and_eq_true, beq_iff_eq]
            at hfacts_align
          exact hfacts_align.1
        have hi_deg : i < primeData.factorDegrees.size := by
          rw [hsizes.2]; exact hi_polys
        have hi_cert : i < primeData.factorCerts.size := by
          rw [hsizes.1] at hi_deg; exact hi_deg
        have hpair :=
          checkCertAtFactor_of_checkFactorCerts primeData hfacts_align i
            hi_deg hi_polys hi_cert
        -- factor is monic; extract Rabin cert acceptance
        have hmonic : Hex.DensePoly.Monic primeData.factorPolys[i] := by
          by_cases hmon : primeData.factorPolys[i].leadingCoeff = 1
          · exact hmon
          · exfalso; simp [Hex.PrimeFactorData.checkCertAtFactor, hmon] at hpair
        have hcheck : Hex.Berlekamp.checkIrreducibilityCertificate
            primeData.factorPolys[i] hmonic primeData.factorCerts[i] = true := by
          have hp := hpair
          simp only [Hex.PrimeFactorData.checkCertAtFactor, Bool.and_eq_true] at hp
          obtain ⟨_, hif⟩ := hp
          have hmonic' : Hex.DensePoly.leadingCoeff primeData.factorPolys[i] = 1 := hmonic
          rw [dif_pos hmonic'] at hif
          exact hif
        have hrabin :=
          Hex.Berlekamp.checkIrreducibilityCertificate_rabinTest
            (p := primeData.p) primeData.factorPolys[i] hmonic _ hcheck
        rw [← hfactor_eq']
        exact HexBerlekampMathlib.rabinTest_true_irreducible _ hmonic hrabin
      -- Apply UFD subset-degree lemma to (c mod p)
      have hc_modP_ne :
          c.map (Int.castRingHom (ZMod primeData.p)) ≠ 0 := by
        intro hzero
        apply hc_lc_map_ne
        have hlc_eq : (c.map (Int.castRingHom (ZMod primeData.p))).leadingCoeff = 0 := by
          rw [hzero, Polynomial.leadingCoeff_zero]
        rw [Polynomial.leadingCoeff, Polynomial.coeff_map] at hlc_eq
        rw [hc_natDeg_modP] at hlc_eq
        exact hlc_eq
      -- Restate the divisibility with Multiset for the UFD lemma
      have hc_modP_dvd_prod :
          c.map (Int.castRingHom (ZMod primeData.p)) ∣
            (↑(primeData.factorPolys.toList.map
                HexBerlekampMathlib.toMathlibPolynomial) : Multiset (Polynomial (ZMod primeData.p))).prod := by
        rw [Multiset.prod_coe]
        exact hc_modP_dvd_F_modP
      have hfactor_irr_ms :
          ∀ q ∈ (↑(primeData.factorPolys.toList.map
                  HexBerlekampMathlib.toMathlibPolynomial) :
              Multiset (Polynomial (ZMod primeData.p))),
            Irreducible q := by
        intro q hq
        rw [Multiset.mem_coe] at hq
        exact hfactor_irr q hq
      obtain ⟨S, hS_le, hS_sum⟩ :=
        UFDPartition.natDegree_eq_sum_subset_of_dvd_prod_irreducibles
          hc_modP_ne hfactor_irr_ms hc_modP_dvd_prod
      -- The subset sum equals natDegree (c mod p) = natDegree c
      have hS_sum' : S.sum = c.natDegree := by
        rw [← hS_sum]; exact hc_natDeg_modP
      -- The "degrees of factor polys" equal `factorDegrees`
      have hsizes :
          primeData.factorDegrees.size = primeData.factorCerts.size ∧
            primeData.factorDegrees.size = primeData.factorPolys.size := by
        simp only [Hex.PrimeFactorData.checkFactorCerts, Bool.and_eq_true, beq_iff_eq]
          at hfacts_align
        exact hfacts_align.1
      have hmap_eq :
          (primeData.factorPolys.toList.map
              HexBerlekampMathlib.toMathlibPolynomial).map Polynomial.natDegree =
            primeData.factorDegrees.toList := by
        rw [List.map_map]
        apply List.ext_getElem
        · simp only [List.length_map, Array.length_toList]
          omega
        · intro i hi₁ hi₂
          simp only [List.length_map, Array.length_toList] at hi₁ hi₂
          have hi_polys : i < primeData.factorPolys.size := by simpa using hi₁
          have hi_deg : i < primeData.factorDegrees.size := by rw [hsizes.2]; exact hi_polys
          have hi_cert : i < primeData.factorCerts.size := by rw [hsizes.1] at hi_deg; exact hi_deg
          rw [List.getElem_map]
          simp only [Function.comp]
          show (HexBerlekampMathlib.toMathlibPolynomial
            primeData.factorPolys.toList[i]).natDegree = _
          rw [Array.getElem_toList]
          have := natDegree_toMathlibPolynomial_factorPolys_eq primeData hfacts_align i
            hi_polys hi_deg hi_cert
          rw [this]
          rw [Array.getElem_toList]
      have hS_le' : S ≤ (primeData.factorDegrees.toList : Multiset Nat) := by
        have hmapcoe :
            Multiset.map Polynomial.natDegree
              (↑(primeData.factorPolys.toList.map
                HexBerlekampMathlib.toMathlibPolynomial) :
              Multiset (Polynomial (ZMod primeData.p))) =
            ↑(List.map Polynomial.natDegree
              (List.map HexBerlekampMathlib.toMathlibPolynomial
                primeData.factorPolys.toList)) :=
          Multiset.map_coe _ _
        rw [hmapcoe] at hS_le
        rw [hmap_eq] at hS_le
        exact hS_le
      -- Apply subset-sum spec
      have hsubsetTrue := hasSubsetDegreeAux_eq_true_of_exists_subMultiset hS_le' hS_sum'
      -- This contradicts hasSubsetDegree = false
      have hsubsetEq : primeData.hasSubsetDegree c.natDegree = true := hsubsetTrue
      rw [hobs_target_eq] at hno_subset
      rw [hsubsetEq] at hno_subset
      exact absurd hno_subset (by decide)
    -- Apply to either (a, b) or (b, a) based on which has smaller natDegree
    rcases le_or_gt a.natDegree b.natDegree with hle | hgt
    · exact hcontradict a b hab.symm ha_ne hb_ne ha_prim ha_not_unit hle
    · exact hcontradict b a (by rw [hab]; ring) hb_ne ha_ne hb_prim hb_not_unit (le_of_lt hgt)

/--
The executable integer-polynomial irreducibility checker is sound for the
Mathlib-free irreducibility predicate as well.
-/
theorem checkIrreducibleCert_sound_zpoly
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : ∀ primeData ∈ cert.perPrime.toList, Nat.Prime primeData.p)
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive)
    (hpos : 0 < (HexPolyZMathlib.toPolynomial f).natDegree) :
    Hex.checkIrreducibleCert f cert = true → Hex.ZPoly.Irreducible f := by
  intro hcert
  exact
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).mpr
      (checkIrreducibleCert_sound f cert hprime hprim hpos hcert)

/-- Index type for the modular factors stored in executable prime-choice data. -/
abbrev ModPFactorIndex (primeData : Hex.PrimeChoiceData) : Type :=
  Fin primeData.factorsModP.size

/-- A finite subset of the modular factors stored in executable prime-choice data. -/
abbrev ModPFactorSubset (primeData : Hex.PrimeChoiceData) : Type :=
  Finset (ModPFactorIndex primeData)

/-- The selected modular factor at an executable `PrimeChoiceData` index. -/
def modPFactor (primeData : Hex.PrimeChoiceData)
    (i : ModPFactorIndex primeData) : @Hex.FpPoly primeData.p primeData.bounds :=
  primeData.factorsModP[i]

/-- Product of the selected modular factors. -/
def modPFactorProduct
    (primeData : Hex.PrimeChoiceData) (S : ModPFactorSubset primeData) :
    @Hex.FpPoly primeData.p primeData.bounds :=
  letI := primeData.bounds
  S.toList.foldl (fun acc i => acc * modPFactor primeData i) 1

/--
Identify the executable modular subset product with a Mathlib `Finset.prod`.

The executable surface stores subset products as a left fold over
`Finset.toList`; after transporting each `FpPoly` to Mathlib, commutativity
identifies that fold with the canonical finite-set product.
-/
theorem toMathlibPolynomial_modPFactorProduct
    (primeData : Hex.PrimeChoiceData) (S : ModPFactorSubset primeData) :
    letI := primeData.bounds
    HexBerlekampMathlib.toMathlibPolynomial (modPFactorProduct primeData S) =
      ∏ i ∈ S,
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) := by
  letI := primeData.bounds
  unfold modPFactorProduct
  rw [show
      (S.toList.foldl (fun acc i => acc * modPFactor primeData i)
          (1 : @Hex.FpPoly primeData.p primeData.bounds)) =
        (S.toList.map (modPFactor primeData)).foldl (· * ·) 1 from by
    rw [List.foldl_map]]
  rw [toMathlibPolynomial_listFoldlMul_one, List.map_map]
  exact Finset.prod_map_toList S
    (fun i => HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i))

/--
The monic modular image used for subset partition statements. This mirrors the
executable prime-choice normalization: zero stays zero, and nonzero inputs are
scaled by the inverse of their leading coefficient.
-/
def monicModPImage {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.FpPoly p) : Hex.FpPoly p :=
  if f.isZero then
    0
  else
    Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)⁻¹ f

theorem monicModPImage_eq_monicModularImage
    {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.FpPoly p) :
    monicModPImage f = Hex.monicModularImage f := by
  rfl

/-- For a nonzero `Hex.FpPoly p`, `Hex.monicModularImage` is exactly the
leading-coefficient inverse scaling of the input. This records the direct
`if f.isZero then 0 else scale (lc f)⁻¹ f` branch of the definition, avoiding
repeated local `unfold Hex.monicModularImage; simp [hf]` derivations at the
call sites that need this equation. -/
private theorem monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false
    {p : Nat} [Hex.ZMod64.Bounds p] {f : Hex.FpPoly p}
    (hf : f.isZero = false) :
    Hex.monicModularImage f =
        Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)⁻¹ f := by
  unfold Hex.monicModularImage
  simp [hf]

theorem monicModPImage_zero {p : Nat} [Hex.ZMod64.Bounds p] :
    @monicModPImage p _ 0 = 0 := by
  rfl

theorem monicModPImage_ne_zero_of_ne_zero
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Hex.Nat.Prime p)]
    {f : Hex.FpPoly p} (hf : f.isZero = false) :
    monicModPImage f ≠ 0 := by
  rw [monicModPImage_eq_monicModularImage]
  have hf_ne : f ≠ 0 := by
    intro hzero
    subst hzero
    contradiction
  exact Hex.monicModularImage_ne_zero_of_ne_zero (Fact.out : Hex.Nat.Prime p) hf_ne

theorem monicModPImage_monic_of_ne_zero
    {p : Nat} [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p) {f : Hex.FpPoly p} (hf : f.isZero = false) :
    Hex.DensePoly.Monic (monicModPImage f) := by
  rw [monicModPImage_eq_monicModularImage]
  exact Hex.monicModularImage_monic hprime f hf

/-- Nonvanishing of the leading coefficient for a positive-size
`Hex.FpPoly p`. Composes `Hex.FpPoly.leadingCoeff_eq_coeff_pred`, which
rewrites the leading coefficient to `f.coeff (f.size - 1)`, with
`Hex.DensePoly.coeff_last_ne_zero_of_pos_size`, the invariant that the
size-pred coefficient of a positive-size `Hex.DensePoly` is nonzero. -/
theorem fpPoly_leadingCoeff_ne_zero_of_size_pos
    {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.FpPoly p)
    (hf_size_pos : 0 < f.size) :
    Hex.DensePoly.leadingCoeff f ≠ (0 : Hex.ZMod64 p) := by
  rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred f hf_size_pos]
  exact Hex.DensePoly.coeff_last_ne_zero_of_pos_size f hf_size_pos

/-- For a nonzero `Hex.FpPoly p`, the monic modular image divides the input.
This packages the nonzero branch of `Hex.monicModularImage`: the branch scales
by the inverse of a nonzero leading coefficient, and unit-scaling preserves
divisibility back to the original polynomial. -/
private theorem monicModularImage_dvd_self_of_isZero_false
    {p : Nat} [Hex.ZMod64.Bounds p] (hprime : Hex.Nat.Prime p)
    {f : Hex.FpPoly p} (hf : f.isZero = false) :
    Hex.monicModularImage f ∣ f := by
  letI : Hex.ZMod64.PrimeModulus p := Hex.ZMod64.primeModulusOfPrime hprime
  have hsize_pos : 0 < f.size :=
    (Hex.DensePoly.isZero_eq_false_iff _).mp hf
  have hlead_ne :
      Hex.DensePoly.leadingCoeff f ≠ (0 : Hex.ZMod64 p) :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos f hsize_pos
  have hinv_ne :
      (Hex.DensePoly.leadingCoeff f)⁻¹ ≠ (0 : Hex.ZMod64 p) :=
    Hex.ZMod64.inv_ne_zero_of_prime hprime hlead_ne
  rw [monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hf]
  exact Hex.FpPoly.dvd_scale_self_of_ne_zero hinv_ne f

theorem monicModPImage_dvd_self_of_ne_zero
    {p : Nat} [Hex.ZMod64.Bounds p]
    (hprime : Hex.Nat.Prime p) {f : Hex.FpPoly p} (hf : f.isZero = false) :
    monicModPImage f ∣ f := by
  letI : Hex.ZMod64.PrimeModulus p := Hex.ZMod64.primeModulusOfPrime hprime
  unfold monicModPImage
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  have hf_ne : f ≠ 0 := by
    intro hzero
    subst hzero
    contradiction
  have hf_size_pos : 0 < f.size := Hex.FpPoly.size_pos_of_ne_zero hf_ne
  have hlead_ne : Hex.DensePoly.leadingCoeff f ≠ (0 : Hex.ZMod64 p) :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos f hf_size_pos
  have hinv_ne : (Hex.DensePoly.leadingCoeff f)⁻¹ ≠ (0 : Hex.ZMod64 p) :=
    Hex.ZMod64.inv_ne_zero_of_prime hprime hlead_ne
  exact Hex.FpPoly.dvd_scale_self_of_ne_zero hinv_ne f

theorem dvd_monicModPImage_of_dvd
    {p : Nat} [Hex.ZMod64.Bounds p]
    (_hprime : Hex.Nat.Prime p) {f : Hex.FpPoly p}
    (hf : f.isZero = false) :
    f ∣ monicModPImage f := by
  unfold monicModPImage
  simp only [hf, Bool.false_eq_true, ↓reduceIte]
  refine ⟨Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹, ?_⟩
  calc
    Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)⁻¹ f
        = Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹ * f := by
          rw [Hex.FpPoly.C_mul_eq_scale]
    _ = f * Hex.DensePoly.C (Hex.DensePoly.leadingCoeff f)⁻¹ :=
          Hex.DensePoly.mul_comm_poly _ _

theorem modP_mul
    (p : Nat) [Hex.ZMod64.Bounds p] (f g : Hex.ZPoly) :
    Hex.ZPoly.modP p (f * g) = Hex.ZPoly.modP p f * Hex.ZPoly.modP p g := by
  have hprod :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f * Hex.ZPoly.modP p g))
        (f * g) p := by
    exact Hex.ZPoly.congr_trans
      (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f * Hex.ZPoly.modP p g))
      (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f) * Hex.FpPoly.liftToZ (Hex.ZPoly.modP p g))
      (f * g) p
      (Hex.ZPoly.liftToZ_mul_congr p (Hex.ZPoly.modP p f) (Hex.ZPoly.modP p g))
      (Hex.ZPoly.congr_mul
        (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f))
        (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p g))
        f g p
        (Hex.FpPoly.congr_liftToZ_modP (p := p) f)
        (Hex.FpPoly.congr_liftToZ_modP (p := p) g))
  have hmod := Hex.ZPoly.modP_eq_of_congr p
    (Hex.FpPoly.liftToZ (Hex.ZPoly.modP p f * Hex.ZPoly.modP p g))
    (f * g) hprod
  simpa [Hex.FpPoly.modP_liftToZ] using hmod.symm

theorem modP_dvd_modP_of_dvd
    (p : Nat) [Hex.ZMod64.Bounds p] {factor core : Hex.ZPoly}
    (hdvd : factor ∣ core) :
    Hex.ZPoly.modP p factor ∣ Hex.ZPoly.modP p core := by
  rcases hdvd with ⟨q, hq⟩
  refine ⟨Hex.ZPoly.modP p q, ?_⟩
  rw [hq, modP_mul]

/-- Divisibility at the `Hex.FpPoly p` layer preserves `isZero = false`:
if `a ∣ b` and `b.isZero = false` then `a.isZero = false`. The bespoke
`Dvd` instance for `Hex.FpPoly p` is `instDvdOfAddOfMul`, not Mathlib's
`semigroupDvd`, so Mathlib's `dvd`-based zero-propagation lemmas do not
apply at this layer and the boolean-`isZero` contrapositive is rebuilt
directly here. -/
private theorem fpPoly_isZero_false_of_dvd_of_isZero_false
    {p : Nat} [Hex.ZMod64.Bounds p] {a b : Hex.FpPoly p}
    (hab : a ∣ b) (hb : b.isZero = false) : a.isZero = false := by
  cases ha : a.isZero with
  | false => rfl
  | true =>
      exfalso
      have ha_zero : a = 0 := by
        apply Hex.DensePoly.ext_coeff
        intro n
        have hsize : a.size = 0 := by
          change a.coeffs.isEmpty = true at ha
          simpa [Hex.DensePoly.size, Array.isEmpty_iff_size_eq_zero] using ha
        rw [Hex.DensePoly.coeff_eq_zero_of_size_le a (by omega)]
        exact Hex.DensePoly.coeff_zero n
      rcases hab with ⟨q, hq⟩
      rw [ha_zero, Hex.FpPoly.zero_mul] at hq
      rw [hq] at hb
      exact Bool.noConfusion hb

/-- Transitivity of `Hex.FpPoly p`-level divisibility. Discharges the
`c = a * (q * v)` step explicitly via `Hex.FpPoly.mul_assoc` because the
`Dvd` instance on `Hex.FpPoly p` is the bespoke `instDvdOfAddOfMul`
(witness shape `b = a * r`), and `dvd_trans` does not see through that. -/
private theorem fpPoly_dvd_trans
    {p : Nat} [Hex.ZMod64.Bounds p]
    {a b c : Hex.FpPoly p} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  refine ⟨q * v, ?_⟩
  rw [hv, hq]
  exact Hex.FpPoly.mul_assoc _ _ _

/-- Products of divisors divide products at the executable `Hex.FpPoly p`
level. The `Dvd` instance on `Hex.FpPoly p` is the bespoke
`instDvdOfAddOfMul` (witness shape `b = a * r`), so Mathlib's
`mul_dvd_mul` does not see through it. -/
private theorem fpPoly_mul_dvd_mul
    {p : Nat} [Hex.ZMod64.Bounds p]
    {a b c d : Hex.FpPoly p} (hab : a ∣ b) (hcd : c ∣ d) :
    a * c ∣ b * d := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨v, hv⟩ := hcd
  refine ⟨q * v, ?_⟩
  rw [hq, hv]
  rw [Hex.FpPoly.mul_assoc a q (c * v)]
  rw [← Hex.FpPoly.mul_assoc q c v]
  rw [Hex.FpPoly.mul_comm q c]
  rw [Hex.FpPoly.mul_assoc c q v]
  rw [← Hex.FpPoly.mul_assoc a c (q * v)]

theorem monicModPImage_dvd_monicModularImage_of_dvd_of_choosePrimeData?_some
    {core factor : Hex.ZPoly}
    (hdvd : factor ∣ core)
    (_hcore_ne : core ≠ 0)
    {primeData : Hex.PrimeChoiceData}
    (hsome : Hex.choosePrimeData? core = some primeData) :
    letI := primeData.bounds
    @monicModPImage primeData.p primeData.bounds
        (@Hex.ZPoly.modP primeData.p primeData.bounds factor) ∣
      Hex.monicModularImage
        (@Hex.ZPoly.modP primeData.p primeData.bounds core) := by
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hsome
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hsome
  have hcore_iszero :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  have hcore_mod_ne : @Hex.ZPoly.modP primeData.p primeData.bounds core ≠ 0 := by
    intro hzero
    rw [hzero] at hcore_iszero
    contradiction
  have hfactor_dvd_core :
      @Hex.ZPoly.modP primeData.p primeData.bounds factor ∣
        @Hex.ZPoly.modP primeData.p primeData.bounds core :=
    modP_dvd_modP_of_dvd primeData.p hdvd
  have hfactor_iszero :
      (@Hex.ZPoly.modP primeData.p primeData.bounds factor).isZero = false :=
    fpPoly_isZero_false_of_dvd_of_isZero_false hfactor_dvd_core hcore_iszero
  have hmonic_factor_dvd_factor :
      @monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor) ∣
        @Hex.ZPoly.modP primeData.p primeData.bounds factor :=
    monicModPImage_dvd_self_of_ne_zero hprime hfactor_iszero
  have hmonic_factor_dvd_core :
      @monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor) ∣
        @Hex.ZPoly.modP primeData.p primeData.bounds core :=
    fpPoly_dvd_trans hmonic_factor_dvd_factor hfactor_dvd_core
  have hcore_dvd_monic :
      @Hex.ZPoly.modP primeData.p primeData.bounds core ∣
        Hex.monicModularImage
          (@Hex.ZPoly.modP primeData.p primeData.bounds core) := by
    unfold Hex.monicModularImage
    simp only [hcore_iszero, Bool.false_eq_true, ↓reduceIte]
    refine ⟨Hex.DensePoly.C
        (Hex.DensePoly.leadingCoeff
          (@Hex.ZPoly.modP primeData.p primeData.bounds core))⁻¹, ?_⟩
    calc
      Hex.DensePoly.scale
          (Hex.DensePoly.leadingCoeff
            (@Hex.ZPoly.modP primeData.p primeData.bounds core))⁻¹
          (@Hex.ZPoly.modP primeData.p primeData.bounds core)
          = Hex.DensePoly.C
              (Hex.DensePoly.leadingCoeff
                (@Hex.ZPoly.modP primeData.p primeData.bounds core))⁻¹ *
            (@Hex.ZPoly.modP primeData.p primeData.bounds core) := by
            rw [Hex.FpPoly.C_mul_eq_scale]
      _ = (@Hex.ZPoly.modP primeData.p primeData.bounds core) *
            Hex.DensePoly.C
              (Hex.DensePoly.leadingCoeff
                (@Hex.ZPoly.modP primeData.p primeData.bounds core))⁻¹ :=
            Hex.DensePoly.mul_comm_poly _ _
  exact fpPoly_dvd_trans hmonic_factor_dvd_core hcore_dvd_monic

/--
An integer factor is represented modulo the selected prime by a subset of the
recorded modular factors when the subset product is the monic modular image of
that integer factor.
-/
def RepresentsIntegerFactorModP
    (primeData : Hex.PrimeChoiceData) (factor : Hex.ZPoly)
    (S : ModPFactorSubset primeData) : Prop :=
  modPFactorProduct primeData S =
    @monicModPImage primeData.p primeData.bounds
      (@Hex.ZPoly.modP primeData.p primeData.bounds factor)

/--
Proof-facing package for the mod-`p` irreducible-factor subset partition over
the executable `PrimeChoiceData` surface.

The proposition parameters are hooks for the eventual admissible-prime and
square-free-reduction hypotheses. Downstream callers should depend on the
existence and uniqueness projections below rather than on a particular analytic
proof of this package.
-/
structure ModPSubsetPartitionHypotheses
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (admissiblePrime squareFreeReduction : Prop) : Prop where
  fModP_eq : primeData.fModP = @Hex.ZPoly.modP primeData.p primeData.bounds core
  admissible_prime : admissiblePrime
  square_free_reduction : squareFreeReduction
  factors_irreducible :
    ∀ i : ModPFactorIndex primeData,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (modPFactor primeData i))
  exists_subset :
    ∀ {factor : Hex.ZPoly},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      ∃ S : ModPFactorSubset primeData, RepresentsIntegerFactorModP primeData factor S
  unique_subset :
    ∀ {factor : Hex.ZPoly} {S T : ModPFactorSubset primeData},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorModP primeData factor S →
      RepresentsIntegerFactorModP primeData factor T →
      S = T

/--
Caller-facing mod-`p` subset partition: an irreducible integer factor of the
core has a unique representing subset of the selected modular factors.
-/
theorem existsUnique_modPFactorSubset_of_modPSubsetPartition
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (h :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃! S : ModPFactorSubset primeData, RepresentsIntegerFactorModP primeData factor S := by
  rcases h.exists_subset hirr hdvd with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  intro T hT
  exact (h.unique_subset (factor := factor) (S := S) (T := T) hirr hdvd hS hT).symm

/-- Existence projection from the mod-`p` subset-partition package. -/
theorem exists_modPFactorSubset_of_modPSubsetPartition
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (h :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃ S : ModPFactorSubset primeData, RepresentsIntegerFactorModP primeData factor S :=
  h.exists_subset hirr hdvd

/-- Uniqueness projection from the mod-`p` subset-partition package. -/
theorem unique_modPFactorSubset_of_modPSubsetPartition
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (h :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    {factor : Hex.ZPoly} {S T : ModPFactorSubset primeData}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hS : RepresentsIntegerFactorModP primeData factor S)
    (hT : RepresentsIntegerFactorModP primeData factor T) :
    S = T :=
  h.unique_subset (factor := factor) (S := S) (T := T) hirr hdvd hS hT

/-- Irreducibility projection for a selected modular factor. -/
theorem modPFactor_irreducible_of_modPSubsetPartition
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {admissiblePrime squareFreeReduction : Prop}
    (h :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (i : ModPFactorIndex primeData) :
    Irreducible
      (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
        (modPFactor primeData i)) :=
  h.factors_irreducible i

/-- Index type for the local factors stored in executable Hensel lift data. -/
abbrev LiftedFactorIndex (d : Hex.LiftData) : Type :=
  Fin d.liftedFactors.size

/-- A finite subset of the local factors stored in executable Hensel lift data. -/
abbrev LiftedFactorSubset (d : Hex.LiftData) : Type :=
  Finset (LiftedFactorIndex d)

/-- The lifted local factor at an executable `LiftData` index. -/
def liftedFactor (d : Hex.LiftData) (i : LiftedFactorIndex d) : Hex.ZPoly :=
  d.liftedFactors[i]

/-- Product of the lifted local factors selected by a finite subset. -/
def liftedFactorProduct (d : Hex.LiftData) (S : LiftedFactorSubset d) : Hex.ZPoly :=
  S.toList.foldl (fun acc i => acc * liftedFactor d i) 1

/-- Transport a modular-factor index to the corresponding lifted-factor index. -/
def liftedIndexOfModPIndex
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (i : ModPFactorIndex primeData) : LiftedFactorIndex d :=
  ⟨i.val, by
    rw [hsize]
    exact i.isLt⟩

/-- Embedding version of `liftedIndexOfModPIndex` for finite-set transport. -/
def modPIndexToLiftedEmbedding
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size) :
    ModPFactorIndex primeData ↪ LiftedFactorIndex d where
  toFun := liftedIndexOfModPIndex primeData d hsize
  inj' := by
    intro i j hij
    apply Fin.ext
    change i.val = j.val
    have hval :=
      congrArg (fun x : LiftedFactorIndex d => x.val) hij
    simpa [liftedIndexOfModPIndex] using hval

/--
Transport a selected subset of modular factors to the corresponding selected
subset of lifted factors, once the lift stage is known to preserve factor count.
-/
def liftedSubsetOfModPSubset
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (S : ModPFactorSubset primeData) : LiftedFactorSubset d :=
  S.map (modPIndexToLiftedEmbedding primeData d hsize)

/--
Selected lifted-factor product scaled by the leading coefficient of the integer
core, matching the product formed by the executable recombination candidate
checker.
-/
def scaledLiftedFactorProduct
    (core : Hex.ZPoly) (d : Hex.LiftData) (S : LiftedFactorSubset d) : Hex.ZPoly :=
  Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) (liftedFactorProduct d S)

/--
An integer factor is represented by a subset of the lifted local factors when
the executable scaled selected product agrees with the factor modulo the Hensel
modulus `p^k`.
-/
def RepresentsIntegerFactorAtLift
    (core : Hex.ZPoly) (d : Hex.LiftData) (factor : Hex.ZPoly)
    (S : LiftedFactorSubset d) : Prop :=
  Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k =
    Hex.ZPoly.reduceModPow factor d.p d.k

/--
Proof-side form of the executable recombination candidate, using the selected
lifted-factor product directly.  The executable-list version is introduced
later, after the list-selection identification has been developed, and is proved equal
to this definition.
-/
def liftedFactorProductCandidate (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Hex.ZPoly :=
  Hex.normalizeFactorSign <|
    Hex.ZPoly.primitivePart <|
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)

/-- Scaled variant of the recombination candidate: centred lift of the
leading-coefficient-scaled selected lifted-factor product, primitivised and
sign-normalised.  This is the primitive non-monic supporting lemma used by the scaled
recombination search. -/
def scaledRecombinationCandidate
    (core : Hex.ZPoly) (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Hex.ZPoly :=
  Hex.normalizeFactorSign <|
    Hex.ZPoly.primitivePart <|
      Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k)

/--
Proof-facing package for the square-free Hensel subset correspondence over the
executable `PrimeChoiceData`/`LiftData` surface.

The two proposition parameters are hooks for the precise admissible-prime and
successful-lift hypotheses supplied by the later analytic Hensel proof.  The
caller theorems below depend only on the resulting existence and uniqueness
fields, so downstream exhaustive-recombination proofs can be written against a
stable executable API.
-/
structure HenselSubsetCorrespondenceHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData) (admissiblePrime successfulLift : Prop) : Prop where
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  admissible_prime : admissiblePrime
  successful_lift : successfulLift
  exists_subset :
    ∀ {factor : Hex.ZPoly},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      ∃ S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S
  unique_subset :
    ∀ {factor : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor S →
      RepresentsIntegerFactorAtLift core d factor T →
      S = T

/--
Caller-facing square-free Hensel subset correspondence: an irreducible
integer factor of the core has a unique representing subset of the executable
lifted local factors.
-/
theorem existsUnique_liftedFactorSubset_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃! S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S := by
  rcases h.exists_subset hirr hdvd with ⟨S, hS⟩
  refine ⟨S, hS, ?_⟩
  intro T hT
  exact (h.unique_subset (factor := factor) (S := S) (T := T) hirr hdvd hS hT).symm

/-- Existence projection from the executable Hensel subset-correspondence API. -/
theorem exists_liftedFactorSubset_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃ S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S :=
  h.exists_subset hirr hdvd

/-- Uniqueness projection from the executable Hensel subset-correspondence API. -/
theorem unique_liftedFactorSubset_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly} {S T : LiftedFactorSubset d}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hS : RepresentsIntegerFactorAtLift core d factor S)
    (hT : RepresentsIntegerFactorAtLift core d factor T) :
    S = T :=
  h.unique_subset (factor := factor) (S := S) (T := T) hirr hdvd hS hT

/--
Descent wrapper for lifted Hensel subset representations.

Once the mod-`p` subset partition, the lifted-subset correspondence, and the
forward mod-`p`-to-lift transport are available, any lifted representation of
an irreducible integer factor is the canonical lift of its unique mod-`p`
representing subset.  This packages the purely structural part of the descent
argument; the analytic Hensel facts remain supplied by the input hypotheses.
-/
theorem henselLiftData_represents_modP_of_lifted
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift : Prop}
    (hmod :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hcorr :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core d factor
          (liftedSubsetOfModPSubset primeData d hsize S))
    {factor : Hex.ZPoly} {T : LiftedFactorSubset d}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hT : RepresentsIntegerFactorAtLift core d factor T) :
    ∃ S : ModPFactorSubset primeData,
      T = liftedSubsetOfModPSubset primeData d hsize S ∧
        RepresentsIntegerFactorModP primeData factor S := by
  rcases hmod.exists_subset hirr hdvd with ⟨S, hS_mod⟩
  have hS_lift :
      RepresentsIntegerFactorAtLift core d factor
        (liftedSubsetOfModPSubset primeData d hsize S) :=
    hlifted_of_modP hirr hdvd hS_mod
  have hT_eq :
      T = liftedSubsetOfModPSubset primeData d hsize S := by
    exact (hcorr.unique_subset hirr hdvd hS_lift hT).symm
  exact ⟨S, hT_eq, hS_mod⟩

/--
Proof-facing package for transporting the mod-`p` subset partition through a
successful Hensel lift.

The fields isolate the analytic Hensel obligations: the lift preserves the
factor count, every mod-`p` selected subset represents the same integer factor
after lifting, and every lifted representation descends to a mod-`p` selected
subset.  The caller theorems below combine these fields with
`ModPSubsetPartitionHypotheses` to recover the existing lifted-subset
correspondence API.
-/
structure HenselSubsetLiftHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData)
    (admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop) :
    Prop where
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  factor_count_eq : d.liftedFactors.size = primeData.factorsModP.size
  admissible_prime : admissiblePrime
  square_free_reduction : squareFreeReduction
  successful_lift : successfulLift
  coprime_lift : coprimeLift
  represents_lifted_of_modP :
    ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorModP primeData factor S →
      RepresentsIntegerFactorAtLift core d factor
        (liftedSubsetOfModPSubset primeData d factor_count_eq S)
  represents_modP_of_lifted :
    ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor T →
      ∃ S : ModPFactorSubset primeData,
        T = liftedSubsetOfModPSubset primeData d factor_count_eq S ∧
          RepresentsIntegerFactorModP primeData factor S

/--
Explicit descent-only package for the lifted Hensel side.

This gives the reverse transport obligation a name independent of the full
`HenselSubsetCorrespondenceHypotheses` API.  Callers still have to prove the
descent field; the point of the package is that they can combine that proof
with forward Hensel transport without first constructing the lifted subset
correspondence.
-/
structure HenselLiftDescentHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData) (successfulLift coprimeLift : Prop) : Prop where
  lift_eq : d = Hex.ZPoly.toMonicLiftData core B primeData
  factor_count_eq : d.liftedFactors.size = primeData.factorsModP.size
  successful_lift : successfulLift
  coprime_lift : coprimeLift
  represents_modP_of_lifted :
    ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      RepresentsIntegerFactorAtLift core d factor T →
      ∃ S : ModPFactorSubset primeData,
        T = liftedSubsetOfModPSubset primeData d factor_count_eq S ∧
          RepresentsIntegerFactorModP primeData factor S

/--
Non-circular assembly of `HenselSubsetLiftHypotheses` from explicit forward
Hensel transport and lifted-side descent.
-/
theorem henselSubsetLiftHypotheses_of_forwardTransport_descent
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hadmissible : admissiblePrime)
    (hsquareFree : squareFreeReduction)
    (hdescent :
      HenselLiftDescentHypotheses core B primeData d
        successfulLift coprimeLift)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core d factor
          (liftedSubsetOfModPSubset primeData d hdescent.factor_count_eq S)) :
    HenselSubsetLiftHypotheses core B primeData d
      admissiblePrime squareFreeReduction successfulLift coprimeLift where
  lift_eq := hdescent.lift_eq
  factor_count_eq := hdescent.factor_count_eq
  admissible_prime := hadmissible
  square_free_reduction := hsquareFree
  successful_lift := hdescent.successful_lift
  coprime_lift := hdescent.coprime_lift
  represents_lifted_of_modP := by
    intro factor S hirr hdvd hrep
    exact hlifted_of_modP hirr hdvd hrep
  represents_modP_of_lifted := by
    intro factor T hirr hdvd hrep
    exact hdescent.represents_modP_of_lifted hirr hdvd hrep

/--
The mod-`p` subset selected for an irreducible integer factor has a unique
lifted representative through the Hensel transport package.
-/
theorem existsUnique_modPSubset_lifting_to_henselRepresentation
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hmod :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hlift :
      HenselSubsetLiftHypotheses core B primeData d
        admissiblePrime squareFreeReduction successfulLift coprimeLift)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃! S : ModPFactorSubset primeData,
      RepresentsIntegerFactorModP primeData factor S ∧
        RepresentsIntegerFactorAtLift core d factor
          (liftedSubsetOfModPSubset primeData d hlift.factor_count_eq S) := by
  rcases hmod.exists_subset hirr hdvd with ⟨S, hS_mod⟩
  refine ⟨S, ⟨hS_mod, hlift.represents_lifted_of_modP hirr hdvd hS_mod⟩, ?_⟩
  intro T hT
  exact hmod.unique_subset hirr hdvd hT.1 hS_mod

/--
Composing the mod-`p` subset partition with Hensel-lift transport gives the
caller-facing lifted-factor subset correspondence.
-/
theorem existsUnique_liftedFactorSubset_of_modPSubsetPartition_henselLift
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hmod :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hlift :
      HenselSubsetLiftHypotheses core B primeData d
        admissiblePrime squareFreeReduction successfulLift coprimeLift)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core) :
    ∃! S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S := by
  rcases hmod.exists_subset hirr hdvd with ⟨S, hS_mod⟩
  let liftedS := liftedSubsetOfModPSubset primeData d hlift.factor_count_eq S
  have hS_lift : RepresentsIntegerFactorAtLift core d factor liftedS :=
    hlift.represents_lifted_of_modP hirr hdvd hS_mod
  refine ⟨liftedS, hS_lift, ?_⟩
  intro T hT
  rcases hlift.represents_modP_of_lifted hirr hdvd hT with ⟨U, hT_eq, hU_mod⟩
  have hUS : U = S :=
    hmod.unique_subset hirr hdvd hU_mod hS_mod
  rw [hT_eq, hUS]

/--
The mod-`p` partition plus Hensel transport produces the existing
`HenselSubsetCorrespondenceHypotheses` package, so downstream callers can
use the stable lifted-factor API without depending on the intermediate
mod-`p` vocabulary.
-/
def henselSubsetCorrespondence_of_modPSubsetPartition
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData}
    {admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop}
    (hmod :
      ModPSubsetPartitionHypotheses core primeData
        admissiblePrime squareFreeReduction)
    (hlift :
      HenselSubsetLiftHypotheses core B primeData d
        admissiblePrime squareFreeReduction successfulLift coprimeLift) :
    HenselSubsetCorrespondenceHypotheses core B primeData d
      admissiblePrime successfulLift where
  lift_eq := hlift.lift_eq
  admissible_prime := hlift.admissible_prime
  successful_lift := hlift.successful_lift
  exists_subset := by
    intro factor hirr hdvd
    exact
      (existsUnique_liftedFactorSubset_of_modPSubsetPartition_henselLift
        hmod hlift hirr hdvd).exists
  unique_subset := by
    intro factor S T hirr hdvd hS hT
    rcases
      existsUnique_liftedFactorSubset_of_modPSubsetPartition_henselLift
        hmod hlift hirr hdvd with
      ⟨U, hU, huniq⟩
    exact (huniq S hS).trans (huniq T hT).symm

/--
Abstract-bound variant of
`centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision`: takes an
arbitrary `B' : Nat` and an explicit validity hypothesis
`hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The body just
threads `B'` and `hvalid` into `centeredLiftPoly_eq_of_reduceModPow_eq`
(which already accepts an abstract bound).  The original core-shape
theorem is a wrapper around this variant.
-/
theorem centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    Hex.centeredLiftPoly
        (Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k)
        (d.p ^ d.k) =
      factor :=
  Hex.centeredLiftPoly_eq_of_reduceModPow_eq
    factor (scaledLiftedFactorProduct core d S) d.p d.k
    B' hvalid hprecision hrep

/--
Mignotte recoverability for one represented integer factor.

If a subset of the executable lifted factors represents an integer divisor of
`core` modulo the Hensel modulus, and that modulus is beyond twice the default
Mignotte coefficient bound for `core`, then the executable centred-lift
operation recovers the integer factor exactly.

This is a thin wrapper over the abstract-bound variant
`centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
HO-1 callers should prefer the `_of_bound` variant directly with
`B' := defaultFactorCoeffBound f`, bypassing the squareFreeCore-bound
monotonicity obligation called out by
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`.
-/
theorem centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    Hex.centeredLiftPoly
        (Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k)
        (d.p ^ d.k) =
      factor :=
  centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hrep hprecision

/--
Abstract-bound variant of
`existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The body mirrors
the original but invokes the `_of_bound` recovery theorem instead of
the core-shape one.
-/
theorem existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence_of_bound
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∃! S : LiftedFactorSubset d,
      RepresentsIntegerFactorAtLift core d factor S ∧
        Hex.centeredLiftPoly
            (Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k)
            (d.p ^ d.k) =
          factor := by
  rcases h.exists_subset hirr hdvd with ⟨S, hS⟩
  refine ⟨S, ⟨hS, ?_⟩, ?_⟩
  · exact
      centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound
        B' hvalid hS hprecision
  · intro T hT
    exact
      (h.unique_subset (factor := factor) (S := S) (T := T)
        hirr hdvd hS hT.1).symm

/--
Group A2 packaged for downstream exhaustive-search proofs: under the Hensel
subset-correspondence hypotheses, each irreducible integer factor has a unique
lifted-factor subset whose scaled product both represents it modulo the Hensel
modulus and centred-lifts back to the factor exactly at Mignotte precision.

This is a thin wrapper over
`existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∃! S : LiftedFactorSubset d,
      RepresentsIntegerFactorAtLift core d factor S ∧
        Hex.centeredLiftPoly
            (Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k)
            (d.p ^ d.k) =
          factor :=
  existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence_of_bound
    h (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hirr hdvd hprecision

/--
The A2 recoverability package specialized to the slow exhaustive path's
default Mignotte precision exponent.
-/
theorem existsUnique_recoveringLiftedFactorSubset_at_defaultPrecision
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core
        (Hex.precisionForCoeffBound (Hex.ZPoly.defaultFactorCoeffBound core)
          primeData.p)
        primeData d admissiblePrime successfulLift)
    {factor : Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∃! S : LiftedFactorSubset d,
      RepresentsIntegerFactorAtLift core d factor S ∧
        Hex.centeredLiftPoly
            (Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d S) d.p d.k)
            (d.p ^ d.k) =
          factor :=
  existsUnique_recoveringLiftedFactorSubset_of_henselSubsetCorrespondence
    h hcore_ne hirr hdvd hprecision

/--
Induced subset-correspondence predicate for the recursive state of the
exhaustive recombination search.

After the search consumes a prefix of subsets, it recurses on a `target`
polynomial (a quotient of `core` by the factors emitted so far) with a reduced
index set `J ⊆ Finset.univ` of lifted-factor indices not yet selected.  This
predicate packages the correspondence between irreducible integer divisors of
`target` and their representing lifted-factor subsets, constrained to live in
`J`.

When `target = core` and `J = Finset.univ`, this reduces to the existence and
uniqueness fields of `HenselSubsetCorrespondenceHypotheses`.  Downstream
coverage proofs use the predicate to track the recursive state across one
emission step at a time.
-/
structure HenselSubsetCorrespondenceRest
    (core : Hex.ZPoly) (d : Hex.LiftData)
    (J : LiftedFactorSubset d) (target : Hex.ZPoly) : Prop where
  exists_subset :
    ∀ {factor : Hex.ZPoly},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ target →
      ∃ S : LiftedFactorSubset d,
        S ⊆ J ∧ RepresentsIntegerFactorAtLift core d factor S
  unique_subset :
    ∀ {factor : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ target →
      S ⊆ J →
      T ⊆ J →
      RepresentsIntegerFactorAtLift core d factor S →
      RepresentsIntegerFactorAtLift core d factor T →
      S = T

/--
Initial-state lemma: a Hensel subset correspondence implies the induced
predicate at the full universe of lifted-factor indices with `target = core`.
This is the entry point for downstream recursive-search coverage proofs.
-/
theorem henselSubsetCorrespondenceRest_initial
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift) :
    HenselSubsetCorrespondenceRest core d Finset.univ core where
  exists_subset := by
    intro factor hirr hdvd
    rcases h.exists_subset hirr hdvd with ⟨S, hS⟩
    exact ⟨S, Finset.subset_univ S, hS⟩
  unique_subset := by
    intro factor S T hirr hdvd _hS_in _hT_in hS hT
    exact h.unique_subset hirr hdvd hS hT

/--
Existence-uniqueness caller view of the induced predicate, mirroring
`existsUnique_liftedFactorSubset_of_henselSubsetCorrespondence` at the
recursive-state surface.
-/
theorem existsUnique_liftedFactorSubset_of_henselSubsetCorrespondenceRest
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d}
    (h : HenselSubsetCorrespondenceRest core d J target)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ target) :
    ∃! S : LiftedFactorSubset d,
      S ⊆ J ∧ RepresentsIntegerFactorAtLift core d factor S := by
  rcases h.exists_subset hirr hdvd with ⟨S, hSJ, hS⟩
  refine ⟨S, ⟨hSJ, hS⟩, ?_⟩
  intro T hT
  exact h.unique_subset hirr hdvd hT.1 hSJ hT.2 hS

/-- Transitivity of `Hex.ZPoly`-level divisibility. Discharges the
`core = g * (q * v)` step explicitly via `Hex.DensePoly.mul_assoc_poly`
because `Hex.ZPoly` does not synthesise a Mathlib `Semigroup` instance
at this layer. -/
private theorem zpoly_dvd_trans
    {a b c : Hex.ZPoly} (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨v, hv⟩ := hbc
  refine ⟨q * v, ?_⟩
  rw [hv, hq]
  exact Hex.DensePoly.mul_assoc_poly (S := Int) _ _ _

/--
Transport an induced Hensel subset correspondence through one emitted
recombination factor.

The emitted subset `S` is removed from the remaining index set.  The only
non-structural obligation is the expected disjointness fact: every irreducible
divisor of the quotient must be represented by a subset disjoint from the
emitted subset.  Later coverage proofs discharge that from square-free
factorisation/associatedness; this lemma packages the pure rest-state transport
and reuses the parent state's uniqueness field.
-/
theorem henselSubsetCorrespondenceRest_transport_of_disjoint
    {core target quotient emitted : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d}
    (h : HenselSubsetCorrespondenceRest core d J target)
    (hquot : quotient * emitted = target)
    (hdisjoint :
      ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ quotient →
        T ⊆ J →
        RepresentsIntegerFactorAtLift core d factor T →
        Disjoint T S) :
    HenselSubsetCorrespondenceRest core d (J \ S) quotient where
  exists_subset := by
    intro factor hirr hdvd_quot
    have hdvd_target : factor ∣ target :=
      zpoly_dvd_trans hdvd_quot ⟨emitted, hquot.symm⟩
    rcases h.exists_subset hirr hdvd_target with ⟨T, hTJ, hTrep⟩
    have hTS : Disjoint T S := hdisjoint hirr hdvd_quot hTJ hTrep
    refine ⟨T, ?_, hTrep⟩
    intro i hi
    exact Finset.mem_sdiff.mpr
      ⟨hTJ hi, fun hiS => (Finset.disjoint_left.mp hTS) hi hiS⟩
  unique_subset := by
    intro factor T U hirr hdvd_quot hTJU hUJU hTrep hUrep
    have hdvd_target : factor ∣ target :=
      zpoly_dvd_trans hdvd_quot ⟨emitted, hquot.symm⟩
    apply h.unique_subset hirr hdvd_target
    · intro i hi
      exact (Finset.mem_sdiff.mp (hTJU hi)).1
    · intro i hi
      exact (Finset.mem_sdiff.mp (hUJU hi)).1
    · exact hTrep
    · exact hUrep

/--
Strengthened rest predicate that augments `HenselSubsetCorrespondenceRest`
with the structural facts the recursive-coverage proof (issue #4301) needs:
square-freeness of `target` in `Polynomial ℤ`, a cover field saying every
remaining index lies in *some* representing subset, a pairwise-disjoint
field for non-associated irreducible divisors, and a uniqueness-up-to-
association field saying associated irreducible divisors of `target` share
their representing subset.

The doc-comment on `henselSubsetCorrespondenceRest_transport_of_disjoint`
flags the disjointness obligation as "discharged from square-free
factorisation by later coverage proofs"; this predicate packages exactly
that information.

The initial-state constructor (from `HenselSubsetCorrespondenceHypotheses`
plus a square-free reduction hypothesis) is intentionally deferred to a
follow-up issue: #4301 only needs the abstract predicate and its transport
through one emitted recombination factor.
-/
structure LiftedFactorSubsetPartition
    (core : Hex.ZPoly) (d : Hex.LiftData)
    (J : LiftedFactorSubset d) (target : Hex.ZPoly) : Prop
    extends HenselSubsetCorrespondenceRest core d J target where
  target_squarefree : Squarefree (HexPolyZMathlib.toPolynomial target)
  cover :
    ∀ {i : LiftedFactorIndex d}, i ∈ J →
      ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
        Irreducible (HexPolyZMathlib.toPolynomial f) ∧
        f ∣ target ∧
        S ⊆ J ∧ i ∈ S ∧
        RepresentsIntegerFactorAtLift core d f S
  pairwise_disjoint :
    ∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      Irreducible (HexPolyZMathlib.toPolynomial g) →
      g ∣ target →
      T ⊆ J →
      RepresentsIntegerFactorAtLift core d g T →
      ¬ Associated (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial g) →
      Disjoint S T
  unique_up_to_associated :
    ∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      Irreducible (HexPolyZMathlib.toPolynomial g) →
      g ∣ target →
      T ⊆ J →
      RepresentsIntegerFactorAtLift core d g T →
      Associated (HexPolyZMathlib.toPolynomial f)
        (HexPolyZMathlib.toPolynomial g) →
      S = T
  support_subset_of_dvd_recombinationCandidate :
    ∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      T ⊆ J →
      f ∣ liftedFactorProductCandidate d T →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      S ⊆ T
  support_subset_of_dvd_scaledRecombinationCandidate :
    ∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
      Irreducible (HexPolyZMathlib.toPolynomial f) →
      f ∣ target →
      T ⊆ J →
      f ∣ scaledRecombinationCandidate core d T →
      S ⊆ J →
      RepresentsIntegerFactorAtLift core d f S →
      S ⊆ T

/--
Specialisation of `LiftedFactorSubsetPartition.cover` to `J.min'`: the
minimum index of a nonempty remaining set lies in the representing subset
of some irreducible divisor of `target`. This is the exact "cover at min"
fact used by the recombination search to descend through `J.min'`'s split
even when the chosen factor's representing subset does not contain it.
-/
theorem LiftedFactorSubsetPartition.cover_at_min
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d}
    (h : LiftedFactorSubsetPartition core d J target)
    (hne : J.Nonempty) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S :=
  h.cover (J.min'_mem hne)

/--
Transport a `LiftedFactorSubsetPartition` through one emitted recombination
factor. The square-free assumption on `target` propagates to `quotient`
(via `Squarefree.squarefree_of_dvd`), and discharges the disjointness
obligation of `henselSubsetCorrespondenceRest_transport_of_disjoint` by
ruling out non-trivial associated divisors of `quotient`.
-/
theorem liftedFactorSubsetPartition_transport
    {core target quotient emitted : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d}
    (h : LiftedFactorSubsetPartition core d J target)
    (hquot : quotient * emitted = target)
    (hSrepEmitted : RepresentsIntegerFactorAtLift core d emitted S)
    (hSJ : S ⊆ J)
    (hEmittedIrr : Irreducible (HexPolyZMathlib.toPolynomial emitted))
    (hEmittedDvd : emitted ∣ target) :
    LiftedFactorSubsetPartition core d (J \ S) quotient := by
  -- Mathlib-side facts derived from `hquot`.
  have hquot_poly :
      HexPolyZMathlib.toPolynomial quotient *
          HexPolyZMathlib.toPolynomial emitted =
        HexPolyZMathlib.toPolynomial target := by
    rw [← HexPolyZMathlib.toPolynomial_mul, hquot]
  have hquot_dvd_target_poly :
      HexPolyZMathlib.toPolynomial quotient ∣
        HexPolyZMathlib.toPolynomial target :=
    ⟨HexPolyZMathlib.toPolynomial emitted, hquot_poly.symm⟩
  have hquot_sqfree :
      Squarefree (HexPolyZMathlib.toPolynomial quotient) :=
    Squarefree.squarefree_of_dvd hquot_dvd_target_poly h.target_squarefree
  -- Helper: every irreducible divisor of `quotient` is non-associated to
  -- `emitted` (otherwise `target` would not be square-free).
  have hno_assoc_of_dvd_quot :
      ∀ {factor : Hex.ZPoly},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ quotient →
        ¬ Associated (HexPolyZMathlib.toPolynomial factor)
          (HexPolyZMathlib.toPolynomial emitted) := by
    intro factor hirr hdvd_quot h_assoc
    have h_fac_dvd_quot_poly :
        HexPolyZMathlib.toPolynomial factor ∣
          HexPolyZMathlib.toPolynomial quotient :=
      HexPolyMathlib.toPolynomial_dvd hdvd_quot
    have h_emit_dvd_quot_poly :
        HexPolyZMathlib.toPolynomial emitted ∣
          HexPolyZMathlib.toPolynomial quotient :=
      h_assoc.symm.dvd.trans h_fac_dvd_quot_poly
    have h_sq_dvd :
        HexPolyZMathlib.toPolynomial emitted *
            HexPolyZMathlib.toPolynomial emitted ∣
          HexPolyZMathlib.toPolynomial target := by
      rw [← hquot_poly]
      exact mul_dvd_mul_right h_emit_dvd_quot_poly
        (HexPolyZMathlib.toPolynomial emitted)
    exact hEmittedIrr.not_isUnit
      (h.target_squarefree _ h_sq_dvd)
  -- Lift `· ∣ quotient` to `· ∣ target = quotient * emitted`.
  have dvd_target_of_dvd_quotient :
      ∀ {factor : Hex.ZPoly}, factor ∣ quotient → factor ∣ target :=
    fun hdvd => zpoly_dvd_trans hdvd ⟨emitted, hquot.symm⟩
  -- Disjointness obligation for `henselSubsetCorrespondenceRest_transport_of_disjoint`.
  have hdisj :
      ∀ {factor : Hex.ZPoly} {T : LiftedFactorSubset d},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ quotient →
        T ⊆ J →
        RepresentsIntegerFactorAtLift core d factor T →
        Disjoint T S := by
    intro factor T hirr hdvd_quot hTJ hTrep
    exact h.pairwise_disjoint hirr (dvd_target_of_dvd_quotient hdvd_quot)
      hTJ hTrep hEmittedIrr hEmittedDvd hSJ hSrepEmitted
      (hno_assoc_of_dvd_quot hirr hdvd_quot)
  -- Build the rest part via the existing transport lemma.
  have hrest :
      HenselSubsetCorrespondenceRest core d (J \ S) quotient :=
    henselSubsetCorrespondenceRest_transport_of_disjoint
      h.toHenselSubsetCorrespondenceRest hquot hdisj
  refine
    { toHenselSubsetCorrespondenceRest := hrest
      target_squarefree := hquot_sqfree
      cover := ?_
      pairwise_disjoint := ?_
      unique_up_to_associated := ?_
      support_subset_of_dvd_recombinationCandidate := ?_
      support_subset_of_dvd_scaledRecombinationCandidate := ?_ }
  -- Cover for the new state at any `i ∈ J \ S`.
  · intro i hi_sdiff
    have ⟨hi_J, hi_notS⟩ := Finset.mem_sdiff.mp hi_sdiff
    obtain ⟨f, T, hirr, hdvd_target, hTJ, hi_T, hTrep⟩ := h.cover hi_J
    -- Either `f ~ emitted` (which forces `T = S`, contradicting `i ∉ S`)
    -- or `f` is prime-non-associated to `emitted` (so `f ∣ quotient`).
    by_cases h_assoc :
        Associated (HexPolyZMathlib.toPolynomial f)
          (HexPolyZMathlib.toPolynomial emitted)
    · exfalso
      have hTS : T = S :=
        h.unique_up_to_associated hirr hdvd_target hTJ hTrep
          hEmittedIrr hEmittedDvd hSJ hSrepEmitted h_assoc
      exact hi_notS (hTS ▸ hi_T)
    · -- `f` is an irreducible (hence prime in `Polynomial ℤ`) divisor of
      -- `quotient * emitted = target`, not associated to `emitted`, so it
      -- divides `quotient`.
      have hf_dvd_target_poly :
          HexPolyZMathlib.toPolynomial f ∣
            HexPolyZMathlib.toPolynomial target :=
        HexPolyMathlib.toPolynomial_dvd hdvd_target
      rw [← hquot_poly] at hf_dvd_target_poly
      have hf_prime : Prime (HexPolyZMathlib.toPolynomial f) := hirr.prime
      have hf_dvd_quot_poly :
          HexPolyZMathlib.toPolynomial f ∣
            HexPolyZMathlib.toPolynomial quotient := by
        rcases hf_prime.dvd_or_dvd hf_dvd_target_poly with hq | he
        · exact hq
        · exact absurd (hirr.associated_of_dvd hEmittedIrr he) h_assoc
      have hf_dvd_quot : f ∣ quotient := by
        rcases hf_dvd_quot_poly with ⟨r, hr⟩
        refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
        apply HexPolyZMathlib.equiv.injective
        show HexPolyZMathlib.toPolynomial quotient =
          HexPolyZMathlib.toPolynomial (f * HexPolyZMathlib.ofPolynomial r)
        rw [HexPolyZMathlib.toPolynomial_mul,
          HexPolyZMathlib.toPolynomial_ofPolynomial]
        exact hr
      have hTS : Disjoint T S :=
        hdisj hirr hf_dvd_quot hTJ hTrep
      refine ⟨f, T, hirr, hf_dvd_quot, ?_, hi_T, hTrep⟩
      intro j hj
      rw [Finset.mem_sdiff]
      refine ⟨hTJ hj, fun hjS => ?_⟩
      exact Finset.disjoint_left.mp hTS hj hjS
  -- Pairwise disjoint for the new state.
  · intro f g T U hirr_f hdvd_f hTJ hTrep hirr_g hdvd_g hUJ hUrep hno_assoc
    have hTJ_orig : T ⊆ J :=
      fun i hi => (Finset.mem_sdiff.mp (hTJ hi)).1
    have hUJ_orig : U ⊆ J :=
      fun i hi => (Finset.mem_sdiff.mp (hUJ hi)).1
    exact h.pairwise_disjoint hirr_f (dvd_target_of_dvd_quotient hdvd_f)
      hTJ_orig hTrep hirr_g (dvd_target_of_dvd_quotient hdvd_g)
      hUJ_orig hUrep hno_assoc
  -- Unique-up-to-associated for the new state.
  · intro f g T U hirr_f hdvd_f hTJ hTrep hirr_g hdvd_g hUJ hUrep h_assoc
    have hTJ_orig : T ⊆ J :=
      fun i hi => (Finset.mem_sdiff.mp (hTJ hi)).1
    have hUJ_orig : U ⊆ J :=
      fun i hi => (Finset.mem_sdiff.mp (hUJ hi)).1
    exact h.unique_up_to_associated hirr_f (dvd_target_of_dvd_quotient hdvd_f)
      hTJ_orig hTrep hirr_g (dvd_target_of_dvd_quotient hdvd_g)
      hUJ_orig hUrep h_assoc
  -- Support containment for candidates in the transported state.
  · intro f U T hirr hdvd_quot hTJ hfactor_dvd_candidate hUJ hUrep
    have hTJ_orig : T ⊆ J :=
      fun i hi => (Finset.mem_sdiff.mp (hTJ hi)).1
    have hUJ_orig : U ⊆ J :=
      fun i hi => (Finset.mem_sdiff.mp (hUJ hi)).1
    have hUT :
        U ⊆ T :=
      h.support_subset_of_dvd_recombinationCandidate hirr
        (dvd_target_of_dvd_quotient hdvd_quot) hTJ_orig
        hfactor_dvd_candidate hUJ_orig hUrep
    intro i hiU
    exact hUT hiU
  -- Scaled-support containment for candidates in the transported state.
  · intro f U T hirr hdvd_quot hTJ hfactor_dvd_candidate hUJ hUrep
    have hTJ_orig : T ⊆ J :=
      fun i hi => (Finset.mem_sdiff.mp (hTJ hi)).1
    have hUJ_orig : U ⊆ J :=
      fun i hi => (Finset.mem_sdiff.mp (hUJ hi)).1
    have hUT :
        U ⊆ T :=
      h.support_subset_of_dvd_scaledRecombinationCandidate hirr
        (dvd_target_of_dvd_quotient hdvd_quot) hTJ_orig
        hfactor_dvd_candidate hUJ_orig hUrep
    intro i hiU
    exact hUT hiU

/-! ### LiftedFactorSubset → executable recombination split

The executable recombination search at the lifted-factor surface enumerates
order-preserving partitions of `d.liftedFactors.toList` via
`Hex.subsetSplitsWithFirst`.  These helpers transport a proof-side
`LiftedFactorSubset d` (a `Finset` of indices) into a concrete `(selected,
rest)` partition that lies in the executable enumeration, with the
selected/rejected lists ordered by their original `d.liftedFactors` index.

The product equality matches the executable
`Array.polyProduct selected.toArray` against the proof-side
`liftedFactorProduct d S` after transport to `Polynomial ℤ`, where
multiplication is commutative and the order difference between the
index-preserving partition and `S.toList` becomes a permutation.
-/

/-- Boolean indicator vector for `S`, indexed by the same `Fin` order as
`d.liftedFactors.toList`. -/
def liftedSubsetMask (d : Hex.LiftData) (S : LiftedFactorSubset d) : List Bool :=
  (List.finRange d.liftedFactors.size).map fun i => decide (i ∈ S)

theorem liftedSubsetMask_length (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    (liftedSubsetMask d S).length = d.liftedFactors.toList.length := by
  unfold liftedSubsetMask; simp

/-- The list of lifted factors selected by `S`, ordered by their original
`d.liftedFactors` index. -/
def liftedSubsetSelectedList (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    List Hex.ZPoly :=
  (d.liftedFactors.toList.zip (liftedSubsetMask d S)).filterMap fun p =>
    if p.2 then some p.1 else none

/-- The list of lifted factors not selected by `S`, ordered by their original
`d.liftedFactors` index. -/
def liftedSubsetRejectedList (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    List Hex.ZPoly :=
  (d.liftedFactors.toList.zip (liftedSubsetMask d S)).filterMap fun p =>
    if p.2 then none else some p.1

/-- Generalised partition lemma: for any list paired with a Boolean mask of
matching length, the order-preserving selected/rejected partition lies in
`Hex.subsetSplits`. -/
private theorem subsetSplits_zip_filterMap_partition :
    ∀ (xs : List Hex.ZPoly) (mask : List Bool), mask.length = xs.length →
      ((xs.zip mask).filterMap (fun p => if p.2 then some p.1 else none),
        (xs.zip mask).filterMap (fun p => if p.2 then none else some p.1)) ∈
        Hex.subsetSplits xs := by
  intro xs
  induction xs with
  | nil =>
      intro mask hmask
      have : mask = [] := List.length_eq_zero_iff.mp hmask
      subst this
      simpa using Hex.subsetSplits_nil_mem
  | cons x xs ih =>
      intro mask hmask
      cases mask with
      | nil => simp at hmask
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hmask
          rw [List.zip_cons_cons, List.filterMap_cons, List.filterMap_cons]
          by_cases hb : b = true
          · subst hb
            simp only [if_true]
            exact Hex.subsetSplits_cons_left_mem (ih bs hmask)
          · have hb' : b = false := by cases b <;> simp_all
            subst hb'
            simp only
            exact Hex.subsetSplits_cons_right_mem (ih bs hmask)

/-- Converse to `subsetSplits_zip_filterMap_partition`: every executable
`subsetSplits` member is induced by a Boolean mask over the input list. -/
theorem subsetSplits_mem_exists_mask :
    ∀ {xs selected rest : List Hex.ZPoly},
      (selected, rest) ∈ Hex.subsetSplits xs →
        ∃ mask : List Bool,
          mask.length = xs.length ∧
            selected =
              (xs.zip mask).filterMap (fun p => if p.2 then some p.1 else none) ∧
            rest =
              (xs.zip mask).filterMap (fun p => if p.2 then none else some p.1)
  | [], selected, rest, h => by
      simp [Hex.subsetSplits] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨[], rfl, rfl, rfl⟩
  | x :: xs, selected, rest, h => by
      unfold Hex.subsetSplits at h
      rcases List.mem_append.mp h with hright | hleft
      · rcases List.mem_map.mp hright with ⟨split, hsplit, hsplit_eq⟩
        rcases split with ⟨selectedTail, restTail⟩
        simp only at hsplit_eq
        rcases hsplit_eq with ⟨rfl, rfl⟩
        rcases subsetSplits_mem_exists_mask hsplit with
          ⟨mask, hmask_len, hselected, hrest⟩
        refine ⟨false :: mask, by simp [hmask_len], ?_, ?_⟩
        · simp [hselected]
        · simp [hrest]
      · rcases List.mem_map.mp hleft with ⟨split, hsplit, hsplit_eq⟩
        rcases split with ⟨selectedTail, restTail⟩
        simp only at hsplit_eq
        rcases hsplit_eq with ⟨rfl, rfl⟩
        rcases subsetSplits_mem_exists_mask hsplit with
          ⟨mask, hmask_len, hselected, hrest⟩
        refine ⟨true :: mask, by simp [hmask_len], ?_, ?_⟩
        · simp [hselected]
        · simp [hrest]

/-- The lifted-factor subset partition lies in the executable
`Hex.subsetSplits` enumeration of the lifted-factor list. -/
theorem liftedSubsetSplit_mem_subsetSplits
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    (liftedSubsetSelectedList d S, liftedSubsetRejectedList d S) ∈
      Hex.subsetSplits d.liftedFactors.toList := by
  unfold liftedSubsetSelectedList liftedSubsetRejectedList
  exact subsetSplits_zip_filterMap_partition d.liftedFactors.toList
    (liftedSubsetMask d S) (liftedSubsetMask_length d S)

/-- Auxiliary partition lemma at the `subsetSplitsWithFirst` surface: when the
mask starts with `true`, the partition lies in
`Hex.subsetSplitsWithFirst (x :: xs)`. -/
private theorem subsetSplitsWithFirst_zip_filterMap_partition
    (x : Hex.ZPoly) (xs : List Hex.ZPoly) (bs : List Bool) (h : bs.length = xs.length) :
    (((x :: xs).zip (true :: bs)).filterMap (fun p => if p.2 then some p.1 else none),
      ((x :: xs).zip (true :: bs)).filterMap (fun p => if p.2 then none else some p.1)) ∈
      Hex.subsetSplitsWithFirst (x :: xs) := by
  rw [List.zip_cons_cons, List.filterMap_cons, List.filterMap_cons]
  simp only [if_true]
  exact Hex.subsetSplitsWithFirst_mem_cons (subsetSplits_zip_filterMap_partition xs bs h)

/-- Converse at the `subsetSplitsWithFirst` surface: every split comes from a
Boolean mask over the tail, with the head forced into the selected side. -/
theorem subsetSplitsWithFirst_mem_exists_tail_mask
    {x : Hex.ZPoly} {xs selected rest : List Hex.ZPoly}
    (h : (selected, rest) ∈ Hex.subsetSplitsWithFirst (x :: xs)) :
    ∃ mask : List Bool,
      mask.length = xs.length ∧
        selected =
          x :: (xs.zip mask).filterMap (fun p => if p.2 then some p.1 else none) ∧
        rest =
          (xs.zip mask).filterMap (fun p => if p.2 then none else some p.1) := by
  unfold Hex.subsetSplitsWithFirst at h
  rcases List.mem_map.mp h with ⟨split, hsplit, hsplit_eq⟩
  rcases split with ⟨selectedTail, restTail⟩
  simp only at hsplit_eq
  rcases hsplit_eq with ⟨rfl, rfl⟩
  rcases subsetSplits_mem_exists_mask hsplit with
    ⟨mask, hmask_len, hselected, hrest⟩
  exact ⟨mask, hmask_len, by simp [hselected], hrest⟩

/-- The first entry of `liftedSubsetMask d S`, via `head?`, records membership
of index `0` in `S`. -/
private theorem liftedSubsetMask_head?_eq_decide
    (d : Hex.LiftData) (S : LiftedFactorSubset d)
    (hpos : 0 < d.liftedFactors.size) :
    (liftedSubsetMask d S).head? =
      some (decide ((⟨0, hpos⟩ : LiftedFactorIndex d) ∈ S)) := by
  unfold liftedSubsetMask
  rw [List.head?_map]
  have hfin : (List.finRange d.liftedFactors.size).head? =
      some (⟨0, hpos⟩ : Fin d.liftedFactors.size) := by
    have h : (List.finRange d.liftedFactors.size)[0]? =
        some (⟨0, hpos⟩ : Fin d.liftedFactors.size) := by
      rw [List.getElem?_eq_getElem (by simp; exact hpos)]
      simp
    simpa [List.head?_eq_getElem?] using h
  rw [hfin]
  rfl

/-- General `filterMap`/`filter`-`map` equivalence: a `filterMap` whose body is
either `some (f x)` or `none` is the same as filtering then mapping. -/
private theorem List.filterMap_if_eq_map_filter
    {α β : Type _} (l : List α) (p : α → Bool) (f : α → β) :
    l.filterMap (fun x => if p x then some (f x) else none) =
      (l.filter p).map f := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      cases hp : p x with
      | true => simp [hp, ih]
      | false => simp [hp, ih]

/-- The selected list has the clean `filter`/`map` characterisation needed for
multiset/permutation reasoning. -/
private theorem liftedSubsetSelectedList_eq_filter_map
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    liftedSubsetSelectedList d S =
      ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∈ S)).map
        (liftedFactor d) := by
  unfold liftedSubsetSelectedList liftedSubsetMask liftedFactor
  -- Rewrite d.liftedFactors.toList as a finRange map.
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs, List.zip_map', List.filterMap_map]
  simp only [Function.comp_def]
  exact List.filterMap_if_eq_map_filter
    (List.finRange d.liftedFactors.size) (fun i => decide (i ∈ S))
    (fun i => d.liftedFactors[i])

/-- The order-preserving filter of `List.finRange n` by membership in a Finset
of `Fin n` is a permutation of the Finset's `toList`. -/
private theorem finRange_filter_mem_perm_toList
    {n : Nat} (S : Finset (Fin n)) :
    ((List.finRange n).filter (fun i => decide (i ∈ S))).Perm S.toList := by
  apply List.perm_of_nodup_nodup_toFinset_eq
  · exact (List.nodup_finRange n).filter _
  · exact S.nodup_toList
  · simp [List.toFinset_filter, List.toFinset_finRange,
      Finset.filter_univ_mem, Finset.toList_toFinset]

/-- The rejected list has the dual `filter`/`map` characterisation: it is the
order-preserving filter of the universe of lifted-factor indices by
non-membership in `S`, mapped through `liftedFactor d`. -/
private theorem liftedSubsetRejectedList_eq_filter_map
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    liftedSubsetRejectedList d S =
      ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∉ S)).map
        (liftedFactor d) := by
  unfold liftedSubsetRejectedList liftedSubsetMask liftedFactor
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs, List.zip_map', List.filterMap_map]
  simp only [Function.comp_def]
  -- Convert `if p then none else some` into `if !p then some else none`.
  have hrewrite :
      (fun x : Fin d.liftedFactors.size =>
          if decide (x ∈ S) then (none : Option Hex.ZPoly)
          else some d.liftedFactors[x]) =
        fun x : Fin d.liftedFactors.size =>
          if decide (x ∉ S) then some d.liftedFactors[x] else none := by
    funext x
    by_cases hx : x ∈ S
    · simp [hx]
    · simp [hx]
  rw [hrewrite]
  exact List.filterMap_if_eq_map_filter
    (List.finRange d.liftedFactors.size) (fun i => decide (i ∉ S))
    (fun i => d.liftedFactors[i])

/-- Predicate capturing that `localFactors` is the order-preserving list of
lifted factors at the indices in `J`.  This is the invariant preserved by the
recursive recombination search: at every level the executable's running
`localFactors` is exactly the list of lifted factors at the remaining
unconsumed indices.

Used by the recursive coverage proof to connect the proof-side
`HenselSubsetCorrespondenceRest core d J target` to the executable list
threaded through `Hex.recombinationSearchModAux`. -/
def LiftedFactorListMatches (d : Hex.LiftData) (J : LiftedFactorSubset d)
    (localFactors : List Hex.ZPoly) : Prop :=
  localFactors =
    ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∈ J)).map
      (liftedFactor d)

/-- The matching predicate is equivalent to `localFactors = liftedSubsetSelectedList d J`,
the cleanest form for connecting to the executable recombination split API. -/
theorem LiftedFactorListMatches_iff_eq_liftedSubsetSelectedList
    (d : Hex.LiftData) (J : LiftedFactorSubset d)
    (localFactors : List Hex.ZPoly) :
    LiftedFactorListMatches d J localFactors ↔
      localFactors = liftedSubsetSelectedList d J := by
  unfold LiftedFactorListMatches
  rw [liftedSubsetSelectedList_eq_filter_map]

/-- Initial-state instance: the full lifted-factor list matches the universe
of indices.  This pairs with `henselSubsetCorrespondenceRest_initial` at the
start of the recursive coverage induction. -/
theorem LiftedFactorListMatches.univ (d : Hex.LiftData) :
    LiftedFactorListMatches d Finset.univ d.liftedFactors.toList := by
  unfold LiftedFactorListMatches liftedFactor
  have hxs : d.liftedFactors.toList =
      (List.finRange d.liftedFactors.size).map (fun i => d.liftedFactors[i]) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [List.getElem_finRange]
  rw [hxs]
  congr 1
  exact (List.filter_eq_self.mpr (by intro a _; simp)).symm

/-- Cardinality lemma: a matched list has length equal to `J.card`.  This is
the natural induction measure for the recursive coverage proof. -/
theorem LiftedFactorListMatches.length_eq_card
    {d : Hex.LiftData} {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    (h : LiftedFactorListMatches d J localFactors) :
    localFactors.length = J.card := by
  rw [h, List.length_map]
  rw [(finRange_filter_mem_perm_toList J).length_eq, Finset.length_toList]

/-- A matched `localFactors` is `Nodup` whenever `liftedFactor d` is injective
on the index set `J`.

Discharges the `hlocal_nodup` hypothesis of
`liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` and
`liftedFactorSubsetPartition_prefix_none`.  The `Set.InjOn` premise is a
Hensel-coprimality fact about the local factors of `d`: distinct lifted
factors are pairwise coprime, so when monic they are not equal as
polynomials.  Producing the injectivity witness from partition data (or
directly from `henselLiftData` invariants) is the caller's responsibility
in #4301; this shim covers only the pure list-level step. -/
theorem LiftedFactorListMatches.nodup_of_injOn
    {d : Hex.LiftData} {J : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    (h : LiftedFactorListMatches d J localFactors)
    (hinj : Set.InjOn (liftedFactor d) (J : Set (LiftedFactorIndex d))) :
    localFactors.Nodup := by
  rw [h]
  refine List.Nodup.map_on ?_ ((List.nodup_finRange _).filter _)
  intro x hx y hy hxy
  rw [List.mem_filter] at hx hy
  exact hinj (of_decide_eq_true hx.2) (of_decide_eq_true hy.2) hxy

/-- The rejected list of a subset `S` is exactly the selected list of the
complementary universe minus `S`.  This is the executable-side identity that
matches `liftedSubsetRejectedList d S` to `Finset.univ \ S`. -/
theorem liftedSubsetRejectedList_eq_liftedSubsetSelectedList_sdiff
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    liftedSubsetRejectedList d S = liftedSubsetSelectedList d (Finset.univ \ S) := by
  rw [liftedSubsetRejectedList_eq_filter_map, liftedSubsetSelectedList_eq_filter_map]
  congr 1
  apply List.filter_congr
  intro i _
  simp [Finset.mem_sdiff]

/-- Rejection-step instance: emitting `S` from the universal initial state
leaves the executable's running `localFactors` matched to `Finset.univ \ S`.
This is the universe-level case of the recursive invariant transition; the
general `J ↦ J \ S` step lives in the recursive coverage proof and uses this
lemma plus a partition-bridging lemma. -/
theorem LiftedFactorListMatches.rejected_of_subset
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    LiftedFactorListMatches d (Finset.univ \ S) (liftedSubsetRejectedList d S) := by
  rw [LiftedFactorListMatches_iff_eq_liftedSubsetSelectedList]
  exact liftedSubsetRejectedList_eq_liftedSubsetSelectedList_sdiff d S

/-- The order-preserving filter of `List.finRange n` by membership in a Finset
equals the sorted list of that Finset.  Two sorted lists with the same
multiset of elements are equal, and `filter` of a sorted list is sorted. -/
private theorem finRange_filter_eq_sort
    {n : Nat} (J : Finset (Fin n)) :
    (List.finRange n).filter (fun i => decide (i ∈ J)) = J.sort (· ≤ ·) := by
  classical
  apply List.Perm.eq_of_sortedLE
  · exact ((List.sortedLT_finRange n).pairwise.imp le_of_lt).filter _ |>.sortedLE
  · exact (J.sortedLT_sort).pairwise.imp le_of_lt |>.sortedLE
  · exact (finRange_filter_mem_perm_toList J).trans (J.sort_perm_toList (· ≤ ·)).symm

/-- The `head?` of the order-preserving filter of `List.finRange n` by
membership in a nonempty Finset `J` is `J.min'`.  Combined with the matching
predicate this identifies the head of `localFactors` with the lifted factor
at `J.min'`. -/
private theorem finRange_filter_head?_eq_min'
    {n : Nat} (J : Finset (Fin n)) (hne : J.Nonempty) :
    ((List.finRange n).filter (fun i => decide (i ∈ J))).head? =
      some (J.min' hne) := by
  classical
  rw [finRange_filter_eq_sort]
  have hpos : 0 < (J.sort (· ≤ ·)).length := by
    rw [Finset.length_sort]; exact hne.card_pos
  rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hpos]
  exact congrArg some Finset.sorted_zero_eq_min'

/-- Head identification for a non-empty matching state: the head of
`localFactors` is the lifted factor at `J.min'`.  Used by the recursive
coverage proof to connect the proof-side "first remaining index of `J`" to the
executable-side head of `localFactors`. -/
theorem LiftedFactorListMatches.head?_eq_liftedFactor_min'
    {d : Hex.LiftData} {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    (h : LiftedFactorListMatches d J localFactors) (hne : J.Nonempty) :
    localFactors.head? = some (liftedFactor d (J.min' hne)) := by
  rw [h, List.head?_map, finRange_filter_head?_eq_min' J hne]
  rfl

/-- The order-preserving filter of `List.finRange n` by membership in `J ∩ S`
equals the filter by `S` when `S ⊆ J`. Used to identify the selected sublist
of a matched `localFactors` with `liftedSubsetSelectedList d S`. -/
private theorem finRange_filter_mem_and_mem_eq_of_subset
    {n : Nat} {J S : Finset (Fin n)} (hSJ : S ⊆ J) :
    ((List.finRange n).filter fun i => decide (i ∈ J)).filter
        (fun i => decide (i ∈ S)) =
      (List.finRange n).filter fun i => decide (i ∈ S) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro i _
  by_cases hS : i ∈ S
  · simp [hS, hSJ hS]
  · simp [hS]

/-- Dual of `finRange_filter_mem_and_mem_eq_of_subset`: filtering by membership
in `J` then by non-membership in `S` (with `S ⊆ J`) is filtering by membership
in `J \ S`. -/
private theorem finRange_filter_mem_and_not_mem_eq_sdiff_of_subset
    {n : Nat} {J S : Finset (Fin n)} :
    ((List.finRange n).filter fun i => decide (i ∈ J)).filter
        (fun i => decide (i ∉ S)) =
      (List.finRange n).filter fun i => decide (i ∈ J \ S) := by
  rw [List.filter_filter]
  apply List.filter_congr
  intro i _
  by_cases hJ : i ∈ J
  · by_cases hS : i ∈ S
    · simp [hJ, hS, Finset.mem_sdiff]
    · simp [hJ, hS, Finset.mem_sdiff]
  · simp [hJ, Finset.mem_sdiff]

/-- Generalised matching transition: removing `S ⊆ J` from a matching state
yields a matching state for `J \ S` whose `localFactors` is
`liftedSubsetSelectedList d (J \ S)`.  This is the recursive invariant
transition used inside the recombination coverage proof. -/
theorem LiftedFactorListMatches.sdiff_of_subset
    {d : Hex.LiftData} {J S : LiftedFactorSubset d} :
    LiftedFactorListMatches d (J \ S)
      (liftedSubsetSelectedList d (J \ S)) :=
  (LiftedFactorListMatches_iff_eq_liftedSubsetSelectedList d (J \ S) _).mpr rfl

/-- Generalised partition lemma at the `subsetSplitsWithFirst` surface: for any
matching state and any `S ⊆ J` containing `J.min'`, the order-preserving
`(selected, rest)` partition of `localFactors` by `S` lies in
`subsetSplitsWithFirst localFactors`.

The selected component is `liftedSubsetSelectedList d S` (since `S ⊆ J`) and
the rest component is `liftedSubsetSelectedList d (J \ S)`. -/
theorem liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
    {d : Hex.LiftData} {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    (h : LiftedFactorListMatches d J localFactors)
    {S : LiftedFactorSubset d} (hSJ : S ⊆ J) (hne : J.Nonempty)
    (hmin : J.min' hne ∈ S) :
    (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) ∈
      Hex.subsetSplitsWithFirst localFactors := by
  classical
  -- Step 1: decompose `localFactors` as `head :: tail`.
  have hhead := h.head?_eq_liftedFactor_min' hne
  rcases hloc : localFactors with _ | ⟨head, tail⟩
  · rw [hloc] at hhead; simp at hhead
  rw [hloc] at hhead
  simp only [List.head?_cons, Option.some.injEq] at hhead
  -- `hhead : head = liftedFactor d (J.min' hne)`.
  -- Step 2: rewrite `localFactors` via the matching predicate.
  have hloc_eq : head :: tail =
      ((List.finRange d.liftedFactors.size).filter fun i => decide (i ∈ J)).map
        (liftedFactor d) := by
    rw [← hloc]; exact h
  -- Step 3: zip with the membership mask for `S`.
  set xs : List (Fin d.liftedFactors.size) :=
    (List.finRange d.liftedFactors.size).filter (fun i => decide (i ∈ J))
    with hxs_def
  have hloc_eq' : head :: tail = xs.map (liftedFactor d) := hloc_eq
  -- The mask paired with `xs` records membership in `S`.
  set bs : List Bool := xs.map (fun i => decide (i ∈ S))
  -- Step 4: the zip identifies the selected/rejected filterMaps.
  have hzip :
      (xs.map (liftedFactor d)).zip bs =
        xs.map (fun i => (liftedFactor d i, decide (i ∈ S))) := by
    rw [List.zip_map']
  -- Step 5: identify the selected filterMap with `liftedSubsetSelectedList d S`.
  have hsel :
      ((xs.map (liftedFactor d)).zip bs).filterMap
        (fun p => if p.2 then some p.1 else none) =
          liftedSubsetSelectedList d S := by
    rw [hzip, List.filterMap_map]
    simp only [Function.comp_def]
    rw [List.filterMap_if_eq_map_filter xs (fun i => decide (i ∈ S))
      (liftedFactor d)]
    rw [hxs_def, finRange_filter_mem_and_mem_eq_of_subset hSJ,
      ← liftedSubsetSelectedList_eq_filter_map]
  -- Step 6: identify the rejected filterMap with `liftedSubsetSelectedList d (J \ S)`.
  have hrej :
      ((xs.map (liftedFactor d)).zip bs).filterMap
        (fun p => if p.2 then none else some p.1) =
          liftedSubsetSelectedList d (J \ S) := by
    rw [hzip, List.filterMap_map]
    simp only [Function.comp_def]
    -- Convert `if p then none else some` into `if !p then some else none`.
    have hrewrite :
        (fun i : Fin d.liftedFactors.size =>
            if decide (i ∈ S) then (none : Option Hex.ZPoly)
            else some (liftedFactor d i)) =
          fun i => if decide (i ∉ S) then some (liftedFactor d i) else none := by
      funext i
      by_cases hi : i ∈ S
      · simp [hi]
      · simp [hi]
    rw [hrewrite, List.filterMap_if_eq_map_filter xs
      (fun i => decide (i ∉ S)) (liftedFactor d)]
    rw [hxs_def, finRange_filter_mem_and_not_mem_eq_sdiff_of_subset,
      ← liftedSubsetSelectedList_eq_filter_map]
  -- Step 7: show `bs = true :: bs'` since the head index `J.min' hne ∈ S`.
  have hxs_cons : ∃ ys, xs = (J.min' hne) :: ys := by
    have hhead_xs : xs.head? = some (J.min' hne) := by
      rw [hxs_def]; exact finRange_filter_head?_eq_min' J hne
    cases hxs_case : xs with
    | nil => rw [hxs_case] at hhead_xs; simp at hhead_xs
    | cons x ys =>
        rw [hxs_case] at hhead_xs
        simp only [List.head?_cons, Option.some.injEq] at hhead_xs
        exact ⟨ys, by rw [hhead_xs]⟩
  obtain ⟨ys, hxs_cons_eq⟩ := hxs_cons
  -- Step 8: invoke `subsetSplitsWithFirst_zip_filterMap_partition`.
  rw [hloc_eq', hxs_cons_eq, List.map_cons]
  have hbs_cons : bs = true :: ys.map (fun i => decide (i ∈ S)) := by
    show xs.map (fun i => decide (i ∈ S)) =
      true :: ys.map (fun i => decide (i ∈ S))
    rw [hxs_cons_eq, List.map_cons]
    congr 1
    simp [hmin]
  -- The selected/rejected filterMaps via the cons form.
  have hsel_cons :
      liftedSubsetSelectedList d S =
        ((liftedFactor d (J.min' hne) :: ys.map (liftedFactor d)).zip
            (true :: ys.map (fun i => decide (i ∈ S)))).filterMap
          (fun p => if p.2 then some p.1 else none) := by
    have := hsel
    rw [hxs_cons_eq, List.map_cons] at this
    rw [hbs_cons] at this
    exact this.symm
  have hrej_cons :
      liftedSubsetSelectedList d (J \ S) =
        ((liftedFactor d (J.min' hne) :: ys.map (liftedFactor d)).zip
            (true :: ys.map (fun i => decide (i ∈ S)))).filterMap
          (fun p => if p.2 then none else some p.1) := by
    have := hrej
    rw [hxs_cons_eq, List.map_cons] at this
    rw [hbs_cons] at this
    exact this.symm
  rw [hsel_cons, hrej_cons]
  have hys_len_eq : (ys.map (fun i => decide (i ∈ S))).length =
      (ys.map (liftedFactor d)).length := by simp
  exact subsetSplitsWithFirst_zip_filterMap_partition
    (liftedFactor d (J.min' hne))
    (ys.map (liftedFactor d))
    (ys.map (fun i => decide (i ∈ S)))
    hys_len_eq

/-- Filter of a `Nodup` list by membership in the `toFinset` of a Boolean-mask
`filterMap` equals the `filterMap` itself.  This is the key combinatorial step
in the converse to `liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches`:
the executable enumeration recovers an index-level Finset from a polynomial-
level mask. -/
private theorem List.nodup_filter_mem_toFinset_zip_filterMap_selected
    {α : Type*} [DecidableEq α]
    (xs : List α) (bs : List Bool) (hxs : xs.Nodup) (hlen : bs.length = xs.length) :
    xs.filter (fun x => decide (x ∈ ((xs.zip bs).filterMap
        (fun p => if p.2 then some p.1 else none)).toFinset)) =
      (xs.zip bs).filterMap (fun p => if p.2 then some p.1 else none) := by
  induction xs generalizing bs with
  | nil => simp
  | cons x xs ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hxs).2
          have hx_notin : x ∉ xs := (List.nodup_cons.mp hxs).1
          set tailSelected : List α :=
            (xs.zip bs).filterMap (fun p => if p.2 then some p.1 else none)
            with htailSelected_def
          cases b with
          | true =>
              -- Both sides reduce to forms involving `x :: tailSelected` via
              -- definitional reduction of `filterMap` on `(x, true) :: ...`.
              show (x :: xs).filter
                  (fun y => decide (y ∈ (x :: tailSelected).toFinset)) =
                x :: tailSelected
              rw [show (x :: xs).filter
                      (fun y => decide (y ∈ (x :: tailSelected).toFinset)) =
                    x :: xs.filter
                      (fun y => decide (y ∈ (x :: tailSelected).toFinset)) from
                List.filter_cons_of_pos (by simp)]
              congr 1
              -- For y ∈ xs, y ≠ x, so membership reduces to tailSelected.toFinset.
              have hcongr : ∀ y ∈ xs,
                  decide (y ∈ (x :: tailSelected).toFinset) =
                    decide (y ∈ tailSelected.toFinset) := by
                intro y hy
                have hyne : y ≠ x := fun heq => hx_notin (heq ▸ hy)
                simp [List.toFinset_cons, hyne]
              rw [List.filter_congr hcongr]
              exact ih bs hxs_nodup hlen
          | false =>
              -- `filterMap` on `(x, false) :: ...` drops x; both sides reduce
              -- to `tailSelected` definitionally.
              show (x :: xs).filter
                  (fun y => decide (y ∈ tailSelected.toFinset)) = tailSelected
              have hx_notin_tail : x ∉ tailSelected := by
                rw [htailSelected_def, List.mem_filterMap]
                rintro ⟨⟨a, b'⟩, hp_mem, hp_eq⟩
                have ha_xs : a ∈ xs := (List.of_mem_zip hp_mem).1
                cases b' with
                | true =>
                    simp only [if_true, Option.some.injEq] at hp_eq
                    rw [← hp_eq] at hx_notin
                    exact hx_notin ha_xs
                | false => simp at hp_eq
              rw [show (x :: xs).filter
                      (fun y => decide (y ∈ tailSelected.toFinset)) =
                    xs.filter
                      (fun y => decide (y ∈ tailSelected.toFinset)) from
                List.filter_cons_of_neg (by simp [hx_notin_tail])]
              exact ih bs hxs_nodup hlen

/-- Dual of `nodup_filter_mem_toFinset_zip_filterMap_selected`: filtering by
non-membership in the selected `toFinset` recovers the rest filterMap. -/
private theorem List.nodup_filter_not_mem_toFinset_zip_filterMap_rest
    {α : Type*} [DecidableEq α]
    (xs : List α) (bs : List Bool) (hxs : xs.Nodup) (hlen : bs.length = xs.length) :
    xs.filter (fun x => decide (x ∉ ((xs.zip bs).filterMap
        (fun p => if p.2 then some p.1 else none)).toFinset)) =
      (xs.zip bs).filterMap (fun p => if p.2 then none else some p.1) := by
  induction xs generalizing bs with
  | nil => simp
  | cons x xs ih =>
      cases bs with
      | nil => simp at hlen
      | cons b bs =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hxs_nodup : xs.Nodup := (List.nodup_cons.mp hxs).2
          have hx_notin : x ∉ xs := (List.nodup_cons.mp hxs).1
          set tailSelected : List α :=
            (xs.zip bs).filterMap (fun p => if p.2 then some p.1 else none)
            with htailSelected_def
          set tailRest : List α :=
            (xs.zip bs).filterMap (fun p => if p.2 then none else some p.1)
          cases b with
          | true =>
              -- selected at (x, true) = some x, rest at (x, true) = none.
              show (x :: xs).filter
                  (fun y => decide (y ∉ (x :: tailSelected).toFinset)) = tailRest
              rw [show (x :: xs).filter
                      (fun y => decide (y ∉ (x :: tailSelected).toFinset)) =
                    xs.filter
                      (fun y => decide (y ∉ (x :: tailSelected).toFinset)) from
                List.filter_cons_of_neg (by simp)]
              have hcongr : ∀ y ∈ xs,
                  decide (y ∉ (x :: tailSelected).toFinset) =
                    decide (y ∉ tailSelected.toFinset) := by
                intro y hy
                have hyne : y ≠ x := fun heq => hx_notin (heq ▸ hy)
                simp [List.toFinset_cons, hyne]
              rw [List.filter_congr hcongr]
              exact ih bs hxs_nodup hlen
          | false =>
              -- selected at (x, false) = none, rest at (x, false) = some x.
              show (x :: xs).filter
                  (fun y => decide (y ∉ tailSelected.toFinset)) = x :: tailRest
              have hx_notin_tail : x ∉ tailSelected := by
                rw [htailSelected_def, List.mem_filterMap]
                rintro ⟨⟨a, b'⟩, hp_mem, hp_eq⟩
                have ha_xs : a ∈ xs := (List.of_mem_zip hp_mem).1
                cases b' with
                | true =>
                    simp only [if_true, Option.some.injEq] at hp_eq
                    rw [← hp_eq] at hx_notin
                    exact hx_notin ha_xs
                | false => simp at hp_eq
              rw [show (x :: xs).filter
                      (fun y => decide (y ∉ tailSelected.toFinset)) =
                    x :: xs.filter
                      (fun y => decide (y ∉ tailSelected.toFinset)) from
                List.filter_cons_of_pos (by simp [hx_notin_tail])]
              congr 1
              exact ih bs hxs_nodup hlen

/-- Mask-to-subset lemma: given a Boolean mask of matching length over the
tail of a matched `localFactors` list, there is a `LiftedFactorSubset d`
(containing `J.min'` and contained in `J`) whose `(selected, rest)` list
partition equals the matched-list mask partition.  The natural converse of
`liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches`, used to recover a
proof-side lifted-factor subset from an arbitrary executable split. -/
theorem liftedSubsetSelectedList_eq_mask_partition_of_matches
    {d : Hex.LiftData} {J : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hne : J.Nonempty)
    {head : Hex.ZPoly} {tail : List Hex.ZPoly}
    (hloc : localFactors = head :: tail)
    (mask : List Bool) (hmask_len : mask.length = tail.length) :
    ∃ T : LiftedFactorSubset d,
      T ⊆ J ∧ J.min' hne ∈ T ∧
      liftedSubsetSelectedList d T =
        head :: (tail.zip mask).filterMap (fun p => if p.2 then some p.1 else none) ∧
      liftedSubsetSelectedList d (J \ T) =
        (tail.zip mask).filterMap (fun p => if p.2 then none else some p.1) := by
  classical
  -- The J-filter index list, starting at J.min'.
  set xs : List (LiftedFactorIndex d) :=
    (List.finRange d.liftedFactors.size).filter (fun i => decide (i ∈ J)) with hxs_def
  have hxs_head : xs.head? = some (J.min' hne) := finRange_filter_head?_eq_min' J hne
  obtain ⟨ys, hxs_eq⟩ : ∃ ys, xs = (J.min' hne) :: ys := by
    cases hxs_case : xs with
    | nil => rw [hxs_case] at hxs_head; simp at hxs_head
    | cons x ys =>
        rw [hxs_case] at hxs_head
        simp only [List.head?_cons, Option.some.injEq] at hxs_head
        exact ⟨ys, by rw [hxs_head]⟩
  -- xs is Nodup, hence ys is Nodup and J.min' ∉ ys.
  have hxs_nodup : xs.Nodup := (List.nodup_finRange _).filter _
  rw [hxs_eq] at hxs_nodup
  have hys_nodup : ys.Nodup := (List.nodup_cons.mp hxs_nodup).2
  have hmin_notin_ys : J.min' hne ∉ ys := (List.nodup_cons.mp hxs_nodup).1
  -- Identify head and tail via the matching predicate.
  have hloc_via_xs : localFactors = xs.map (liftedFactor d) := hmatches
  rw [hxs_eq, List.map_cons] at hloc_via_xs
  rw [hloc] at hloc_via_xs
  obtain ⟨hhead_eq, htail_eq⟩ :
      head = liftedFactor d (J.min' hne) ∧ tail = ys.map (liftedFactor d) := by
    simp only [List.cons.injEq] at hloc_via_xs
    exact hloc_via_xs
  -- mask length matches ys length.
  have hys_mask_len : mask.length = ys.length := by
    rw [hmask_len, htail_eq, List.length_map]
  -- The tail-selected index list and T.
  set tailSelected : List (LiftedFactorIndex d) :=
    (ys.zip mask).filterMap (fun p => if p.2 then some p.1 else none)
    with htailSelected_def
  set T : LiftedFactorSubset d :=
    insert (J.min' hne) tailSelected.toFinset with hT_def
  -- tailSelected is a sublist of ys.
  have htailSelected_subset_ys : ∀ x ∈ tailSelected, x ∈ ys := by
    intro x hx
    rw [htailSelected_def, List.mem_filterMap] at hx
    obtain ⟨⟨a, b⟩, hp_mem, hp_eq⟩ := hx
    have ha_ys : a ∈ ys := (List.of_mem_zip hp_mem).1
    cases b with
    | true => simp only [if_true, Option.some.injEq] at hp_eq; rw [← hp_eq]; exact ha_ys
    | false => simp at hp_eq
  -- T ⊆ J.
  have hTJ : T ⊆ J := by
    intro x hx
    rw [hT_def] at hx
    rcases Finset.mem_insert.mp hx with hmin | htf
    · rw [hmin]; exact J.min'_mem hne
    · rw [List.mem_toFinset] at htf
      have hx_ys : x ∈ ys := htailSelected_subset_ys x htf
      have hx_xs : x ∈ xs := by rw [hxs_eq]; exact List.mem_cons_of_mem _ hx_ys
      rw [hxs_def, List.mem_filter] at hx_xs
      exact of_decide_eq_true hx_xs.2
  -- J.min' ∈ T.
  have hmin_in_T : J.min' hne ∈ T := by
    rw [hT_def]; exact Finset.mem_insert_self _ _
  refine ⟨T, hTJ, hmin_in_T, ?_, ?_⟩
  · -- Selected list equality.
    rw [liftedSubsetSelectedList_eq_filter_map]
    -- Reduce (finRange n).filter (· ∈ T) to xs.filter (· ∈ T) via T ⊆ J.
    rw [show (List.finRange d.liftedFactors.size).filter (fun i => decide (i ∈ T)) =
            xs.filter (fun i => decide (i ∈ T)) from by
      rw [hxs_def]; exact (finRange_filter_mem_and_mem_eq_of_subset hTJ).symm]
    rw [hxs_eq]
    rw [show (J.min' hne :: ys).filter (fun i => decide (i ∈ T)) =
            J.min' hne :: ys.filter (fun i => decide (i ∈ T)) from
      List.filter_cons_of_pos (by simp [hmin_in_T])]
    rw [List.map_cons]
    rw [hhead_eq, htail_eq]
    congr 1
    -- (ys.filter (· ∈ T)).map (liftedFactor d) =
    --   ((ys.map (liftedFactor d)).zip mask).filterMap selected
    have hys_filter_eq :
        ys.filter (fun i => decide (i ∈ T)) =
          ys.filter (fun i => decide (i ∈ tailSelected.toFinset)) := by
      apply List.filter_congr
      intro y hy
      have hyne : y ≠ J.min' hne := fun heq => hmin_notin_ys (heq ▸ hy)
      simp [hT_def, hyne]
    rw [hys_filter_eq]
    rw [List.nodup_filter_mem_toFinset_zip_filterMap_selected ys mask hys_nodup
      hys_mask_len]
    rw [List.zip_map_left, List.filterMap_map, List.map_filterMap]
    congr 1
    funext p
    obtain ⟨a, b⟩ := p
    cases b <;> rfl
  · -- Rest list equality.
    rw [liftedSubsetSelectedList_eq_filter_map]
    rw [show ((List.finRange d.liftedFactors.size).filter
            (fun i => decide (i ∈ J \ T))) =
            xs.filter (fun i => decide (i ∉ T)) from by
      rw [hxs_def]
      exact (finRange_filter_mem_and_not_mem_eq_sdiff_of_subset
        (J := J) (S := T)).symm]
    rw [hxs_eq]
    rw [show (J.min' hne :: ys).filter (fun i => decide (i ∉ T)) =
            ys.filter (fun i => decide (i ∉ T)) from
      List.filter_cons_of_neg (by simp [hmin_in_T])]
    rw [htail_eq]
    have hys_filter_eq :
        ys.filter (fun i => decide (i ∉ T)) =
          ys.filter (fun i => decide (i ∉ tailSelected.toFinset)) := by
      apply List.filter_congr
      intro y hy
      have hyne : y ≠ J.min' hne := fun heq => hmin_notin_ys (heq ▸ hy)
      simp [hT_def, hyne]
    rw [hys_filter_eq]
    rw [List.nodup_filter_not_mem_toFinset_zip_filterMap_rest ys mask hys_nodup
      hys_mask_len]
    rw [List.zip_map_left, List.filterMap_map, List.map_filterMap]
    congr 1
    funext p
    obtain ⟨a, b⟩ := p
    cases b <;> rfl

/-- Structural enumeration-order content of `Hex.subsetSplits` on a `Nodup`
input: if the `mask_S`-induced split sits at the boundary `pre ++ _ :: suffix`
and the `mask_T`-induced split sits somewhere inside `pre`, then `mask_S` has
a `true` at some position where `mask_T` is `false`.

The `Nodup` precondition rules out the duplicate-element ambiguity where a
mask's induced split happens to land in the `false`-branch image of an
inductive step despite the mask's head bit being `true`. Once duplicates are
excluded, the cons step has exactly four sub-cases on the head bits
`(mask_S.head, mask_T.head)`: `(true, false)` yields `i = 0` directly,
`(false, true)` is structurally impossible because `mask_T`'s split lands in
the second half of `Hex.subsetSplits (x :: xs')` (after `mask_S`'s split),
and the head-matching cases recurse into the tail.

Used by the matched-state prefix-with-bit-difference lemma
`liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` after promoting the
matched J-filter index list (which is `Nodup`) into scope. -/
private theorem subsetSplits_prefix_exists_bit_diff_aux
    {xs : List Hex.ZPoly} (hxs_nodup : xs.Nodup)
    {mask_S mask_T : List Bool}
    (hSlen : mask_S.length = xs.length)
    (hTlen : mask_T.length = xs.length)
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hsplits :
      Hex.subsetSplits xs =
        pre ++
          ((xs.zip mask_S).filterMap (fun p => if p.2 then some p.1 else none),
           (xs.zip mask_S).filterMap (fun p => if p.2 then none else some p.1))
            :: suffix)
    (hT_in_pre :
      ((xs.zip mask_T).filterMap (fun p => if p.2 then some p.1 else none),
       (xs.zip mask_T).filterMap (fun p => if p.2 then none else some p.1))
         ∈ pre) :
    ∃ i, ∃ hi : i < xs.length,
      mask_T[i]'(hTlen ▸ hi) = false ∧
      mask_S[i]'(hSlen ▸ hi) = true := by
  induction xs generalizing mask_S mask_T pre suffix with
  | nil =>
      -- Base case: subsetSplits [] = [([], [])], so pre = [] and hT_in_pre is False.
      cases mask_S with
      | nil =>
        cases mask_T with
        | nil =>
          -- hsplits : [([], [])] = pre ++ ([], []) :: suffix; derive pre = []
          have hlen := congrArg List.length hsplits
          simp [Hex.subsetSplits, List.length_append, List.length_cons] at hlen
          have hpre_nil : pre = [] := List.length_eq_zero_iff.mp (by omega)
          subst hpre_nil
          simp at hT_in_pre
        | cons => simp at hTlen
      | cons => simp at hSlen
  | cons x xs' ih =>
      have hx_notin : x ∉ xs' := (List.nodup_cons.mp hxs_nodup).1
      have hxs'_nodup : xs'.Nodup := (List.nodup_cons.mp hxs_nodup).2
      cases mask_S with
      | nil => simp at hSlen
      | cons bS msS =>
        cases mask_T with
        | nil => simp at hTlen
        | cons bT msT =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hSlen hTlen
          -- L_false and L_true are the two halves of subsetSplits (x :: xs').
          set L_false :=
            (Hex.subsetSplits xs').map (fun s => (s.1, x :: s.2)) with hLfalse_def
          set L_true :=
            (Hex.subsetSplits xs').map (fun s => (x :: s.1, s.2)) with hLtrue_def
          have hsplits' : Hex.subsetSplits (x :: xs') = L_false ++ L_true := by
            show (let rest := Hex.subsetSplits xs';
                  rest.map (fun split => (split.1, x :: split.2)) ++
                    rest.map (fun split => (x :: split.1, split.2))) = _
            rfl
          rw [hsplits'] at hsplits
          -- Abbreviate tail-mask filterMaps for S and T.
          set tailSel_S : List Hex.ZPoly :=
            (xs'.zip msS).filterMap (fun p => if p.2 then some p.1 else none)
            with htailSel_S_def
          set tailRest_S : List Hex.ZPoly :=
            (xs'.zip msS).filterMap (fun p => if p.2 then none else some p.1)
            with htailRest_S_def
          set tailSel_T : List Hex.ZPoly :=
            (xs'.zip msT).filterMap (fun p => if p.2 then some p.1 else none)
            with htailSel_T_def
          set tailRest_T : List Hex.ZPoly :=
            (xs'.zip msT).filterMap (fun p => if p.2 then none else some p.1)
            with htailRest_T_def
          -- The tail-induced split of xs' under msS / msT.
          have htailSplit_S_mem : (tailSel_S, tailRest_S) ∈ Hex.subsetSplits xs' :=
            subsetSplits_zip_filterMap_partition xs' msS hSlen
          have htailSplit_T_mem : (tailSel_T, tailRest_T) ∈ Hex.subsetSplits xs' :=
            subsetSplits_zip_filterMap_partition xs' msT hTlen
          -- Lemma: with `x ∉ xs'`, no L_false entry has its selected starting
          -- with `x`, and no L_true entry has its rest starting with `x`.
          -- Lemma: with `x ∉ xs'`, no L_false entry has selected starting with `x`,
          -- and no L_true entry has rest starting with `x`. Used to commit to a
          -- specific half based on the head bit of mask_S / mask_T.
          have hx_notin_split_sel :
              ∀ {a b : List Hex.ZPoly}, (a, b) ∈ Hex.subsetSplits xs' → x ∉ a := by
            intro a b hab hxa
            obtain ⟨m, hmlen, hsel_eq, _⟩ := subsetSplits_mem_exists_mask hab
            rw [hsel_eq, List.mem_filterMap] at hxa
            obtain ⟨⟨a', b'⟩, hpair_mem, hpair_eq⟩ := hxa
            have hax' : a' ∈ xs' := (List.of_mem_zip hpair_mem).1
            cases b' with
            | true =>
                simp at hpair_eq
                exact hx_notin (hpair_eq ▸ hax')
            | false => simp at hpair_eq
          have hx_notin_split_rest :
              ∀ {a b : List Hex.ZPoly}, (a, b) ∈ Hex.subsetSplits xs' → x ∉ b := by
            intro a b hab hxb
            obtain ⟨m, hmlen, _, hrest_eq⟩ := subsetSplits_mem_exists_mask hab
            rw [hrest_eq, List.mem_filterMap] at hxb
            obtain ⟨⟨a', b'⟩, hpair_mem, hpair_eq⟩ := hxb
            have hax' : a' ∈ xs' := (List.of_mem_zip hpair_mem).1
            cases b' with
            | true => simp at hpair_eq
            | false =>
                simp at hpair_eq
                exact hx_notin (hpair_eq ▸ hax')
          -- Simplification helpers for evaluating the cons step of zip + filterMap
          -- once the head bit is fixed.
          have eval_sel_false : ∀ (m : List Bool),
              ((x :: xs').zip (false :: m)).filterMap
                  (fun p => if p.2 then some p.1 else none) =
                (xs'.zip m).filterMap (fun p => if p.2 then some p.1 else none) := by
            intro m
            simp [List.zip_cons_cons]
          have eval_rest_false : ∀ (m : List Bool),
              ((x :: xs').zip (false :: m)).filterMap
                  (fun p => if p.2 then none else some p.1) =
                x :: (xs'.zip m).filterMap (fun p => if p.2 then none else some p.1) := by
            intro m
            simp [List.zip_cons_cons]
          have eval_sel_true : ∀ (m : List Bool),
              ((x :: xs').zip (true :: m)).filterMap
                  (fun p => if p.2 then some p.1 else none) =
                x :: (xs'.zip m).filterMap (fun p => if p.2 then some p.1 else none) := by
            intro m
            simp [List.zip_cons_cons]
          have eval_rest_true : ∀ (m : List Bool),
              ((x :: xs').zip (true :: m)).filterMap
                  (fun p => if p.2 then none else some p.1) =
                (xs'.zip m).filterMap (fun p => if p.2 then none else some p.1) := by
            intro m
            simp [List.zip_cons_cons]
          -- Case-split on the head bits.
          cases bS with
          | false =>
            rw [eval_sel_false, eval_rest_false] at hsplits
            -- Shape: split_S = (tailSel_S, x :: tailRest_S). Show split_S ∉ L_true.
            have hsplitS_notin_Ltrue : (tailSel_S, x :: tailRest_S) ∉ L_true := by
              intro h
              obtain ⟨⟨a, _⟩, hab, hab_eq⟩ := List.mem_map.mp h
              simp only [Prod.mk.injEq] at hab_eq
              obtain ⟨ha, _⟩ := hab_eq
              exact hx_notin_split_sel htailSplit_S_mem (ha ▸ List.mem_cons_self)
            cases bT with
            | false =>
              -- (false, false): both splits in L_false.
              rw [eval_sel_false, eval_rest_false] at hT_in_pre
              -- Decompose hsplits.
              rcases (List.append_eq_append_iff).mp hsplits with
                ⟨e, _, hLt_eq⟩ | ⟨e, hLf_eq, hsuff_eq⟩
              · -- Case 1: split_S ∈ L_true. Contradiction.
                exfalso
                have : (tailSel_S, x :: tailRest_S) ∈ L_true := by
                  rw [hLt_eq]; exact List.mem_append_right _ List.mem_cons_self
                exact hsplitS_notin_Ltrue this
              · -- Case 2: L_false = pre ++ e ∧ split_S :: suffix = e ++ L_true.
                -- Extract decomposition of subsetSplits xs' from L_false = (...).map f.
                rw [hLfalse_def] at hLf_eq
                obtain ⟨preIdx, suffIdx, hsplitsXs', hpreIdx_eq, hsuffIdx_eq⟩ :=
                  List.map_eq_append_iff.mp hLf_eq
                cases suffIdx with
                | nil =>
                  exfalso
                  simp only [List.map_nil] at hsuffIdx_eq
                  subst hsuffIdx_eq
                  simp only [List.nil_append] at hsuff_eq
                  have : (tailSel_S, x :: tailRest_S) ∈ L_true := by
                    rw [← hsuff_eq]; exact List.mem_cons_self
                  exact hsplitS_notin_Ltrue this
                | cons headIdx tailIdx =>
                  simp only [List.map_cons] at hsuffIdx_eq
                  subst hsuffIdx_eq
                  -- hsuff_eq : split_S :: suffix =
                  --   (headIdx.1, x :: headIdx.2) :: tailIdx.map f ++ L_true
                  rw [List.cons_append] at hsuff_eq
                  injection hsuff_eq with hsplit_eq _hsuffix_eq
                  -- hsplit_eq : (tailSel_S, x :: tailRest_S) = (headIdx.1, x :: headIdx.2)
                  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hsplit_eq
                  obtain ⟨hsel_S_eq, hrest_S_eq⟩ := hsplit_eq
                  -- Reconstruct: headIdx = (tailSel_S, tailRest_S).
                  obtain ⟨headSel, headRest⟩ := headIdx
                  simp only at hsel_S_eq hrest_S_eq
                  subst hsel_S_eq; subst hrest_S_eq
                  -- Now: hsplitsXs' : subsetSplits xs' = preIdx ++ (tailSel_S, tailRest_S) :: tailIdx
                  -- Need: (tailSel_T, tailRest_T) ∈ preIdx (from split_T ∈ pre).
                  have hsplitT_in_preIdx : (tailSel_T, tailRest_T) ∈ preIdx := by
                    rw [← hpreIdx_eq] at hT_in_pre
                    obtain ⟨⟨a, b⟩, hab, hab_eq⟩ := List.mem_map.mp hT_in_pre
                    simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hab_eq
                    obtain ⟨ha, hb⟩ := hab_eq
                    convert hab
                    · exact ha.symm
                    · exact hb.symm
                  -- Apply IH (using simped length hypotheses).
                  have hSlen' : msS.length = xs'.length := by simpa using hSlen
                  have hTlen' : msT.length = xs'.length := by simpa using hTlen
                  obtain ⟨i', hi', hmsT_i', hmsS_i'⟩ :=
                    ih hxs'_nodup hSlen' hTlen' hsplitsXs' hsplitT_in_preIdx
                  -- Translate to mask_S = false :: msS, mask_T = false :: msT.
                  refine ⟨i' + 1, by simp; omega, ?_, ?_⟩
                  · simp only [List.getElem_cons_succ]; exact hmsT_i'
                  · simp only [List.getElem_cons_succ]; exact hmsS_i'
            | true =>
              -- (false, true): impossible with x ∉ xs'.
              rw [eval_sel_true, eval_rest_true] at hT_in_pre
              exfalso
              -- Shape facts: split_S ∉ L_true (rest starts with x; L_true rests don't).
              have hsplitS_notin_Ltrue :
                  (tailSel_S, x :: tailRest_S) ∉ L_true := by
                intro h
                obtain ⟨⟨a, b⟩, hab, hab_eq⟩ := List.mem_map.mp h
                simp only [Prod.mk.injEq] at hab_eq
                obtain ⟨_, hb⟩ := hab_eq
                have hxb : x ∈ b := hb ▸ List.mem_cons_self
                exact hx_notin_split_rest hab hxb
              have hsplitT_notin_Lfalse :
                  (x :: tailSel_T, tailRest_T) ∉ L_false := by
                intro h
                obtain ⟨⟨a, b⟩, hab, hab_eq⟩ := List.mem_map.mp h
                simp only [Prod.mk.injEq] at hab_eq
                obtain ⟨ha, _⟩ := hab_eq
                have hxa : x ∈ a := ha ▸ List.mem_cons_self
                exact hx_notin_split_sel hab hxa
              -- Decompose hsplits via List.append_eq_append_iff.
              -- For L_false ++ L_true = pre ++ split_S :: suffix, the two cases are:
              -- (1) ∃ e, pre = L_false ++ e ∧ L_true = e ++ split_S :: suffix. (pre extends past L_false)
              -- (2) ∃ e, L_false = pre ++ e ∧ split_S :: suffix = e ++ L_true. (pre is prefix of L_false)
              rcases (List.append_eq_append_iff).mp hsplits with
                ⟨e, _, hLt_eq⟩ | ⟨e, hLf_eq, _⟩
              · -- Case 1: split_S ∈ L_true. Contradiction.
                have hsplitS_in_Ltrue : (tailSel_S, x :: tailRest_S) ∈ L_true := by
                  rw [hLt_eq]
                  exact List.mem_append_right _ (List.mem_cons_self)
                exact hsplitS_notin_Ltrue hsplitS_in_Ltrue
              · -- Case 2: pre ⊆ L_false; split_T ∈ pre ⊆ L_false. Contradiction.
                have hsplitT_in_Lfalse : (x :: tailSel_T, tailRest_T) ∈ L_false := by
                  rw [hLf_eq]; exact List.mem_append_left _ hT_in_pre
                exact hsplitT_notin_Lfalse hsplitT_in_Lfalse
          | true =>
            rw [eval_sel_true, eval_rest_true] at hsplits
            cases bT with
            | false =>
              -- (true, false): i = 0 works.
              refine ⟨0, by simp, ?_, ?_⟩ <;> rfl
            | true =>
              -- (true, true): both splits in L_true. Recurse.
              rw [eval_sel_true, eval_rest_true] at hT_in_pre
              -- Shape: split_T = (x :: tailSel_T, tailRest_T). Show split_T ∉ L_false.
              have hsplitT_notin_Lfalse : (x :: tailSel_T, tailRest_T) ∉ L_false := by
                intro h
                obtain ⟨⟨a, _⟩, hab, hab_eq⟩ := List.mem_map.mp h
                simp only [Prod.mk.injEq] at hab_eq
                obtain ⟨ha, _⟩ := hab_eq
                exact hx_notin_split_sel hab (ha ▸ List.mem_cons_self)
              -- Decompose hsplits.
              rcases (List.append_eq_append_iff).mp hsplits with
                ⟨e, hpre_eq, hLt_eq⟩ | ⟨e, hLf_eq, _hsuff_eq⟩
              · -- Case 1: pre = L_false ++ e_pre, L_true = e_pre ++ split_S :: suffix.
                rw [hLtrue_def] at hLt_eq
                obtain ⟨preIdx, suffIdx, hsplitsXs', hpreIdx_eq, hsuffIdx_eq⟩ :=
                  List.map_eq_append_iff.mp hLt_eq
                cases suffIdx with
                | nil =>
                  exfalso
                  simp only [List.map_nil] at hsuffIdx_eq
                  exact List.cons_ne_nil _ _ hsuffIdx_eq.symm
                | cons headIdx tailIdx =>
                  simp only [List.map_cons] at hsuffIdx_eq
                  injection hsuffIdx_eq with hsplit_eq _hsuffix_eq
                  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hsplit_eq
                  obtain ⟨hsel_S_eq, hrest_S_eq⟩ := hsplit_eq
                  obtain ⟨headSel, headRest⟩ := headIdx
                  simp only at hsel_S_eq hrest_S_eq
                  subst hsel_S_eq; subst hrest_S_eq
                  -- Now hsplitsXs' : subsetSplits xs' = preIdx ++ (tailSel_S, tailRest_S) :: tailIdx
                  have hsplitT_in_preIdx : (tailSel_T, tailRest_T) ∈ preIdx := by
                    rw [hpre_eq] at hT_in_pre
                    rw [List.mem_append] at hT_in_pre
                    rcases hT_in_pre with hLf | hE
                    · exact (hsplitT_notin_Lfalse hLf).elim
                    · rw [← hpreIdx_eq] at hE
                      obtain ⟨⟨a, b⟩, hab, hab_eq⟩ := List.mem_map.mp hE
                      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hab_eq
                      obtain ⟨ha, hb⟩ := hab_eq
                      convert hab
                      · exact ha.symm
                      · exact hb.symm
                  have hSlen' : msS.length = xs'.length := by simpa using hSlen
                  have hTlen' : msT.length = xs'.length := by simpa using hTlen
                  obtain ⟨i', hi', hmsT_i', hmsS_i'⟩ :=
                    ih hxs'_nodup hSlen' hTlen' hsplitsXs' hsplitT_in_preIdx
                  refine ⟨i' + 1, by simp; omega, ?_, ?_⟩
                  · simp only [List.getElem_cons_succ]; exact hmsT_i'
                  · simp only [List.getElem_cons_succ]; exact hmsS_i'
              · -- Case 2: L_false = pre ++ e, split_T ∈ pre ⊆ L_false. Contradiction.
                exfalso
                have hsplitT_in_Lfalse : (x :: tailSel_T, tailRest_T) ∈ L_false := by
                  rw [hLf_eq]; exact List.mem_append_left _ hT_in_pre
                exact hsplitT_notin_Lfalse hsplitT_in_Lfalse

/-- Prefix characterization at the matched-state `subsetSplitsWithFirst`
surface: given an arbitrary executable split `split ∈ pre` appearing before a
chosen matched `S`-split in `Hex.subsetSplitsWithFirst localFactors`, there is
a proof-side lifted-factor subset `T ⊆ J` containing `J.min'` whose
order-preserving `(selected, rest)` partition equals `split`.

Combines the executable-enumeration mask converse
`subsetSplitsWithFirst_mem_exists_tail_mask` with the mask-to-subset lemma
`liftedSubsetSelectedList_eq_mask_partition_of_matches`. Used by the
prefix-none discharge in the recursive coverage proof.

The conclusion is independent of the `S`-side shape constraints (`S ⊆ J` and
`J.min' hne ∈ S`) that the caller typically has in scope: the prefix
characterization is a structural property of the executable enumeration. The
caller call site keeps those hypotheses for the suffix `(S, J \ S)` entry
itself, but does not need to thread them through this lemma. -/
theorem liftedSubsetSplit_prefix_mem_of_matches
    {d : Hex.LiftData} {J S : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hne : J.Nonempty)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix)
    {split : List Hex.ZPoly × List Hex.ZPoly} (hsplit : split ∈ pre) :
    ∃ T : LiftedFactorSubset d,
      T ⊆ J ∧ J.min' hne ∈ T ∧
      split = (liftedSubsetSelectedList d T,
               liftedSubsetSelectedList d (J \ T)) := by
  classical
  -- Step 1: lift `hsplit ∈ pre` to membership in the full enumeration.
  have hsplit_mem_all : split ∈ Hex.subsetSplitsWithFirst localFactors := by
    rw [hsplits]
    exact List.mem_append_left _ hsplit
  -- Step 2: decompose `localFactors` as `head :: tail` via the matching predicate.
  have hhead := hmatches.head?_eq_liftedFactor_min' hne
  rcases hloc : localFactors with _ | ⟨head, tail⟩
  · rw [hloc] at hhead; simp at hhead
  rw [hloc] at hsplit_mem_all
  -- Step 3: destructure the split prod.
  obtain ⟨ssel, srest⟩ := split
  -- Step 4: pull out a Boolean tail mask via the executable converse.
  obtain ⟨mask, hmask_len, hsel_eq, hrest_eq⟩ :=
    subsetSplitsWithFirst_mem_exists_tail_mask hsplit_mem_all
  -- Step 5: convert the mask back to a proof-side `LiftedFactorSubset` `T`.
  obtain ⟨T, hTJ, hmin_in_T, hT_sel, hT_rest⟩ :=
    liftedSubsetSelectedList_eq_mask_partition_of_matches
      hmatches hne hloc mask hmask_len
  refine ⟨T, hTJ, hmin_in_T, ?_⟩
  -- Step 6: chain the cons-form equalities to identify `split` with the
  -- `T`-selected/rest pair.
  rw [hsel_eq, hrest_eq, ← hT_sel, ← hT_rest]

/-- Canonical mask decomposition of a matched-state at its head index.

Given that `localFactors` matches `J` and `J` is nonempty, `localFactors`
decomposes as `liftedFactor d (J.min' hne) :: ys.map (liftedFactor d)` for
some `ys` contained in `J`. For any `S ⊆ J` containing `J.min' hne`, the
`(S, J \ S)` partition has the canonical mask form indexed by
`ys.map (· ∈ S)`. -/
private theorem LiftedFactorListMatches.exists_tail_indices
    {d : Hex.LiftData} {J : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hne : J.Nonempty) :
    ∃ (ys : List (LiftedFactorIndex d)),
      (∀ y ∈ ys, y ∈ J) ∧
      localFactors = liftedFactor d (J.min' hne) :: ys.map (liftedFactor d) ∧
      ∀ (S : LiftedFactorSubset d), S ⊆ J → J.min' hne ∈ S →
        liftedSubsetSelectedList d S =
          liftedFactor d (J.min' hne) ::
            ((ys.map (liftedFactor d)).zip
                (ys.map (fun i => decide (i ∈ S)))).filterMap
              (fun p => if p.2 then some p.1 else none) ∧
        liftedSubsetSelectedList d (J \ S) =
          ((ys.map (liftedFactor d)).zip
              (ys.map (fun i => decide (i ∈ S)))).filterMap
            (fun p => if p.2 then none else some p.1) := by
  classical
  -- Set up the J-filter index list and decompose at its head.
  set xsIdx : List (LiftedFactorIndex d) :=
    (List.finRange d.liftedFactors.size).filter (fun i => decide (i ∈ J))
    with hxsIdx_def
  have hxsIdx_head : xsIdx.head? = some (J.min' hne) :=
    finRange_filter_head?_eq_min' J hne
  obtain ⟨ys, hxsIdx_eq⟩ : ∃ ys, xsIdx = (J.min' hne) :: ys := by
    cases hxsIdx_case : xsIdx with
    | nil => rw [hxsIdx_case] at hxsIdx_head; simp at hxsIdx_head
    | cons x ys =>
        rw [hxsIdx_case] at hxsIdx_head
        simp only [List.head?_cons, Option.some.injEq] at hxsIdx_head
        exact ⟨ys, by rw [hxsIdx_head]⟩
  refine ⟨ys, ?_, ?_, ?_⟩
  · -- ∀ y ∈ ys, y ∈ J
    intro y hy
    have hy_xsIdx : y ∈ xsIdx := by rw [hxsIdx_eq]; exact List.mem_cons_of_mem _ hy
    rw [hxsIdx_def, List.mem_filter] at hy_xsIdx
    exact of_decide_eq_true hy_xsIdx.2
  · -- localFactors = head :: ys.map liftedFactor
    have : localFactors = xsIdx.map (liftedFactor d) := hmatches
    rw [hxsIdx_eq, List.map_cons] at this
    exact this
  · -- The S-partition canonical mask equations.
    intro S hSJ hmin
    -- Common computation: zip of two maps over the same list.
    have hzip :
        (ys.map (liftedFactor d)).zip (ys.map (fun i => decide (i ∈ S))) =
          ys.map (fun i => (liftedFactor d i, decide (i ∈ S))) := by
      rw [List.zip_map']
    refine ⟨?_, ?_⟩
    · -- liftedSubsetSelectedList d S = head :: filterMap selected
      rw [liftedSubsetSelectedList_eq_filter_map]
      rw [show (List.finRange d.liftedFactors.size).filter
              (fun i => decide (i ∈ S)) =
            xsIdx.filter (fun i => decide (i ∈ S)) from by
        rw [hxsIdx_def]
        exact (finRange_filter_mem_and_mem_eq_of_subset hSJ).symm]
      rw [hxsIdx_eq]
      rw [show (J.min' hne :: ys).filter (fun i => decide (i ∈ S)) =
              J.min' hne :: ys.filter (fun i => decide (i ∈ S)) from
        List.filter_cons_of_pos (by simp [hmin])]
      rw [List.map_cons]
      congr 1
      rw [hzip, List.filterMap_map]
      simp only [Function.comp_def]
      exact (List.filterMap_if_eq_map_filter ys
        (fun i => decide (i ∈ S)) (liftedFactor d)).symm
    · -- liftedSubsetSelectedList d (J \ S) = filterMap rest
      rw [liftedSubsetSelectedList_eq_filter_map]
      rw [show (List.finRange d.liftedFactors.size).filter
              (fun i => decide (i ∈ J \ S)) =
            xsIdx.filter (fun i => decide (i ∉ S)) from by
        rw [hxsIdx_def]
        exact (finRange_filter_mem_and_not_mem_eq_sdiff_of_subset
          (J := J) (S := S)).symm]
      rw [hxsIdx_eq]
      rw [show (J.min' hne :: ys).filter (fun i => decide (i ∉ S)) =
              ys.filter (fun i => decide (i ∉ S)) from
        List.filter_cons_of_neg (by simp [hmin])]
      rw [hzip, List.filterMap_map]
      simp only [Function.comp_def]
      have hrewrite :
          (fun i : LiftedFactorIndex d =>
              if decide (i ∈ S) then (none : Option Hex.ZPoly)
              else some (liftedFactor d i)) =
            fun i => if decide (i ∉ S) then some (liftedFactor d i) else none := by
        funext i
        by_cases hi : i ∈ S
        · simp [hi]
        · simp [hi]
      rw [hrewrite]
      exact (List.filterMap_if_eq_map_filter ys
        (fun i => decide (i ∉ S)) (liftedFactor d)).symm

/-- Strengthening of `liftedSubsetSplit_prefix_mem_of_matches`: when the
matched `localFactors` is `Nodup` and the boundary split is the canonical
`(S, J \ S)` partition, every prefix `split ∈ pre` admits a witness index
`i ∈ J ∩ S` that is **not** in the recovered subset `T`.

The `Nodup` hypothesis is required to lift the executable mask-level bit
difference (provided by `subsetSplits_prefix_exists_bit_diff_aux`) back to a
proof-side `LiftedFactorIndex d` difference, since `liftedFactor d` is
otherwise allowed to collide on distinct indices. Callers thread this
hypothesis from a Hensel-coprimality fact at the recombination call site
(`liftedFactor d` injective on the J-filter index list).

Used by the recursive coverage assembler for the prefix-none case: an
arbitrary executable split appearing before the `S`-split must miss at least
one of the `S`-indices, witnessing recombination-search progress. -/
theorem liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches
    {d : Hex.LiftData} {J S : LiftedFactorSubset d}
    {localFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hlocal_nodup : localFactors.Nodup)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix)
    {split : List Hex.ZPoly × List Hex.ZPoly} (hsplit : split ∈ pre) :
    ∃ (T : LiftedFactorSubset d),
      T ⊆ J ∧ J.min' hne ∈ T ∧
      split = (liftedSubsetSelectedList d T,
               liftedSubsetSelectedList d (J \ T)) ∧
      ∃ i ∈ J, i ∈ S ∧ i ∉ T := by
  classical
  -- Step 1: get T from the prefix-mem lemma.
  obtain ⟨T, hTJ, hmin_in_T, hsplit_eq⟩ :=
    liftedSubsetSplit_prefix_mem_of_matches hmatches hne hsplits hsplit
  refine ⟨T, hTJ, hmin_in_T, hsplit_eq, ?_⟩
  -- Step 2: decompose localFactors and obtain canonical mask equations.
  obtain ⟨ys, hys_in_J, hloc_eq, hS_eqs⟩ :=
    hmatches.exists_tail_indices hne
  obtain ⟨hS_sel_cons, hS_rest_eq⟩ := hS_eqs S hSJ hmin
  obtain ⟨hT_sel_cons, hT_rest_eq⟩ := hS_eqs T hTJ hmin_in_T
  -- Useful abbreviations.
  set head : Hex.ZPoly := liftedFactor d (J.min' hne)
  set tail : List Hex.ZPoly := ys.map (liftedFactor d)
  set mask_S : List Bool := ys.map (fun i => decide (i ∈ S)) with hmask_S_def
  set mask_T : List Bool := ys.map (fun i => decide (i ∈ T)) with hmask_T_def
  have hmask_S_len : mask_S.length = tail.length := by
    simp [hmask_S_def, tail]
  have hmask_T_len : mask_T.length = tail.length := by
    simp [hmask_T_def, tail]
  -- Tail Nodup (from hlocal_nodup).
  rw [hloc_eq] at hlocal_nodup
  have htail_nodup : tail.Nodup := (List.nodup_cons.mp hlocal_nodup).2
  -- Step 3: lift `hsplits` to a `subsetSplits tail` decomposition.
  have hsswf_eq :
      Hex.subsetSplitsWithFirst localFactors =
        (Hex.subsetSplits tail).map (fun s => (head :: s.1, s.2)) := by
    rw [hloc_eq]
    show (Hex.subsetSplits tail).map _ = _
    rfl
  -- The boundary split (S-sel, (J\S)-sel) in the cons-canonical form.
  have hS_boundary_eq :
      (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) =
        (fun s : List Hex.ZPoly × List Hex.ZPoly => (head :: s.1, s.2))
          ((tail.zip mask_S).filterMap (fun p => if p.2 then some p.1 else none),
           (tail.zip mask_S).filterMap (fun p => if p.2 then none else some p.1)) := by
    simp only [Prod.mk.injEq]
    refine ⟨?_, ?_⟩
    · rw [hS_sel_cons]
    · rw [hS_rest_eq]
  rw [hsswf_eq, hS_boundary_eq] at hsplits
  -- Apply List.map_eq_append_iff to get a decomposition of subsetSplits tail.
  obtain ⟨preIdx, suffIdx, hsplitsTail, hpreIdx_eq, hsuffIdx_eq⟩ :=
    List.map_eq_append_iff.mp hsplits
  cases suffIdx with
  | nil =>
      exfalso
      simp only [List.map_nil] at hsuffIdx_eq
      exact List.cons_ne_nil _ _ hsuffIdx_eq.symm
  | cons headIdx tailIdx =>
      simp only [List.map_cons] at hsuffIdx_eq
      injection hsuffIdx_eq with hboundary_eq _hsuffix_map_eq
      -- hboundary_eq : (head :: headIdx.1, headIdx.2) =
      --   (head :: mask_S filterMap selected, mask_S filterMap rest)
      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hboundary_eq
      obtain ⟨hheadIdx_sel, hheadIdx_rest⟩ := hboundary_eq
      obtain ⟨headIdxSel, headIdxRest⟩ := headIdx
      simp only at hheadIdx_sel hheadIdx_rest
      subst hheadIdx_sel
      subst hheadIdx_rest
      -- hsplitsTail : subsetSplits tail =
      --   preIdx ++ ((tail.zip mask_S).filterMap selected,
      --              (tail.zip mask_S).filterMap rest) :: tailIdx
      -- Step 4: identify split = f((tail.zip mask_T).filterMap selected, ...).
      have hsplit_eq_canonical :
          split = (fun s : List Hex.ZPoly × List Hex.ZPoly => (head :: s.1, s.2))
            ((tail.zip mask_T).filterMap (fun p => if p.2 then some p.1 else none),
             (tail.zip mask_T).filterMap (fun p => if p.2 then none else some p.1)) := by
        rw [hsplit_eq]
        simp only [Prod.mk.injEq]
        refine ⟨?_, ?_⟩
        · rw [hT_sel_cons]
        · rw [hT_rest_eq]
      -- pre = preIdx.map f and split ∈ pre.
      rw [← hpreIdx_eq] at hsplit
      rw [hsplit_eq_canonical] at hsplit
      obtain ⟨innerT, hinnerT_mem, hinnerT_eq⟩ := List.mem_map.mp hsplit
      -- innerT ∈ preIdx and f(innerT) = f(canonical_T_inner). By injectivity, innerT =
      -- canonical_T_inner.
      simp only [Prod.mk.injEq, List.cons.injEq, true_and] at hinnerT_eq
      obtain ⟨hT_inner_sel_eq, hT_inner_rest_eq⟩ := hinnerT_eq
      obtain ⟨innerTSel, innerTRest⟩ := innerT
      simp only at hT_inner_sel_eq hT_inner_rest_eq
      subst hT_inner_sel_eq
      subst hT_inner_rest_eq
      -- innerT-canonical ∈ preIdx.
      -- Step 5: apply the mask-level helper.
      obtain ⟨i', hi', hmsT_i', hmsS_i'⟩ :=
        subsetSplits_prefix_exists_bit_diff_aux htail_nodup
          hmask_S_len hmask_T_len hsplitsTail hinnerT_mem
      -- Step 6: translate i' to ys[i'].
      have hi'_ys : i' < ys.length := by
        have : tail.length = ys.length := by simp [tail]
        rw [this] at hi'
        exact hi'
      refine ⟨ys[i'], ?_, ?_, ?_⟩
      · exact hys_in_J ys[i'] (List.getElem_mem _)
      · -- ys[i'] ∈ S, from mask_S[i'] = true.
        have h_mask_S_val : mask_S[i'] = decide (ys[i'] ∈ S) := by
          simp [hmask_S_def]
        have : decide (ys[i'] ∈ S) = true := by
          rw [← h_mask_S_val]
          exact hmsS_i'
        exact of_decide_eq_true this
      · -- ys[i'] ∉ T, from mask_T[i'] = false.
        have h_mask_T_val : mask_T[i'] = decide (ys[i'] ∈ T) := by
          simp [hmask_T_def]
        have : decide (ys[i'] ∈ T) = false := by
          rw [← h_mask_T_val]
          exact hmsT_i'
        exact of_decide_eq_false this

/-- The transported recombination candidate product equals the proof-side
lifted-factor product: both factor lists are permutations of each other in
`Polynomial ℤ`, so commutativity collapses the order difference. -/
theorem polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Array.polyProduct (liftedSubsetSelectedList d S).toArray =
      liftedFactorProduct d S := by
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [polyProduct_toPolynomial, liftedSubsetSelectedList_eq_filter_map]
  -- LHS: ((((List.finRange n).filter (· ∈ S)).map (liftedFactor d)).map toPolynomial).prod
  rw [List.map_map]
  -- LHS: (((List.finRange n).filter (· ∈ S)).map (toPolynomial ∘ liftedFactor d)).prod
  -- Now compute RHS.
  unfold liftedFactorProduct
  rw [show (S.toList.foldl (fun acc i => acc * liftedFactor d i) (1 : Hex.ZPoly)) =
        (S.toList.map (liftedFactor d)).foldl (· * ·) 1 from by
    rw [List.foldl_map]]
  rw [toPolynomial_foldl_mul, toPolynomial_one_zpoly, ← List.prod_eq_foldl, List.map_map]
  -- Now both sides are List.prod over (... .map (toPolynomial ∘ liftedFactor d))
  apply List.Perm.prod_eq
  apply List.Perm.map
  exact finRange_filter_mem_perm_toList S

/-- When index `0` is in `S`, the lifted-factor subset partition lies in the
`subsetSplitsWithFirst` enumeration that the recombination search iterates. -/
theorem liftedSubsetSplit_mem_subsetSplitsWithFirst
    (d : Hex.LiftData) (S : LiftedFactorSubset d)
    (hpos : 0 < d.liftedFactors.size)
    (h0 : (⟨0, hpos⟩ : LiftedFactorIndex d) ∈ S) :
    (liftedSubsetSelectedList d S, liftedSubsetRejectedList d S) ∈
      Hex.subsetSplitsWithFirst d.liftedFactors.toList := by
  unfold liftedSubsetSelectedList liftedSubsetRejectedList
  -- Decompose d.liftedFactors.toList and the mask into cons forms.
  have hxs_pos : 0 < d.liftedFactors.toList.length := by simpa using hpos
  have hmask_len := liftedSubsetMask_length d S
  have hmask_head := liftedSubsetMask_head?_eq_decide d S hpos
  rcases hxs : d.liftedFactors.toList with _ | ⟨x, xs⟩
  · rw [hxs] at hxs_pos; simp at hxs_pos
  rcases hmask : liftedSubsetMask d S with _ | ⟨b, bs⟩
  · rw [hmask] at hmask_head; simp at hmask_head
  -- Head bit is determined by `h0`.
  rw [hmask] at hmask_head
  simp [h0] at hmask_head
  -- `hmask_head : b = true`
  subst hmask_head
  -- Lengths line up.
  have hbs_len : bs.length = xs.length := by
    rw [hmask, hxs] at hmask_len
    simpa using hmask_len
  exact subsetSplitsWithFirst_zip_filterMap_partition x xs bs hbs_len

/-- The executable recombination candidate associated to a lifted-factor
subset: this is the `Hex.ZPoly` value that the recombination search compares
against the running target via `shouldRecordPolynomialFactor` /
`exactQuotient?`.  Definitionally equal to the inline expression used inside
`Hex.recombinationSearchModAux`. -/
def recombinationCandidate (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    Hex.ZPoly :=
  Hex.normalizeFactorSign <|
    Hex.ZPoly.primitivePart <|
      Hex.centeredLiftPoly
        (Array.polyProduct (liftedSubsetSelectedList d S).toArray)
        (d.p ^ d.k)

/-- The executable-list recombination candidate agrees with the proof-side
product candidate. -/
theorem recombinationCandidate_eq_liftedFactorProductCandidate
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    recombinationCandidate d S = liftedFactorProductCandidate d S := by
  unfold recombinationCandidate liftedFactorProductCandidate
  rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]

/--
Structural support containment for a divisor of an executable recombination
candidate under a lifted-factor subset partition.

This is the projection consumed by the cover-at-min assembler: an irreducible
integer factor represented by `S` cannot divide the candidate built from `T`
unless all local factors in `S` were selected by `T`.
-/
theorem representingSubset_subset_of_dvd_recombinationCandidate
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_hcore_ne : core ≠ 0)
    (_hcore_monic : Hex.DensePoly.Monic core)
    (_hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ recombinationCandidate d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  apply hpartition.support_subset_of_dvd_recombinationCandidate
    hirr hfactor_dvd_target hTJ
  · rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
    exact hfactor_dvd_candidate
  · exact hSJ
  · exact hrep

/-- Abstract-bound variant of
`representingSubset_subset_of_dvd_recombinationCandidate`: takes
`_B' : Nat`, `_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B'`, and
`_hprecision : 2 * _B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Both the
abstract bound and the precision hypothesis are vestigial here (the
proof body delegates to the structural support field of
`LiftedFactorSubsetPartition`, which never consumes precision); they
are threaded purely for API parity with the broader `_of_bound`
propagation chain. -/
theorem representingSubset_subset_of_dvd_recombinationCandidate_of_bound
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_B' : Nat)
    (_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B')
    (_hcore_ne : core ≠ 0)
    (_hcore_monic : Hex.DensePoly.Monic core)
    (_hprecision : 2 * _B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ recombinationCandidate d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  apply hpartition.support_subset_of_dvd_recombinationCandidate
    hirr hfactor_dvd_target hTJ
  · rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
    exact hfactor_dvd_candidate
  · exact hSJ
  · exact hrep

/-- Primitive + positive-leading-core variant of
`representingSubset_subset_of_dvd_recombinationCandidate` (#4646 chain).

The original `hcore_monic` parameter is vestigial in the monic version (the
proof body never uses it), so the primitive variant has identical body and
threads `hcore_primitive` and `hcore_lc_pos` purely for API uniformity with
the rest of the primitive-core chain. -/
theorem representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (_hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ recombinationCandidate d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  apply hpartition.support_subset_of_dvd_recombinationCandidate
    hirr hfactor_dvd_target hTJ
  · rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
    exact hfactor_dvd_candidate
  · exact hSJ
  · exact hrep

/-- Abstract-bound variant of
`representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core`:
takes `_B' : Nat`, `_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B'`, and
`_hprecision : 2 * _B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Both the
abstract bound and the precision hypothesis are vestigial here; they
are threaded purely for API parity with the broader `_of_bound`
propagation chain. -/
theorem representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_B' : Nat)
    (_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B')
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (_hprecision : 2 * _B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (hfactor_dvd_candidate : f ∣ recombinationCandidate d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  apply hpartition.support_subset_of_dvd_recombinationCandidate
    hirr hfactor_dvd_target hTJ
  · rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
    exact hfactor_dvd_candidate
  · exact hSJ
  · exact hrep

/-- Primitive + positive-leading-core support containment for scaled
recombination candidates (#4736).

This is the scaled-candidate analogue of
`representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core`.
The extra primitive/sign/target-divisibility hypotheses match the recovery
pipeline used by the primitive recursive recombination chain; the actual
support conclusion is supplied by the scaled analytic support field of
`LiftedFactorSubsetPartition`, not by identifying scaled and unscaled
candidates. -/
theorem representingSubset_subset_of_dvd_scaledRecombinationCandidate_of_primitive_pos_lc_core
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (_hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (_htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (_hfactor_prim : Hex.ZPoly.content f = 1)
    (_hfactor_norm : Hex.normalizeFactorSign f = f)
    (hfactor_dvd_candidate : f ∣ scaledRecombinationCandidate core d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  exact hpartition.support_subset_of_dvd_scaledRecombinationCandidate
    hirr hfactor_dvd_target hTJ hfactor_dvd_candidate hSJ hrep

/-- Abstract-bound variant of
`representingSubset_subset_of_dvd_scaledRecombinationCandidate_of_primitive_pos_lc_core`:
takes `_B' : Nat`, `_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B'`, and
`_hprecision : 2 * _B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Both the
abstract bound and the precision hypothesis are vestigial here (the
proof body delegates to the scaled support field of
`LiftedFactorSubsetPartition`, which never consumes precision); they
are threaded purely for API parity with the broader `_of_bound`
propagation chain. -/
theorem representingSubset_subset_of_dvd_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
    {core target f : Hex.ZPoly} {d : Hex.LiftData}
    {J T S : LiftedFactorSubset d}
    (_B' : Nat)
    (_hvalid : ∀ i, (f.coeff i).natAbs ≤ _B')
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (_hprecision : 2 * _B' < d.p ^ d.k)
    (_htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hTJ : T ⊆ J)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f))
    (hfactor_dvd_target : f ∣ target)
    (_hfactor_prim : Hex.ZPoly.content f = 1)
    (_hfactor_norm : Hex.normalizeFactorSign f = f)
    (hfactor_dvd_candidate : f ∣ scaledRecombinationCandidate core d T)
    (hSJ : S ⊆ J)
    (hrep : RepresentsIntegerFactorAtLift core d f S) :
    S ⊆ T := by
  exact hpartition.support_subset_of_dvd_scaledRecombinationCandidate
    hirr hfactor_dvd_target hTJ hfactor_dvd_candidate hSJ hrep

/-- The `Hex.centeredLiftPoly` operation is invariant under prior reduction by
the same modulus, so the A2 recovery equality phrased in terms of
`reduceModPow` of the scaled lifted product can equivalently be stated as the
direct centered lift of the scaled lifted product. -/
private theorem centeredLiftPoly_reduceModPow_eq
    (f : Hex.ZPoly) (p k : Nat) (hp : 0 < p) :
    Hex.centeredLiftPoly (Hex.ZPoly.reduceModPow f p k) (p ^ k) =
      Hex.centeredLiftPoly f (p ^ k) := by
  have hpkpos : 0 < p ^ k := Nat.pow_pos hp
  have hpkne : p ^ k ≠ 0 := Nat.ne_of_gt hpkpos
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.coeff_centeredLiftPoly, Hex.coeff_centeredLiftPoly,
    Hex.ZPoly.coeff_reduceModPow_eq_emod_of_pos _ _ _ _ hpkpos]
  -- Goal: centeredModNat ((f.coeff n) % (p^k : Int)) (p^k) = centeredModNat (f.coeff n) (p^k)
  unfold Hex.centeredModNat
  rw [if_neg hpkne, if_neg hpkne]
  -- both branches use r = z % m; the LHS computes ((f.coeff n) % m) % m which equals (f.coeff n) % m
  rw [Int.emod_emod_of_dvd _ (dvd_refl _)]

/-- Abstract-bound variant of
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint. -/
theorem centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k) =
      factor := by
  have h := centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision_of_bound
    B' hvalid hrep hprecision
  rwa [centeredLiftPoly_reduceModPow_eq _ _ _ d.p_pos] at h

/-- The A2 recovery equality reformulated against the executable centred-lift
of the **scaled** lifted product, ready to feed downstream packaging that
relates the scaled centered lift to the unscaled `recombinationCandidate`.

This is the cleanest form in which the proof-side recovery is expressed for
later integration with executable-side normalisation reasoning (which removes
the `lc(core)` scale and chooses a sign).

This is a thin wrapper over
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`. -/
theorem centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k) =
      factor :=
  centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hrep hprecision

private theorem densePoly_scale_one_int (f : Hex.ZPoly) :
    Hex.DensePoly.scale (1 : Int) f = f := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_scale (1 : Int) f n (by simp)]
  simp

/-- Abstract-bound variant of
`recombinationCandidate_eq_factor_of_recovery_of_monic_core`: takes
`B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The proof mirrors
the core-shape original but invokes
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`
in place of the core-shape recovery theorem. -/
theorem recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    recombinationCandidate d S = factor := by
  have hlead : Hex.DensePoly.leadingCoeff core = (1 : Int) := by
    simpa [Hex.DensePoly.Monic] using hcore_monic
  have hscaled :
      scaledLiftedFactorProduct core d S = liftedFactorProduct d S := by
    unfold scaledLiftedFactorProduct
    rw [hlead]
    exact densePoly_scale_one_int (liftedFactorProduct d S)
  have hcenter :
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k) = factor := by
    have h :=
      centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
        B' hvalid hrep hprecision
    rwa [hscaled] at h
  unfold recombinationCandidate
  rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct, hcenter]
  have hprimitive :
      Hex.ZPoly.primitivePart factor = factor :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive factor
      (by simpa [Hex.ZPoly.Primitive] using hfactor_prim)
  rw [hprimitive]
  exact hfactor_norm

/--
Under a monic core hypothesis, the scaled recovery theorem identifies the
unscaled executable recombination candidate with the represented integer
factor.  This is the core recovery statement; the older
`recombinationCandidate_eq_factor_of_recovery` wrapper also accepts the
executable record-filter hypothesis needed by some callers.

This is a thin wrapper over
`recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem recombinationCandidate_eq_factor_of_recovery_of_monic_core
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hcore_monic hfactor_prim hfactor_norm _hirr hrep hprecision

/-- Abstract-bound variant of
`recombinationCandidate_eq_factor_of_recovery`: takes `B' : Nat`,
`hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Delegates to
`recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound`. -/
theorem recombinationCandidate_eq_factor_of_recovery_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (_hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound
    B' hvalid hcore_ne hcore_monic hfactor_prim hfactor_norm _hirr hrep hprecision

/--
Under a monic core hypothesis, the scaled recovery theorem identifies the
unscaled executable recombination candidate with the represented integer
factor.

This is a thin wrapper over
`recombinationCandidate_eq_factor_of_recovery_of_bound` that instantiates
`B' := defaultFactorCoeffBound core` and discharges `hvalid` via
`defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem recombinationCandidate_eq_factor_of_recovery
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (_hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_recovery_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hcore_monic _hcore_record hfactor_prim hfactor_norm _hirr hrep hprecision

/-- Abstract-bound variant of
`recombinationCandidate_eq_factor_of_henselSubsetCorrespondence`: takes
`B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Delegates to
`recombinationCandidate_eq_factor_of_recovery_of_bound`. -/
theorem recombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    {S : LiftedFactorSubset d}
    (_h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_recovery_of_bound
    B' hvalid hcore_ne hcore_monic hcore_record hfactor_prim hfactor_norm hirr
    hrep hprecision

/--
Hensel-correspondence wrapper for the monic-core recovery theorem.

Once a proof-side subset is known to represent an irreducible integer divisor
at the Hensel lift, the executable recombination candidate is exactly that
factor under the monic/primitive/sign-normalised hypotheses required by the
centered-lift recovery bound.

This is a thin wrapper over
`recombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem recombinationCandidate_eq_factor_of_henselSubsetCorrespondence
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    {S : LiftedFactorSubset d}
    (_h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    recombinationCandidate d S = factor :=
  recombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound
    _h
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hcore_monic hcore_record hirr hfactor_prim hfactor_norm hrep hprecision

/-- Abstract-bound variant of
`scaledRecombinationCandidate_eq_factor_of_recovery`: takes `B' : Nat`,
`hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The body mirrors
the original but invokes the `_of_bound` centered-lift recovery theorem
instead of the core-shape one.  The original core-shape theorem is a
wrapper around this variant. -/
theorem scaledRecombinationCandidate_eq_factor_of_recovery_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    scaledRecombinationCandidate core d S = factor := by
  unfold scaledRecombinationCandidate
  rw [centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
        B' hvalid hrep hprecision]
  have hprimitive : Hex.ZPoly.primitivePart factor = factor :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive factor
      (by simpa [Hex.ZPoly.Primitive] using hfactor_prim)
  rw [hprimitive]
  exact hfactor_norm

/--
Primitive non-monic recovery supporting lemma: the scaled recombination candidate
equals the represented integer `factor` under primitive/sign-normalised
hypotheses on `factor` plus the standard Mignotte-precision and representation
hypotheses. This is the corrected first recovery step for the primitive
non-monic recombination chain (parent #4638, replaces stale #4643).

Unlike `recombinationCandidate_eq_factor_of_recovery_of_monic_core`, this
theorem does *not* require `Monic core` and does *not* route through the
leading-coefficient collapse `scaledLiftedFactorProduct = liftedFactorProduct`.
The inner equality is supplied directly by
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery`;
`primitivePart_eq_self_of_primitive` and the supplied `normalizeFactorSign`
fixed-point discharge the outer normalisation pipeline.

Downstream callers (#4644, #4646, #4647, #4648) call this in place of the
monic-core recovery when the core hypotheses are
`core ≠ 0 ∧ Primitive core ∧ 0 < leadingCoeff core`; the primitive/sign
hypotheses on `factor` are supplied by their primitive-factor packaging step.

This is a thin wrapper over
`scaledRecombinationCandidate_eq_factor_of_recovery_of_bound` that
instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem scaledRecombinationCandidate_eq_factor_of_recovery
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    scaledRecombinationCandidate core d S = factor :=
  scaledRecombinationCandidate_eq_factor_of_recovery_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hfactor_prim hfactor_norm hrep hprecision

/-- Abstract-bound variant of
`scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Body is a
one-line delegation to
`scaledRecombinationCandidate_eq_factor_of_recovery_of_bound`. -/
theorem scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    {S : LiftedFactorSubset d}
    (_h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    scaledRecombinationCandidate core d S = factor :=
  scaledRecombinationCandidate_eq_factor_of_recovery_of_bound
    B' hvalid hcore_ne hfactor_prim hfactor_norm hrep hprecision

/--
Hensel-correspondence wrapper for the primitive-core scaled recovery theorem.

Primitive-core analogue of
`recombinationCandidate_eq_factor_of_henselSubsetCorrespondence`: once a
proof-side subset is known to represent an irreducible integer divisor at the
Hensel lift, the *scaled* recombination candidate is exactly that factor under
the primitive/sign-normalised hypotheses required by the centered-lift
recovery bound.

This is a thin wrapper over
`scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    {S : LiftedFactorSubset d}
    (_h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    scaledRecombinationCandidate core d S = factor :=
  scaledRecombinationCandidate_eq_factor_of_henselSubsetCorrespondence_of_bound
    _h (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hfactor_prim hfactor_norm hrep hprecision

/-- Monic integer polynomials have positive stored size. -/
private theorem zpoly_size_pos_of_monic {f : Hex.ZPoly}
    (h : Hex.DensePoly.Monic f) : 0 < f.size := by
  have hlead : Hex.DensePoly.leadingCoeff f = (1 : Int) := h
  rcases Nat.eq_zero_or_pos f.coeffs.size with hcs_zero | hcs_pos
  · exfalso
    have hback_none : f.coeffs.back? = none := by
      rw [Array.back?_eq_getElem?]; simp [hcs_zero]
    have hlc_zero : Hex.DensePoly.leadingCoeff f = (0 : Int) := by
      unfold Hex.DensePoly.leadingCoeff; rw [hback_none]; rfl
    rw [hlc_zero] at hlead
    exact absurd hlead (by decide)
  · exact hcs_pos

/-- Monic integer polynomials are primitive (content 1). -/
theorem zpoly_primitive_of_monic {f : Hex.ZPoly}
    (h : Hex.DensePoly.Monic f) : Hex.ZPoly.Primitive f := by
  have hlead : Hex.DensePoly.leadingCoeff f = (1 : Int) := h
  have hcs_pos : 0 < f.coeffs.size := zpoly_size_pos_of_monic h
  have hsize_pos : 0 < f.size := hcs_pos
  have hcoeff_last : f.coeff (f.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hsize_pos]
    exact hlead
  have hdvd_one : Hex.ZPoly.content f ∣ (1 : Int) := by
    have := Hex.DensePoly.content_dvd_coeff f (f.size - 1)
    rwa [hcoeff_last] at this
  have hcontent_nonneg : (0 : Int) ≤ Hex.ZPoly.content f := by
    unfold Hex.ZPoly.content Hex.DensePoly.content
    exact Int.natCast_nonneg _
  rcases Int.isUnit_iff.mp (isUnit_of_dvd_one hdvd_one) with hpos | hneg
  · exact hpos
  · exfalso
    rw [hneg] at hcontent_nonneg
    exact absurd hcontent_nonneg (by decide)

/-- Monic integer polynomials are fixed by `Hex.normalizeFactorSign`. -/
theorem zpoly_normalize_factor_sign_of_monic {f : Hex.ZPoly}
    (h : Hex.DensePoly.Monic f) : Hex.normalizeFactorSign f = f := by
  have hlead : Hex.DensePoly.leadingCoeff f = (1 : Int) := h
  unfold Hex.normalizeFactorSign
  have hnot_neg : ¬ Hex.DensePoly.leadingCoeff f < 0 := by
    rw [hlead]; decide
  simp [hnot_neg]

/--
A monic integer polynomial automatically has primitive content and is its own
sign-normalisation. This packages the two normalisation hypotheses required
by `recombinationCandidate_eq_factor_of_recovery` (`content factor = 1` and
`normalizeFactorSign factor = factor`) into one consequence of `Monic factor`,
together with restating the monic hypothesis itself.

Intended use by the recursive coverage proof for `Hex.recombinationSearchModAux`
(#4301): once the proof obtains a monic integer divisor of the current target
via the Hensel-lift partition, this helper discharges the primitive and
sign-normalised hypotheses of `recombinationCandidate_eq_factor_of_recovery`
for that factor. Monicness itself is taken as a hypothesis here because the
`LiftedFactorSubsetPartition.cover` field does not constrain the integer
factor's leading-coefficient sign; the recursive coverage proof supplies it
from a separate Hensel-lift normalisation argument.
-/
theorem monic_primitive_sign_normalized_of_monic
    {factor : Hex.ZPoly} (hfactor_monic : Hex.DensePoly.Monic factor) :
    Hex.DensePoly.Monic factor ∧
      Hex.ZPoly.content factor = 1 ∧
        Hex.normalizeFactorSign factor = factor :=
  ⟨hfactor_monic,
    zpoly_primitive_of_monic hfactor_monic,
    zpoly_normalize_factor_sign_of_monic hfactor_monic⟩

/--
Size of the lifted-factor array equals the size of the modular-factor array.

This is the `factor_count_eq` field that `HenselSubsetLiftHypotheses` (line
1425 above) requires for the executable `Hex.choosePrimeData` /
`Hex.henselLiftData` surface. The lifted-factor array is
`Hex.ZPoly.multifactorLiftQuadratic primeData.p B core
  (primeData.factorsModP.map Hex.FpPoly.liftToZ)`, whose size equals the
input map's size by `Hex.ZPoly.multifactorLiftQuadratic_size_eq_input`; the
map preserves size by `Array.size_map`. -/
theorem henselLiftData_liftedFactors_size_eq
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData) :
    (Hex.henselLiftData core B primeData).liftedFactors.size =
      primeData.factorsModP.size := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  show (Hex.ZPoly.multifactorLiftQuadratic primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ)).size
      = primeData.factorsModP.size
  rw [Hex.ZPoly.multifactorLiftQuadratic_size_eq_input]
  simp

theorem Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData) :
    (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size =
      primeData.factorsModP.size := by
  unfold Hex.ZPoly.toMonicLiftData
  exact henselLiftData_liftedFactors_size_eq
    (Hex.ZPoly.toMonic core).monic
    (Hex.precisionForCoeffBound B primeData.p) primeData

/--
Thin umbrella wrapper exposing per-output monicness of `Hex.henselLiftData` in
the Mathlib-facing surface.

`Hex.henselLiftData` produces its `liftedFactors` by invoking
`Hex.ZPoly.multifactorLiftQuadratic`, and the executable proof
`Hex.ZPoly.multifactorLiftQuadratic_each_monic` already supplies monicness of
every output index given monicness of the input core and the quadratic
multifactor lift invariant. This wrapper simply re-exposes that conclusion at
the `henselLiftData` umbrella for downstream callers
(notably `monic_primitive_sign_normalized_of_monic` above, which discharges
the primitivity and sign-normalisation hypotheses required by
`recombinationCandidate_eq_factor_of_recovery` once monicness is in hand).
-/
theorem henselLiftData_liftedFactor_monic
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B) :
    ∀ i : Fin (Hex.henselLiftData core B primeData).liftedFactors.size,
      Hex.DensePoly.Monic
        (Hex.henselLiftData core B primeData).liftedFactors[i] := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  intro i
  exact Hex.ZPoly.multifactorLiftQuadratic_each_monic
    primeData.p B core
    (primeData.factorsModP.map Hex.FpPoly.liftToZ)
    hB hp hcore_monic hprime_invariant i

/--
Per-output monicness for the executable `Hex.ZPoly.toMonicLiftData`.

This is the direct `Hex.ZPoly.toMonicLiftData` surface over the existing
`henselLiftData_liftedFactor_monic` invariant: the Hensel stage runs on
`(Hex.ZPoly.toMonic core).monic`, while recombination callers
still keep representation predicates against the original `core`.
-/
theorem Hex.ZPoly.toMonicLiftData_liftedFactor_monic
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hmonic_core :
      Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p)
        (Hex.ZPoly.toMonic core).monic
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p) :
    ∀ i : Fin (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size,
      Hex.DensePoly.Monic
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i) := by
  unfold Hex.ZPoly.toMonicLiftData
  exact henselLiftData_liftedFactor_monic
    (Hex.ZPoly.toMonic core).monic
    (Hex.precisionForCoeffBound B primeData.p) primeData
    hmonic_core hprime_invariant hp hprecision

/--
Composed convenience wrapper: combines
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData` with
`henselLiftData_liftedFactor_monic` so that a Mathlib-side caller can
discharge per-output monicness of `Hex.henselLiftData` from the
`choosePrimeData` boundary facts directly, without having to construct the
internal `QuadraticMultifactorLiftInvariant` themselves.

The upstream wrapper
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData`
(in `HexBerlekampZassenhaus/Basic.lean`) packages the per-factor monicness,
mod-`p` product congruence, sequential split coprimality, and nonempty witness
into the abstract invariant; this wrapper then feeds it into the abstract-
invariant version `henselLiftData_liftedFactor_monic` above.
-/
theorem henselLiftData_liftedFactor_monic_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hp_prime : Hex.Nat.Prime primeData.p)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList)
    (hnonempty : primeData.factorsModP.toList ≠ []) :
    ∀ i : Fin (Hex.henselLiftData core B primeData).liftedFactors.size,
      Hex.DensePoly.Monic
        (Hex.henselLiftData core B primeData).liftedFactors[i] := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hinv :
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList :=
    Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      core B primeData hp_prime hp hB hcore_monic
      hfactors_monic hproduct_mod_p hcoprime hnonempty
  exact henselLiftData_liftedFactor_monic core B primeData
    hcore_monic hinv hp hB

/--
Abstract-invariant injectivity umbrella for `Hex.henselLiftData` outputs.

Mirrors the structure of `henselLiftData_liftedFactor_monic`: takes the
recursive `QuadraticMultifactorLiftInvariant` package plus mod-`p` product
congruence and `Nodup` of the original modular factor list, and produces
`Function.Injective (liftedFactor d)` directly.

The proof routes through `Hex.ZPoly.multifactorLiftQuadratic_each_congr_mod_base`:
each lifted factor reduces modulo `p` to the corresponding original modular
factor (after `FpPoly.liftToZ`). Equal lifted factors therefore force equal
modular factors, and `Nodup` of `factorsModP` collapses to equal indices.

This bypasses pairwise coprimality entirely; degenerate "unit lifted factor"
cases are excluded by `Nodup` rather than by positive natDegree. -/
theorem henselLiftData_liftedFactor_injective
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hfactorsModP_nodup : primeData.factorsModP.toList.Nodup) :
    Function.Injective
      (liftedFactor (Hex.henselLiftData core B primeData)) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  -- The lifted-factor array equals the multifactor output by definition of
  -- `Hex.henselLiftData`. We name a local abbreviation for the multifactor output
  -- to thread index reasoning through both views.
  set arr :=
    Hex.ZPoly.multifactorLiftQuadratic primeData.p B core
      (primeData.factorsModP.map Hex.FpPoly.liftToZ) with harr_def
  have hd_factors :
      (Hex.henselLiftData core B primeData).liftedFactors = arr := by
    simp [Hex.henselLiftData, harr_def]
  have harr_size :
      arr.size = primeData.factorsModP.size := by
    rw [harr_def, Hex.ZPoly.multifactorLiftQuadratic_size_eq_input]
    simp
  have hd_size :
      (Hex.henselLiftData core B primeData).liftedFactors.size =
        primeData.factorsModP.size := by
    rw [hd_factors]; exact harr_size
  intro i j hij
  -- Convert the goal-level equality to an array-level equality on arr.
  have hi_arr : i.val < arr.size := by rw [harr_size]; rw [← hd_size]; exact i.isLt
  have hj_arr : j.val < arr.size := by rw [harr_size]; rw [← hd_size]; exact j.isLt
  have hi_in : i.val < primeData.factorsModP.size := by
    rw [← harr_size]; exact hi_arr
  have hj_in : j.val < primeData.factorsModP.size := by
    rw [← harr_size]; exact hj_arr
  have hij_arr : arr[i.val]'hi_arr = arr[j.val]'hj_arr := by
    -- Both arrays are definitionally equal via the henselLiftData definition.
    change (Hex.henselLiftData core B primeData).liftedFactors[i.val]'i.isLt =
           (Hex.henselLiftData core B primeData).liftedFactors[j.val]'j.isLt
    show (Hex.henselLiftData core B primeData).liftedFactors[i] =
         (Hex.henselLiftData core B primeData).liftedFactors[j]
    exact hij
  -- Monic premises in the lifted-array form
  have hfactors_monic_arr :
      ∀ g ∈ (primeData.factorsModP.map Hex.FpPoly.liftToZ),
        Hex.DensePoly.Monic g := by
    intro g hg
    rw [Array.mem_map] at hg
    obtain ⟨f0, hf0_mem, hf0_eq⟩ := hg
    rw [← hf0_eq]
    exact Hex.FpPoly.monic_liftToZ_of_monic f0 hp (hfactors_monic f0 hf0_mem)
  -- Per-output mod-p congruences at indices i.val, j.val (getD form)
  have hcongr_i :=
    Hex.ZPoly.multifactorLiftQuadratic_each_congr_mod_base
      primeData.p B core (primeData.factorsModP.map Hex.FpPoly.liftToZ)
      hB hp hcore_monic hfactors_monic_arr hprime_invariant hproduct_mod_p i.val
  have hcongr_j :=
    Hex.ZPoly.multifactorLiftQuadratic_each_congr_mod_base
      primeData.p B core (primeData.factorsModP.map Hex.FpPoly.liftToZ)
      hB hp hcore_monic hfactors_monic_arr hprime_invariant hproduct_mod_p j.val
  -- Reduce getD-form to direct getElem-form
  have hi_map :
      i.val < (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList.length := by
    rw [Array.length_toList, Array.size_map]; exact hi_in
  have hj_map :
      j.val < (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList.length := by
    rw [Array.length_toList, Array.size_map]; exact hj_in
  have hi_arr_list : i.val < arr.toList.length := by
    rw [Array.length_toList]; exact hi_arr
  have hj_arr_list : j.val < arr.toList.length := by
    rw [Array.length_toList]; exact hj_arr
  have hgetD_arr_i :
      arr.toList[i.val]?.getD 0 = arr[i.val]'hi_arr := by
    rw [List.getElem?_eq_getElem hi_arr_list, Option.getD_some, Array.getElem_toList]
  have hgetD_arr_j :
      arr.toList[j.val]?.getD 0 = arr[j.val]'hj_arr := by
    rw [List.getElem?_eq_getElem hj_arr_list, Option.getD_some, Array.getElem_toList]
  have hgetD_factors_i :
      (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList[i.val]?.getD 0 =
        Hex.FpPoly.liftToZ (primeData.factorsModP[i.val]'hi_in) := by
    rw [List.getElem?_eq_getElem hi_map, Option.getD_some,
      Array.getElem_toList, Array.getElem_map]
  have hgetD_factors_j :
      (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList[j.val]?.getD 0 =
        Hex.FpPoly.liftToZ (primeData.factorsModP[j.val]'hj_in) := by
    rw [List.getElem?_eq_getElem hj_map, Option.getD_some,
      Array.getElem_toList, Array.getElem_map]
  rw [hgetD_arr_i, hgetD_factors_i] at hcongr_i
  rw [hgetD_arr_j, hgetD_factors_j] at hcongr_j
  -- Combine to liftToZ factorsModP[i] ≡ liftToZ factorsModP[j] mod p
  have hcongr_ij :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ (primeData.factorsModP[i.val]'hi_in))
        (Hex.FpPoly.liftToZ (primeData.factorsModP[j.val]'hj_in))
        primeData.p := by
    have h_i_symm := Hex.ZPoly.congr_symm _ _ _ hcongr_i
    have hcongr_j' :
        Hex.ZPoly.congr
          (arr[i.val]'hi_arr)
          (Hex.FpPoly.liftToZ (primeData.factorsModP[j.val]'hj_in))
          primeData.p := hij_arr ▸ hcongr_j
    exact Hex.ZPoly.congr_trans _ _ _ _ h_i_symm hcongr_j'
  -- Reduce mod p both sides
  have hmodP :
      Hex.ZPoly.modP primeData.p
        (Hex.FpPoly.liftToZ (primeData.factorsModP[i.val]'hi_in)) =
      Hex.ZPoly.modP primeData.p
        (Hex.FpPoly.liftToZ (primeData.factorsModP[j.val]'hj_in)) :=
    Hex.ZPoly.modP_eq_of_congr primeData.p _ _ hcongr_ij
  rw [Hex.FpPoly.modP_liftToZ, Hex.FpPoly.modP_liftToZ] at hmodP
  -- Apply Nodup to extract i.val = j.val
  have hi_list : i.val < primeData.factorsModP.toList.length := by
    rw [Array.length_toList]; exact hi_in
  have hj_list : j.val < primeData.factorsModP.toList.length := by
    rw [Array.length_toList]; exact hj_in
  have hlist_i :
      primeData.factorsModP.toList[i.val]'hi_list =
        primeData.factorsModP[i.val]'hi_in := by
    rw [Array.getElem_toList]
  have hlist_j :
      primeData.factorsModP.toList[j.val]'hj_list =
        primeData.factorsModP[j.val]'hj_in := by
    rw [Array.getElem_toList]
  have hlist_eq :
      primeData.factorsModP.toList[i.val]'hi_list =
      primeData.factorsModP.toList[j.val]'hj_list := by
    rw [hlist_i, hlist_j]; exact hmodP
  have hidx_eq : i.val = j.val :=
    (List.Nodup.getElem_inj_iff hfactorsModP_nodup).mp hlist_eq
  exact Fin.ext hidx_eq

/--
Injectivity of lifted local factors for the executable
`Hex.ZPoly.toMonicLiftData`.  This is the surface over
`henselLiftData_liftedFactor_injective`.
-/
theorem Hex.ZPoly.toMonicLiftData_liftedFactor_injective
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hmonic_core :
      Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p)
        (Hex.ZPoly.toMonic core).monic
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        (Hex.ZPoly.toMonic core).monic primeData.p)
    (hfactorsModP_nodup : primeData.factorsModP.toList.Nodup) :
    Function.Injective
      (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData)) := by
  unfold Hex.ZPoly.toMonicLiftData
  exact henselLiftData_liftedFactor_injective
    (Hex.ZPoly.toMonic core).monic
    (Hex.precisionForCoeffBound B primeData.p) primeData
    hmonic_core hprime_invariant hp hprecision hfactors_monic
    hproduct_mod_p hfactorsModP_nodup

/--
Each lifted factor produced by `Hex.henselLiftData` reduces modulo the base
prime to the corresponding modular factor selected by `PrimeChoiceData`.

This is a direct indexed form of
`Hex.ZPoly.multifactorLiftQuadratic_each_congr_mod_base`, specialised to the
`Hex.henselLiftData` umbrella and the `liftedIndexOfModPIndex` transport.
-/
theorem henselLiftData_liftedFactor_modP_eq_modPFactor
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (i : ModPFactorIndex primeData) :
    letI := primeData.bounds
    Hex.ZPoly.modP primeData.p
      (liftedFactor (Hex.henselLiftData core B primeData)
        (liftedIndexOfModPIndex primeData (Hex.henselLiftData core B primeData)
          (henselLiftData_liftedFactors_size_eq core B primeData) i)) =
      modPFactor primeData i := by
  letI := primeData.bounds
  set arr :=
    Hex.ZPoly.multifactorLiftQuadratic primeData.p B core
      (primeData.factorsModP.map Hex.FpPoly.liftToZ) with harr_def
  have harr_size :
      arr.size = primeData.factorsModP.size := by
    rw [harr_def, Hex.ZPoly.multifactorLiftQuadratic_size_eq_input]
    simp
  have hi_arr : i.val < arr.size := by
    rw [harr_size]
    exact i.isLt
  have hi_map :
      i.val < (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList.length := by
    rw [Array.length_toList, Array.size_map]
    exact i.isLt
  have hi_arr_list : i.val < arr.toList.length := by
    rw [Array.length_toList]
    exact hi_arr
  have hfactors_monic_arr :
      ∀ g ∈ (primeData.factorsModP.map Hex.FpPoly.liftToZ),
        Hex.DensePoly.Monic g := by
    intro g hg
    rw [Array.mem_map] at hg
    obtain ⟨f0, hf0_mem, hf0_eq⟩ := hg
    rw [← hf0_eq]
    exact Hex.FpPoly.monic_liftToZ_of_monic f0 hp (hfactors_monic f0 hf0_mem)
  have hcongr_i :=
    Hex.ZPoly.multifactorLiftQuadratic_each_congr_mod_base
      primeData.p B core (primeData.factorsModP.map Hex.FpPoly.liftToZ)
      hB hp hcore_monic hfactors_monic_arr hprime_invariant hproduct_mod_p i.val
  have hgetD_arr :
      arr.toList[i.val]?.getD 0 = arr[i.val]'hi_arr := by
    rw [List.getElem?_eq_getElem hi_arr_list, Option.getD_some, Array.getElem_toList]
  have hgetD_factors :
      (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList[i.val]?.getD 0 =
        Hex.FpPoly.liftToZ (primeData.factorsModP[i.val]'i.isLt) := by
    rw [List.getElem?_eq_getElem hi_map, Option.getD_some,
      Array.getElem_toList, Array.getElem_map]
  rw [hgetD_arr, hgetD_factors] at hcongr_i
  have hlifted_eq :
      liftedFactor (Hex.henselLiftData core B primeData)
        (liftedIndexOfModPIndex primeData (Hex.henselLiftData core B primeData)
          (henselLiftData_liftedFactors_size_eq core B primeData) i) =
        arr[i.val]'hi_arr := by
    rfl
  rw [hlifted_eq]
  have hmodP :
      Hex.ZPoly.modP primeData.p (arr[i.val]'hi_arr) =
        Hex.ZPoly.modP primeData.p (Hex.FpPoly.liftToZ (modPFactor primeData i)) :=
    Hex.ZPoly.modP_eq_of_congr primeData.p _ _ hcongr_i
  simpa [modPFactor, Hex.FpPoly.modP_liftToZ] using hmodP

private theorem squareFree_common_of_squareFreeModP
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    (f : Hex.ZPoly)
    (hsf : Hex.squareFreeModP f p) :
    ∀ d : Hex.FpPoly p,
      d ∣ Hex.ZPoly.modP p f →
      d ∣ Hex.DensePoly.derivative (Hex.ZPoly.modP p f) →
      Hex.Berlekamp.isUnitPolynomial d = true := by
  intro d hdf hdd
  apply Hex.Berlekamp.isUnitPolynomial_of_dvd_gcd_isUnit hdf hdd
  unfold Hex.squareFreeModP at hsf
  change
    Hex.gcdIsUnit
      (Hex.DensePoly.gcd (Hex.ZPoly.modP p f)
        (Hex.DensePoly.derivative (Hex.ZPoly.modP p f))) = true at hsf
  unfold Hex.gcdIsUnit at hsf
  have hsize :
      (Hex.DensePoly.gcd (Hex.ZPoly.modP p f)
        (Hex.DensePoly.derivative (Hex.ZPoly.modP p f))).size = 1 := by
    simpa using (beq_iff_eq.mp hsf)
  unfold Hex.Berlekamp.isUnitPolynomial
  have hpos :
      0 <
        (Hex.DensePoly.gcd (Hex.ZPoly.modP p f)
          (Hex.DensePoly.derivative (Hex.ZPoly.modP p f))).size := by
    omega
  rw [Hex.DensePoly.degree?_eq_some_of_pos_size _ hpos, hsize]

/-- `choosePrimeData`-shaped caller wrapper for the Berlekamp factor `Nodup`
property: given the `factorsModPBerlekampForm` invariant (which records that
`primeData.factorsModP` is the Berlekamp factor array of the monic modular
image of the input) together with a successful `isGoodPrime` check (which
certifies the modular image is square-free), the stored factor list has no
duplicates.

Proof: extract the existential witnesses from `factorsModPBerlekampForm` to
view `data.factorsModP.toList` as the Berlekamp factor list of
`monicModularImage (modP data.p f)`, then apply the polymorphic abstract
loop invariant `Hex.Berlekamp.berlekampFactor_factors_nodup_of_no_squared`.
The squareness-free hypothesis is discharged by transferring any `g * g`
divisor through `monicModularImage modP_f ∣ modP_f` (via
`Hex.FpPoly.dvd_scale_self_of_ne_zero`) and applying
`Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd` to the
modular squarefreeness obtained from `Hex.isGoodPrime_squareFreeModP`.

This is the wrapper that lets a Mathlib-side caller of
`henselLiftData_liftedFactor_injective_of_choosePrimeData` (below) discharge
the `hfactorsModP_nodup` parameter from the `choosePrimeData?` facts alone,
without constructing the Berlekamp `Nodup` argument by hand. -/
theorem factorsModP_nodup_of_factorsModPBerlekampForm
    (f : Hex.ZPoly) (data : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm f data)
    (hgood :
      letI := data.bounds
      Hex.isGoodPrime f data.p = true) :
    data.factorsModP.toList.Nodup := by
  letI : Hex.ZMod64.Bounds data.p := data.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime data.p data.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI : Hex.ZMod64.PrimeModulus data.p := Hex.ZMod64.primeModulusOfPrime hprime
  -- Square-free precondition on the modular image, extracted from `isGoodPrime`.
  have hsf_common :
      ∀ d : Hex.FpPoly data.p,
        d ∣ Hex.ZPoly.modP data.p f →
        d ∣ Hex.DensePoly.derivative (Hex.ZPoly.modP data.p f) →
        Hex.Berlekamp.isUnitPolynomial d = true :=
    squareFree_common_of_squareFreeModP f
      (Hex.isGoodPrime_squareFreeModP f data.p hgood)
  -- `monicModularImage modP_f ∣ modP_f`: dividing by the leading coefficient
  -- scales by a nonzero element, and a unit-scaled polynomial divides the
  -- original via `dvd_scale_self_of_ne_zero`.
  have hmonicImage_dvd :
      Hex.monicModularImage (Hex.ZPoly.modP data.p f) ∣
        Hex.ZPoly.modP data.p f :=
    monicModularImage_dvd_self_of_isZero_false hprime hzero
  -- Berlekamp factor list of the monic modular image has no duplicates.
  have hNodup :
      (@Hex.Berlekamp.berlekampFactor data.p data.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP data.p f))
        (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP data.p f) hzero)
        hfield).factors.Nodup := by
    apply Hex.Berlekamp.berlekampFactor_factors_nodup_of_no_squared
    intro g hgg hpos
    have hg_dvd_mod : g * g ∣ Hex.ZPoly.modP data.p f :=
      fpPoly_dvd_trans hgg hmonicImage_dvd
    have hunit : Hex.Berlekamp.isUnitPolynomial g = true :=
      Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd hsf_common
        hg_dvd_mod
    have hdeg : Hex.DensePoly.degree? g = some 0 := by
      unfold Hex.Berlekamp.isUnitPolynomial at hunit
      cases hd : Hex.DensePoly.degree? g with
      | none => rw [hd] at hunit; simp at hunit
      | some k =>
          rw [hd] at hunit
          cases k with
          | zero => rfl
          | succ _ => simp at hunit
    rw [hdeg] at hpos
    simp at hpos
  -- The product of the Berlekamp factors equals the monic modular image
  -- (by `factorProduct_berlekampFactor`).
  have hprod :
      Hex.Berlekamp.factorProduct
          (@Hex.Berlekamp.berlekampFactor data.p data.bounds
            (Hex.monicModularImage (Hex.ZPoly.modP data.p f))
            (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP data.p f) hzero)
            hfield).factors =
        Hex.monicModularImage (Hex.ZPoly.modP data.p f) :=
    Hex.Berlekamp.factorProduct_berlekampFactor
      (Hex.monicModularImage (Hex.ZPoly.modP data.p f))
      (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP data.p f) hzero)
  -- Now show that `monicModularImage` is injective on the Berlekamp factor list:
  -- two distinct factors that agree under `monicModularImage` would be unit
  -- multiples, contradicting square-freeness of the monic image.
  set factors :=
      (@Hex.Berlekamp.berlekampFactor data.p data.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP data.p f))
        (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP data.p f) hzero)
        hfield).factors with hfactors_def
  have hinj_on :
      ∀ g₁ ∈ factors, ∀ g₂ ∈ factors,
        Hex.monicModularImage g₁ = Hex.monicModularImage g₂ → g₁ = g₂ := by
    intro g₁ hg₁ g₂ hg₂ heqm
    by_contra hne
    -- Both factors are nonzero: their monic images agree, and a zero factor
    -- has `monicModularImage = 0` while a nonzero factor has nonzero
    -- `monicModularImage` (positive leading coefficient).  But we use a
    -- more direct argument via square-freeness, so we just extract
    -- nonzero-ness from positive degree.
    -- Factors of a monic square-free polynomial have positive degree, so are
    -- nonzero.  However, the discharger does not assume input positive degree,
    -- so we handle the degenerate `factors = [1]` case via length.
    -- If factors has fewer than 2 distinct elements, hg₁/hg₂/hne contradict.
    -- Use `mul_dvd_factorProduct_of_mem_of_ne` to extract `g₁ * g₂ ∣ factorProduct`.
    have hg₁_dvd_g₂ :
        g₁ * g₂ ∣ Hex.Berlekamp.factorProduct factors :=
      Hex.Berlekamp.mul_dvd_factorProduct_of_mem_of_ne hNodup hg₁ hg₂ hne
    -- Hence g₁ * g₂ ∣ monicImage modP_f.
    rw [hprod] at hg₁_dvd_g₂
    have hg₁g₂_dvd_modP : g₁ * g₂ ∣ Hex.ZPoly.modP data.p f :=
      fpPoly_dvd_trans hg₁_dvd_g₂ hmonicImage_dvd
    -- From `monicModularImage g₁ = monicModularImage g₂`, both being nonzero,
    -- we get `g₁ = scale u g₂` for some nonzero `u`.  Use this to conclude
    -- `g₂² ∣ modP_f`, contradicting square-freeness.
    -- First we need positive degree of g₁, g₂ to know they're nonzero.
    -- For this, we case on whether `monicImage modP_f` has positive degree.
    by_cases hpos_image :
        0 < (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).degree?.getD 0
    · -- Positive-degree input: every Berlekamp factor has positive degree.
      have hg_pos :
          ∀ g ∈ factors, 0 < g.degree?.getD 0 :=
        Hex.Berlekamp.berlekampFactor_factors_pos_degree
          (Hex.monicModularImage (Hex.ZPoly.modP data.p f))
          (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP data.p f) hzero)
          hpos_image
      have hg₁_pos : 0 < g₁.degree?.getD 0 := hg_pos g₁ hg₁
      have hg₂_pos : 0 < g₂.degree?.getD 0 := hg_pos g₂ hg₂
      have hg₁_size_pos : 0 < g₁.size := by
        unfold Hex.DensePoly.degree? at hg₁_pos
        by_cases hsz : g₁.size = 0
        · simp [hsz] at hg₁_pos
        · exact Nat.pos_of_ne_zero hsz
      have hg₂_size_pos : 0 < g₂.size := by
        unfold Hex.DensePoly.degree? at hg₂_pos
        by_cases hsz : g₂.size = 0
        · simp [hsz] at hg₂_pos
        · exact Nat.pos_of_ne_zero hsz
      -- Show g₁ = scale u g₂ for u = lc g₁ · (lc g₂)⁻¹ ≠ 0.
      have hg₁_lead_ne :
          Hex.DensePoly.leadingCoeff g₁ ≠ (0 : Hex.ZMod64 data.p) :=
        Hex.FpPoly.leadingCoeff_ne_zero_of_pos_degree g₁ hg₁_pos
      have hg₂_lead_ne :
          Hex.DensePoly.leadingCoeff g₂ ≠ (0 : Hex.ZMod64 data.p) :=
        Hex.FpPoly.leadingCoeff_ne_zero_of_pos_degree g₂ hg₂_pos
      have hg₁_isZero : g₁.isZero = false :=
        (Hex.DensePoly.isZero_eq_false_iff _).mpr hg₁_size_pos
      have hg₂_isZero : g₂.isZero = false :=
        (Hex.DensePoly.isZero_eq_false_iff _).mpr hg₂_size_pos
      -- Express both monicModularImages explicitly: `scale (lc gᵢ)⁻¹ gᵢ`.
      have hmm₁_eq :
          Hex.monicModularImage g₁ =
            Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g₁)⁻¹ g₁ :=
        monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hg₁_isZero
      have hmm₂_eq :
          Hex.monicModularImage g₂ =
            Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g₂)⁻¹ g₂ :=
        monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hg₂_isZero
      rw [hmm₁_eq, hmm₂_eq] at heqm
      -- Apply `scale (lc g₁)` to both sides to recover `g₁` on the LHS.
      have hscaled :
          Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g₁)
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g₁)⁻¹ g₁) =
          Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g₁)
            (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g₂)⁻¹ g₂) := by
        rw [heqm]
      rw [Hex.FpPoly.scale_scale,
          show Hex.DensePoly.leadingCoeff g₁ *
            (Hex.DensePoly.leadingCoeff g₁)⁻¹ = (1 : Hex.ZMod64 data.p) from
              Hex.ZMod64.mul_inv_eq_one_of_prime hprime hg₁_lead_ne,
          Hex.FpPoly.scale_one_left g₁,
          Hex.FpPoly.scale_scale] at hscaled
      -- Now `hscaled : g₁ = scale (lc g₁ * (lc g₂)⁻¹) g₂`.
      set u := Hex.DensePoly.leadingCoeff g₁ *
                 (Hex.DensePoly.leadingCoeff g₂)⁻¹ with hu_def
      have hu_ne : u ≠ (0 : Hex.ZMod64 data.p) := by
        intro h0
        rw [hu_def] at h0
        rcases Hex.ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero
            (Hex.ZMod64.PrimeModulus.prime (p := data.p)) h0 with h1 | h2
        · exact hg₁_lead_ne h1
        · exact (Hex.ZMod64.inv_ne_zero_of_prime hprime hg₂_lead_ne) h2
      have hg₁_eq_scale : g₁ = Hex.DensePoly.scale u g₂ := hscaled
      -- Then g₁ * g₂ = scale u (g₂²), and g₂² ∣ scale u (g₂²) since u ≠ 0.
      have hg₁g₂_eq : g₁ * g₂ = Hex.DensePoly.scale u (g₂ * g₂) := by
        rw [hg₁_eq_scale, Hex.FpPoly.scale_mul_left]
      have hg₂sq_dvd : g₂ * g₂ ∣ Hex.DensePoly.scale u (g₂ * g₂) := by
        refine ⟨Hex.DensePoly.C u, ?_⟩
        -- Goal: scale u (g₂ * g₂) = g₂ * g₂ * C u
        calc Hex.DensePoly.scale u (g₂ * g₂)
            = Hex.DensePoly.C u * (g₂ * g₂) := (Hex.FpPoly.C_mul_eq_scale u (g₂ * g₂)).symm
          _ = (g₂ * g₂) * Hex.DensePoly.C u :=
              Hex.DensePoly.mul_comm_poly _ _
      have hg₂sq_dvd_modP : g₂ * g₂ ∣ Hex.ZPoly.modP data.p f := by
        rw [hg₁g₂_eq] at hg₁g₂_dvd_modP
        exact fpPoly_dvd_trans hg₂sq_dvd hg₁g₂_dvd_modP
      -- Square-freeness implies g₂ is a unit polynomial (degree 0).
      have hunit : Hex.Berlekamp.isUnitPolynomial g₂ = true :=
        Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd hsf_common
          hg₂sq_dvd_modP
      have hdeg_zero : Hex.DensePoly.degree? g₂ = some 0 := by
        unfold Hex.Berlekamp.isUnitPolynomial at hunit
        cases hd : Hex.DensePoly.degree? g₂ with
        | none => rw [hd] at hunit; simp at hunit
        | some k =>
            rw [hd] at hunit
            cases k with
            | zero => rfl
            | succ _ => simp at hunit
      rw [hdeg_zero] at hg₂_pos
      simp at hg₂_pos
    · -- Degenerate case: the monic image has degree 0.  Then it has size ≤ 1,
      -- and the Berlekamp factor list is the singleton `[monicImage modP_f]`.
      -- Hence `g₁ = g₂` (both equal to the unique factor), contradicting `hne`.
      have hsize_le_one : (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).size ≤ 1 := by
        by_contra h
        push_neg at h
        apply hpos_image
        have hsize_ne : (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).size ≠ 0 := by
          omega
        unfold Hex.DensePoly.degree?
        simp [hsize_ne]
        omega
      have hfactors_eq :
          factors = [Hex.monicModularImage (Hex.ZPoly.modP data.p f)] :=
        Hex.Berlekamp.berlekampFactor_factors_eq_singleton_of_size_le_one
          (Hex.monicModularImage (Hex.ZPoly.modP data.p f))
          (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP data.p f) hzero)
          hsize_le_one
      rw [hfactors_eq] at hg₁ hg₂
      rw [List.mem_singleton] at hg₁ hg₂
      exact hne (hg₁.trans hg₂.symm)
  -- Transport `Nodup` from the post-mapped Berlekamp factor list to
  -- `data.factorsModP.toList`.
  rw [heq]
  simpa using List.Nodup.map_on hinj_on hNodup

/-- Discharge of the per-modular-factor natural-degree positivity premise on
`henselLiftData_liftedFactor_natDegree_pos`: given the `factorsModPBerlekampForm`
invariant (which records that `primeData.factorsModP` is the Berlekamp factor
array of the monic modular image of the input) together with a successful
`isGoodPrime` check and a positive-degree input polynomial, every modular factor
lifts back to a positive-natural-degree Mathlib polynomial over `ℤ`.

Proof: extract the existential witnesses from `factorsModPBerlekampForm` to view
`data.factorsModP` as the Berlekamp factor list of `monicModularImage (modP data.p f)`,
then apply the polymorphic abstract `Hex.Berlekamp.berlekampFactor_factors_pos_degree`.
The required positivity of the monic modular image follows from `isGoodPrime`'s
leading-coefficient admissibility (which preserves degree through `modP`) together
with the input's positive degree.  The route from `0 < g.degree?.getD 0` on each
`FpPoly p` factor to `0 < (toPolynomial (liftToZ g)).natDegree` on the integer
side is `HexPolyMathlib.natDegree_toPolynomial` plus the (inline) observation
that `liftToZ` preserves size on any nonzero `FpPoly p`.

This is the sibling of `factorsModP_nodup_of_factorsModPBerlekampForm`: it lets a
Mathlib-side caller of `henselLiftData_liftedFactor_natDegree_pos_of_choosePrimeData`
discharge the `hfactors_natDegree_pos` premise from the `choosePrimeData?` facts
alone, without constructing the per-modular-factor natural-degree witnesses by
hand. -/
theorem factorsModP_natDegree_pos_of_factorsModPBerlekampForm
    (f : Hex.ZPoly) (data : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm f data)
    (hgood :
      letI := data.bounds
      Hex.isGoodPrime f data.p = true)
    (hf_pos : 0 < f.degree?.getD 0) :
    letI := data.bounds
    ∀ g ∈ data.factorsModP,
      0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree := by
  letI : Hex.ZMod64.Bounds data.p := data.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime data.p data.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI : Hex.ZMod64.PrimeModulus data.p := Hex.ZMod64.primeModulusOfPrime hprime
  -- Step A: 0 < (monicModularImage (modP data.p f)).degree?.getD 0
  have hfsize_ge_two : 2 ≤ f.size := by
    unfold Hex.DensePoly.degree? at hf_pos
    by_cases hfs0 : f.size = 0
    · simp [hfs0] at hf_pos
    · simp [hfs0] at hf_pos
      omega
  have hfsize_pos : 0 < f.size := by omega
  have hadm : Hex.leadingCoeffAdmissible f data.p :=
    Hex.isGoodPrime_leadingCoeffAdmissible f data.p hgood
  have hcoeff_modP_ne :
      (Hex.ZPoly.modP data.p f).coeff (f.size - 1) ≠
        (0 : Hex.ZMod64 data.p) := by
    rw [Hex.ZPoly.coeff_modP, ← Hex.DensePoly.leadingCoeff_eq_coeff_last f hfsize_pos]
    exact hadm
  have hmodP_size_le : (Hex.ZPoly.modP data.p f).size ≤ f.size := by
    unfold Hex.ZPoly.modP Hex.FpPoly.ofCoeffs
    have := Hex.DensePoly.size_ofCoeffs_le
      (((List.range f.size).map fun i =>
          Hex.ZMod64.ofNat data.p (Hex.ZPoly.intModNat (f.coeff i) data.p)).toArray)
    simpa using this
  have hmodP_size_ge : f.size ≤ (Hex.ZPoly.modP data.p f).size := by
    by_contra h
    have hlt : (Hex.ZPoly.modP data.p f).size < f.size := Nat.not_le.mp h
    have hle : (Hex.ZPoly.modP data.p f).size ≤ f.size - 1 := Nat.le_pred_of_lt hlt
    exact hcoeff_modP_ne
      (Hex.DensePoly.coeff_eq_zero_of_size_le (Hex.ZPoly.modP data.p f) hle)
  have hmodP_size_eq : (Hex.ZPoly.modP data.p f).size = f.size :=
    Nat.le_antisymm hmodP_size_le hmodP_size_ge
  have hmodP_size_ge_two : 2 ≤ (Hex.ZPoly.modP data.p f).size := by
    rw [hmodP_size_eq]; exact hfsize_ge_two
  have hmod_size_pos : 0 < (Hex.ZPoly.modP data.p f).size := by omega
  have hmodP_lead_ne :
      Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP data.p f) ≠
        (0 : Hex.ZMod64 data.p) :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos (Hex.ZPoly.modP data.p f) hmod_size_pos
  have hinv_ne :
      (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP data.p f))⁻¹ ≠
        (0 : Hex.ZMod64 data.p) :=
    Hex.ZMod64.inv_ne_zero_of_prime hprime hmodP_lead_ne
  have hmonicImage_size :
      (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).size =
        (Hex.ZPoly.modP data.p f).size := by
    unfold Hex.monicModularImage
    simp only [hzero, Bool.false_eq_true, ↓reduceIte]
    exact Hex.FpPoly.scale_size_eq_of_ne_zero (p := data.p) hinv_ne _
  have hmonicImage_size_ge_two :
      2 ≤ (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).size := by
    rw [hmonicImage_size]; exact hmodP_size_ge_two
  have hmonicImage_pos :
      0 < (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).degree?.getD 0 := by
    unfold Hex.DensePoly.degree?
    have hne : (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).size ≠ 0 := by omega
    simp [hne]; omega
  -- Step B: positivity for every entry in the Berlekamp factor list.
  have hFactorsPos :
      ∀ h ∈ (@Hex.Berlekamp.berlekampFactor data.p data.bounds
              (Hex.monicModularImage (Hex.ZPoly.modP data.p f))
              (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP data.p f) hzero)
              hfield).factors,
        0 < h.degree?.getD 0 :=
    Hex.Berlekamp.berlekampFactor_factors_pos_degree
      (Hex.monicModularImage (Hex.ZPoly.modP data.p f))
      (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP data.p f) hzero)
      hmonicImage_pos
  -- Step C: transport positivity from FpPoly factors to integer-side `toPolynomial`.
  intro g hg
  -- Membership: g ∈ data.factorsModP corresponds to g = monicModularImage h for
  -- some h ∈ berlekampFactor.factors via heq.
  rw [heq] at hg
  simp only [List.mem_toArray, List.mem_map] at hg
  obtain ⟨h, hh_mem, rfl⟩ := hg
  -- Positivity of `h`.
  have hh_pos : 0 < h.degree?.getD 0 := hFactorsPos h hh_mem
  -- Show `monicModularImage h` has positive degree (preserved by nonzero scaling).
  have hh_size_pos : 0 < h.size := by
    unfold Hex.DensePoly.degree? at hh_pos
    by_cases hsz : h.size = 0
    · simp [hsz] at hh_pos
    · exact Nat.pos_of_ne_zero hsz
  have hh_lead_ne : Hex.DensePoly.leadingCoeff h ≠ (0 : Hex.ZMod64 data.p) :=
    Hex.FpPoly.leadingCoeff_ne_zero_of_pos_degree h hh_pos
  have hh_isZero : h.isZero = false :=
    (Hex.DensePoly.isZero_eq_false_iff _).mpr hh_size_pos
  have hg_degree_eq :
      (Hex.monicModularImage h).degree? = h.degree? := by
    unfold Hex.monicModularImage
    simp only [hh_isZero, Bool.false_eq_true, ↓reduceIte]
    exact Hex.FpPoly.scale_degree?_eq_of_ne_zero
      (Hex.ZMod64.inv_ne_zero_of_prime hprime hh_lead_ne) h
  have hg_pos : 0 < (Hex.monicModularImage h).degree?.getD 0 := by
    rw [hg_degree_eq]; exact hh_pos
  set g := Hex.monicModularImage h with hg_def
  -- Show 0 < g.size from hg_pos.
  have hg_size_pos : 0 < g.size := by
    unfold Hex.DensePoly.degree? at hg_pos
    by_cases hgz : g.size = 0
    · simp [hgz] at hg_pos
    · exact Nat.pos_of_ne_zero hgz
  -- Step: (liftToZ g).size = g.size, hence (liftToZ g).degree? = g.degree?.
  have hg_lead_ne : g.coeff (g.size - 1) ≠ (0 : Hex.ZMod64 data.p) :=
    Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hg_size_pos
  have hg_lead_toNat_ne : (g.coeff (g.size - 1)).toNat ≠ 0 := by
    intro h
    apply hg_lead_ne
    have heq_zero : g.coeff (g.size - 1) = Hex.ZMod64.zero := by
      apply (Hex.ZMod64.eq_iff_toNat_eq _ _).mpr
      rw [Hex.ZMod64.toNat_zero, h]
    exact heq_zero
  have hlift_coeff_ne :
      (Hex.FpPoly.liftToZ g).coeff (g.size - 1) ≠ (0 : Int) := by
    rw [Hex.FpPoly.coeff_liftToZ]
    intro h
    exact hg_lead_toNat_ne (by simpa [Int.ofNat_eq_zero] using h)
  have hlift_size_le : (Hex.FpPoly.liftToZ g).size ≤ g.size := by
    unfold Hex.FpPoly.liftToZ
    have := Hex.DensePoly.size_ofCoeffs_le
      (((List.range g.size).map fun i => Int.ofNat (g.coeff i).toNat).toArray)
    simpa using this
  have hlift_size_ge : g.size ≤ (Hex.FpPoly.liftToZ g).size := by
    by_contra h
    have hlt : (Hex.FpPoly.liftToZ g).size < g.size := Nat.not_le.mp h
    have hle : (Hex.FpPoly.liftToZ g).size ≤ g.size - 1 := Nat.le_pred_of_lt hlt
    exact hlift_coeff_ne
      (Hex.DensePoly.coeff_eq_zero_of_size_le (Hex.FpPoly.liftToZ g) hle)
  have hlift_size_eq : (Hex.FpPoly.liftToZ g).size = g.size :=
    Nat.le_antisymm hlift_size_le hlift_size_ge
  have hlift_degree_eq :
      (Hex.FpPoly.liftToZ g).degree? = g.degree? := by
    unfold Hex.DensePoly.degree?
    rw [hlift_size_eq]
  -- Conclude using natDegree_toPolynomial.
  have hnatDeg_eq :
      (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree =
        (Hex.FpPoly.liftToZ g).degree?.getD 0 :=
    HexPolyMathlib.natDegree_toPolynomial _
  rw [hnatDeg_eq, hlift_degree_eq]
  exact hg_pos

/-- For a monic integer polynomial `core` and a prime modulus `p > 1`, the
monic modular image of `modP p core` is just `modP p core` itself: the leading
coefficient of the modular image is `1` (since `core`'s is `1` and reduces to
`1` mod `p`), so the renormalisation scaling factor is `1⁻¹ = 1`. -/
private theorem monicModularImage_modP_eq_of_monic
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    (core : Hex.ZPoly) (hcore_monic : Hex.DensePoly.Monic core)
    (hprime : Hex.Nat.Prime p) (hp : 1 < p)
    (hzero : (Hex.ZPoly.modP p core).isZero = false) :
    Hex.monicModularImage (Hex.ZPoly.modP p core) = Hex.ZPoly.modP p core := by
  -- `core.size > 0` from monicness.
  have hcore_size_pos : 0 < core.size := zpoly_size_pos_of_monic hcore_monic
  have hcore_lead_one : core.coeff (core.size - 1) = 1 := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last core hcore_size_pos]
    exact hcore_monic
  -- `(1 : ZMod64 p).toNat = 1` (since `1 < p`).
  have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
  have htoNat_one : (1 : Hex.ZMod64 p).toNat = 1 := by
    show Hex.ZMod64.one.toNat = 1
    rw [Hex.ZMod64.toNat_one, hmod1]
  have hone_ne_zero_zmod : (1 : Hex.ZMod64 p) ≠ 0 := by
    intro h
    have hnat := congrArg Hex.ZMod64.toNat h
    rw [htoNat_one, show (0 : Hex.ZMod64 p) = Hex.ZMod64.zero from rfl,
        Hex.ZMod64.toNat_zero] at hnat
    exact (by decide : (1 : Nat) ≠ 0) hnat
  -- Leading coefficient of `modP p core` is `1`.
  have hmodP_coeff_lead :
      (Hex.ZPoly.modP p core).coeff (core.size - 1) = (1 : Hex.ZMod64 p) := by
    rw [Hex.ZPoly.coeff_modP, hcore_lead_one]
    have hintModNat : Hex.ZPoly.intModNat (1 : Int) p = 1 := by
      show Int.toNat ((1 : Int) % Int.ofNat p) = 1
      have hppos : (1 : Int) < Int.ofNat p := Int.ofNat_lt.mpr hp
      have h0 : (0 : Int) ≤ 1 := by decide
      rw [Int.emod_eq_of_lt h0 hppos]
      rfl
    rw [hintModNat]
    rfl
  -- Size of `modP p core` equals `core.size`.
  have hmodP_size_le : (Hex.ZPoly.modP p core).size ≤ core.size := by
    unfold Hex.ZPoly.modP Hex.FpPoly.ofCoeffs
    have := Hex.DensePoly.size_ofCoeffs_le
      (((List.range core.size).map fun i =>
          Hex.ZMod64.ofNat p (Hex.ZPoly.intModNat (core.coeff i) p)).toArray)
    simpa using this
  have hmodP_size_ge : core.size ≤ (Hex.ZPoly.modP p core).size := by
    by_contra hneg
    have hlt : (Hex.ZPoly.modP p core).size < core.size := Nat.not_le.mp hneg
    have hle : (Hex.ZPoly.modP p core).size ≤ core.size - 1 := Nat.le_pred_of_lt hlt
    have hzero_coeff :
        (Hex.ZPoly.modP p core).coeff (core.size - 1) = 0 :=
      Hex.DensePoly.coeff_eq_zero_of_size_le _ hle
    rw [hzero_coeff] at hmodP_coeff_lead
    exact hone_ne_zero_zmod hmodP_coeff_lead.symm
  have hmodP_size_eq : (Hex.ZPoly.modP p core).size = core.size :=
    Nat.le_antisymm hmodP_size_le hmodP_size_ge
  have hmodP_size_pos : 0 < (Hex.ZPoly.modP p core).size := by
    rw [hmodP_size_eq]; exact hcore_size_pos
  -- Leading coefficient of `modP p core` is `1`.
  have hmodP_lead_one :
      Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP p core) = (1 : Hex.ZMod64 p) := by
    rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred _ hmodP_size_pos, hmodP_size_eq]
    exact hmodP_coeff_lead
  -- `(1 : ZMod64 p)⁻¹ = 1`.
  have hone_inv : (1 : Hex.ZMod64 p)⁻¹ = (1 : Hex.ZMod64 p) := by
    show Hex.ZMod64.inv (1 : Hex.ZMod64 p) = (1 : Hex.ZMod64 p)
    have hone_mul :
        Hex.ZMod64.mul (Hex.ZMod64.inv (1 : Hex.ZMod64 p)) (1 : Hex.ZMod64 p) = 1 :=
      Hex.ZMod64.inv_mul_eq_one_of_prime hprime hone_ne_zero_zmod
    rw [Hex.ZMod64.eq_iff_toNat_eq]
    have htoNat_eq := congrArg Hex.ZMod64.toNat hone_mul
    rw [Hex.ZMod64.toNat_mul, htoNat_one, Nat.mul_one] at htoNat_eq
    have hinv_lt : (Hex.ZMod64.inv (1 : Hex.ZMod64 p)).toNat < p :=
      (Hex.ZMod64.inv (1 : Hex.ZMod64 p)).isLt
    rw [Nat.mod_eq_of_lt hinv_lt] at htoNat_eq
    rw [htoNat_one]; exact htoNat_eq
  -- Combine: `monicModularImage = scale 1⁻¹ (modP p core) = scale 1 (modP p core) = modP p core`.
  unfold Hex.monicModularImage
  simp only [hzero, Bool.false_eq_true, ↓reduceIte]
  rw [hmodP_lead_one, hone_inv, Hex.FpPoly.scale_one_left]

/-- Reducing a `polyProduct` of canonically-lifted `FpPoly p` factors back
modulo `p` recovers the in-field `factorProduct`.  This identifies the
integer-side product carried by `Array.polyProduct` with the
`FpPoly p`-side product `Hex.Berlekamp.factorProduct`, threading the
multiplicative-homomorphism property of `modP` through each lifted factor.

Shared base lemma for both
`factorsModP_polyProduct_congr_of_factorsModPBerlekampForm` (via the
`polyProduct_map_liftToZ_congr_factorProduct` corollary just below) and
`factorsModP_coprime_of_factorsModPBerlekampForm` (which rewrites
`modP p (Array.polyProduct ...)` to the direct `factorProduct`
viewpoint where pairwise-coprime arguments apply). -/
private theorem modP_polyProduct_liftToZ_eq_factorProduct
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    (xs : List (Hex.FpPoly p)) :
    Hex.ZPoly.modP p (Array.polyProduct ((xs.map Hex.FpPoly.liftToZ).toArray)) =
      Hex.Berlekamp.factorProduct xs := by
  induction xs with
  | nil =>
      show Hex.ZPoly.modP p (Array.polyProduct (#[] : Array Hex.ZPoly)) =
        Hex.Berlekamp.factorProduct ([] : List (Hex.FpPoly p))
      rw [Hex.ZPoly.polyProduct_empty]
      exact Hex.ZPoly.modP_one p
  | cons x rest ih =>
      have hcons :
          Array.polyProduct (((x :: rest).map Hex.FpPoly.liftToZ).toArray) =
            Hex.FpPoly.liftToZ x *
              Array.polyProduct ((rest.map Hex.FpPoly.liftToZ).toArray) := by
        rw [List.map_cons]
        exact Hex.ZPoly.polyProduct_cons_toArray (Hex.FpPoly.liftToZ x) _
      rw [hcons, Hex.ZPoly.modP_lift_mul_left p x _, ih,
        Hex.Berlekamp.factorProduct_cons]

/-- Identification of the FpPoly factor product with the integer-side ordered
product through `liftToZ`: lifting a foldl product is congruent mod `p` to the
foldl product of the lifts. Stated as a list-level helper so we can apply it
after unfolding `factorsModP.toList`.

Corollary of `modP_polyProduct_liftToZ_eq_factorProduct`: that lemma reduces
the `polyProduct` of lifted factors back to `factorProduct`, and
`congr_liftToZ_of_modP_eq` then converts the equation into the `congr` shape
expected by the `_polyProduct_congr_` discharger. -/
private theorem polyProduct_map_liftToZ_congr_factorProduct
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    (factors : List (Hex.FpPoly p)) :
    Hex.ZPoly.congr
      (Array.polyProduct ((factors.map Hex.FpPoly.liftToZ).toArray))
      (Hex.FpPoly.liftToZ (Hex.Berlekamp.factorProduct factors))
      p :=
  Hex.ZPoly.congr_symm _ _ _
    (Hex.ZPoly.congr_liftToZ_of_modP_eq p _ _
      (modP_polyProduct_liftToZ_eq_factorProduct factors))

/-- Primitive + positive-leading-coefficient sibling of
`factorsModP_polyProduct_congr_of_factorsModPBerlekampForm`: the
Berlekamp factor product over `primeData.factorsModP` is congruent mod
`p` to `liftToZ (monicModularImage (modP p core))`, the canonical monic
representative of `modP p core`.

The proof mirrors the monic version up to (but not including) the
`monicModularImage_modP_eq_of_monic` collapse: `factorProduct` on the
raw Berlekamp factor list returns the monic input
`monicModularImage (modP p core)` by `factorProduct_berlekampFactor`,
`factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct`
pushes `monicModularImage` through the outer map, and
`monicModularImage_eq_self_of_monic` collapses the resulting double
application because `monicModularImage (modP p core)` is already monic
(via `monicModularImage_monic`).  The monic wrapper above adds the
final `monicModularImage (modP p core) = modP p core` step that
requires `hcore_monic`.

`_hcore_primitive`, `_hcore_lc_pos`, and `_hgood` are not consumed by
the proof; they are threaded for API parity with the broader
`_of_primitive_pos_lc_core` propagation chain. -/
theorem factorsModP_polyProduct_congr_of_factorsModPBerlekampForm_of_primitive_pos_lc_core
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (_hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (_hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true) :
    letI := primeData.bounds
    Hex.ZPoly.congr
      (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
      (Hex.FpPoly.liftToZ
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)))
      primeData.p := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  -- `monicModularImage (modP p core)` is monic.
  have hmonicImage_monic :
      Hex.DensePoly.Monic (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  -- Raw Berlekamp factor list of the monic image.
  let raw :=
      (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
        hmonicImage_monic hfield).factors
  -- `factorProduct raw = monicModularImage (modP p core)` (input recovered;
  -- no `hcore_monic` needed here — the monic premise of `factorProduct_berlekampFactor`
  -- is supplied by `monicModularImage_monic`).
  have hprod_eq_raw :
      Hex.Berlekamp.factorProduct raw =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    show Hex.Berlekamp.factorProduct
        (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
          hmonicImage_monic hfield).factors = _
    rw [Hex.Berlekamp.factorProduct_berlekampFactor]
  -- Each raw factor is nonzero.
  have hraw_ne : ∀ g ∈ raw, g ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic
  -- `monicModularImage` is idempotent on its own image (the image is monic).
  have hmonicImage_idem :
      Hex.monicModularImage (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) :=
    Hex.monicModularImage_eq_self_of_monic hprime _ hmonicImage_monic
  -- Push `monicModularImage` through `factorProduct`, then apply idempotence:
  -- `factorProduct (raw.map monicModularImage) = monicModularImage (factorProduct raw)
  --   = monicModularImage (monicModularImage (modP p core))
  --   = monicModularImage (modP p core)`.
  have hprod_eq_mapped :
      Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    rw [Hex.factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct
        hprime raw hraw_ne, hprod_eq_raw, hmonicImage_idem]
  -- Apply the lift-congruence lemma at the *mapped* Berlekamp factor list.
  have hbridge :=
    polyProduct_map_liftToZ_congr_factorProduct (p := primeData.p)
      (raw.map Hex.monicModularImage)
  rw [hprod_eq_mapped] at hbridge
  -- `primeData.factorsModP = (raw.map monicModularImage).toArray` by `heq`.
  rw [heq, List.map_toArray]
  exact hbridge

/-- Discharge of the `polyProduct (factorsModP.map liftToZ) ≡ core (mod p)`
premise on `henselLiftData_liftedFactor_monic_of_choosePrimeData` (and the two
other umbrellas at lines 4549, 4613) from the `factorsModPBerlekampForm`
invariant plus a successful `isGoodPrime` check.  Requires `core` to be monic
so that the leading coefficient of `modP p core` is `1`, hence
`monicModularImage (modP p core) = modP p core`; under that identification
the `_of_primitive_pos_lc_core` sibling above (which lands at
`liftToZ (monicModularImage (modP p core))`) collapses to `liftToZ (modP p core)`,
and the lift to the integer side is closed by `congr_liftToZ_modP`.

The added `hcore_monic` premise costs downstream callers nothing: the
umbrellas they feed already require it.  No additional `1 < p` premise is
needed; it is derived from `hprime`'s `two_le`. -/
theorem factorsModP_polyProduct_congr_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true) :
    letI := primeData.bounds
    Hex.ZPoly.congr
      (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
      core primeData.p := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hp : 1 < primeData.p := by have := hprime.two_le; omega
  -- `monicModularImage (modP p core) = modP p core` (because `core` is monic).
  have hmonicImage_eq :
      Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) =
        Hex.ZPoly.modP primeData.p core :=
    monicModularImage_modP_eq_of_monic core hcore_monic hprime hp hzero
  -- Delegate to the `_of_primitive_pos_lc_core` sibling, landing at
  -- `liftToZ (monicModularImage (modP p core))`; the monic-image layer
  -- is a no-op on monic input, so `rw [hmonicImage_eq]` collapses it.
  have hcongr_mon :=
    factorsModP_polyProduct_congr_of_factorsModPBerlekampForm_of_primitive_pos_lc_core
      core primeData
      (zpoly_primitive_of_monic hcore_monic)
      (hcore_monic ▸ (by decide : (0 : Int) < 1))
      ⟨hprime, hzero, heq⟩ hgood
  rw [hmonicImage_eq] at hcongr_mon
  -- Close to `≡ core (mod p)` via `congr_liftToZ_modP`.
  exact Hex.ZPoly.congr_trans _ _ _ _ hcongr_mon (Hex.FpPoly.congr_liftToZ_modP core)

/-- Discharge of the `primeData.factorsModP.toList ≠ []` premise on the lifted-factor
umbrellas: the `factorsModPBerlekampForm` invariant records that
`primeData.factorsModP` is exactly the Berlekamp factor array of the monic modular
image, and `Hex.Berlekamp.berlekampFactor_factors_ne_nil` guarantees the Berlekamp
factor list is nonempty for any monic input.

No `hgood` premise is needed: nonemptiness is preserved by `berlekampFactor`
regardless of square-freeness, and `factorsModPBerlekampForm` already bundles the
nonzero-image witness used to construct the monic image.

Used together with `factorsModP_monic_*`, `factorsModP_polyProduct_congr_*`, and
`factorsModP_coprime_*` to discharge the four `QuadraticMultifactorLiftInvariant`
boundary hypotheses fed into the umbrellas via
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData`. -/
theorem factorsModP_ne_nil_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm core primeData) :
    primeData.factorsModP.toList ≠ [] := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  have hbl_ne :
      (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
        (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero)
        hfield).factors ≠ [] :=
    Hex.Berlekamp.berlekampFactor_factors_ne_nil
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      (Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero)
  rw [heq]
  simpa [List.map_eq_nil_iff] using hbl_ne

/-- Generalized inductive helper for the `factorsModP_coprime` discharger.

For any list of factors in `FpPoly p` whose `factorProduct` divides a
nonzero polynomial `X` with no positive-degree squared divisor, the
recursive predicate `Hex.ZPoly.QuadraticMultifactorCoprimeSplits` holds.

The recursion peels one head factor `g` off at a time:
* `xgcd.gcd = 1` follows from the pairwise-coprime view of `g` against
  `factorProduct rest`, identified via `modP_polyProduct_liftToZ_eq_factorProduct`.
* The recursive tail satisfies the same divisibility-into-`X` invariant via
  `factorProduct rest ∣ factorProduct (g :: rest) ∣ X`. -/
private theorem quadraticMultifactorCoprimeSplits_of_factorProduct_no_squared
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    [Lean.Grind.Field (Hex.ZMod64 p)]
    (X : Hex.FpPoly p)
    (hX_ne : X ≠ 0)
    (h_no_squared : ∀ d : Hex.FpPoly p,
        d * d ∣ X → ¬ (0 < d.degree?.getD 0))
    (xs : List (Hex.FpPoly p))
    (h_dvd : Hex.Berlekamp.factorProduct xs ∣ X) :
    Hex.ZPoly.QuadraticMultifactorCoprimeSplits p xs := by
  induction xs with
  | nil => exact True.intro
  | cons g rest ih =>
      cases rest with
      | nil => exact True.intro
      | cons h tail =>
          -- The recursive predicate at `g :: h :: tail` expects
          -- `xgcd.gcd = 1` and `QuadraticMultifactorCoprimeSplits p (h :: tail)`.
          refine ⟨?_, ?_⟩
          · -- `xgcd.gcd = 1` for the head split.
            -- Unfold `normalizedXGCD` and identify the raw EEA gcd.
            change
              (Hex.ZPoly.normalizedXGCD p (Hex.FpPoly.liftToZ g)
                (Array.polyProduct
                  (((h :: tail).map Hex.FpPoly.liftToZ).toArray))).gcd =
                (1 : Hex.FpPoly p)
            -- Reduce both `modP`-arguments to `FpPoly p` shape.
            have hmodP_g : Hex.ZPoly.modP p (Hex.FpPoly.liftToZ g) = g :=
              Hex.FpPoly.modP_liftToZ g
            have hmodP_tail :
                Hex.ZPoly.modP p
                    (Array.polyProduct
                      (((h :: tail).map Hex.FpPoly.liftToZ).toArray)) =
                  Hex.Berlekamp.factorProduct (h :: tail) :=
              modP_polyProduct_liftToZ_eq_factorProduct (h :: tail)
            -- The raw EEA gcd is `DensePoly.gcd g (factorProduct (h :: tail))`.
            set rawGcd : Hex.FpPoly p :=
              Hex.DensePoly.gcd g (Hex.Berlekamp.factorProduct (h :: tail))
              with hrawGcd_def
            -- `normalizedXGCD.gcd = scale (lc⁻¹) rawGcd`.
            have hnorm_def :
                (Hex.ZPoly.normalizedXGCD p (Hex.FpPoly.liftToZ g)
                  (Array.polyProduct
                    (((h :: tail).map Hex.FpPoly.liftToZ).toArray))).gcd =
                  Hex.DensePoly.scale
                    (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ rawGcd := by
              show Hex.DensePoly.scale
                  (Hex.DensePoly.leadingCoeff
                    (Hex.DensePoly.xgcd
                      (Hex.ZPoly.modP p (Hex.FpPoly.liftToZ g))
                      (Hex.ZPoly.modP p
                        (Array.polyProduct
                          (((h :: tail).map Hex.FpPoly.liftToZ).toArray)))).gcd)⁻¹
                  (Hex.DensePoly.xgcd
                    (Hex.ZPoly.modP p (Hex.FpPoly.liftToZ g))
                    (Hex.ZPoly.modP p
                      (Array.polyProduct
                        (((h :: tail).map Hex.FpPoly.liftToZ).toArray)))).gcd =
                Hex.DensePoly.scale
                  (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ rawGcd
              rw [hmodP_g, hmodP_tail, hrawGcd_def]
              rfl
            rw [hnorm_def]
            -- The rest: show `scale (lc rawGcd)⁻¹ rawGcd = 1`.  This needs
            -- `rawGcd` to be a nonzero constant in `FpPoly p`.
            -- Step 1: `rawGcd² ∣ X`.
            have hrawGcd_dvd_g : rawGcd ∣ g :=
              Hex.DensePoly.gcd_dvd_left g (Hex.Berlekamp.factorProduct (h :: tail))
            have hrawGcd_dvd_tail :
                rawGcd ∣ Hex.Berlekamp.factorProduct (h :: tail) :=
              Hex.DensePoly.gcd_dvd_right g (Hex.Berlekamp.factorProduct (h :: tail))
            have hrawGcd_sq_dvd_prod :
                rawGcd * rawGcd ∣ g * Hex.Berlekamp.factorProduct (h :: tail) :=
              fpPoly_mul_dvd_mul hrawGcd_dvd_g hrawGcd_dvd_tail
            have hcons_prod :
                g * Hex.Berlekamp.factorProduct (h :: tail) =
                  Hex.Berlekamp.factorProduct (g :: h :: tail) :=
              (Hex.Berlekamp.factorProduct_cons g (h :: tail)).symm
            have hrawGcd_sq_dvd_X : rawGcd * rawGcd ∣ X := by
              rw [hcons_prod] at hrawGcd_sq_dvd_prod
              exact fpPoly_dvd_trans hrawGcd_sq_dvd_prod h_dvd
            -- Step 2: rawGcd has degree ≤ 0 by no-squared on X.
            have hrawGcd_not_pos :
                ¬ (0 < rawGcd.degree?.getD 0) :=
              h_no_squared rawGcd hrawGcd_sq_dvd_X
            -- Step 3: rawGcd ≠ 0 (via `rawGcd * rawGcd ∣ X` with `X ≠ 0`).
            have hrawGcd_ne : rawGcd ≠ 0 := by
              intro hraw
              apply hX_ne
              rcases hrawGcd_sq_dvd_X with ⟨k, hk⟩
              rw [hraw, Hex.FpPoly.zero_mul, Hex.FpPoly.zero_mul] at hk
              exact hk
            -- Step 4: rawGcd.size = 1.
            have hrawGcd_size_pos : 0 < rawGcd.size := by
              apply Nat.pos_of_ne_zero
              intro hsize
              apply hrawGcd_ne
              apply Hex.DensePoly.ext_coeff
              intro i
              rw [Hex.DensePoly.coeff_zero]
              exact Hex.DensePoly.coeff_eq_zero_of_size_le rawGcd (by omega)
            have hrawGcd_size_one : rawGcd.size = 1 := by
              by_contra hsize_ne
              apply hrawGcd_not_pos
              have hsize_ge_two : 2 ≤ rawGcd.size := by omega
              have hdeg_form : rawGcd.degree? = some (rawGcd.size - 1) := by
                unfold Hex.DensePoly.degree?
                have hne : rawGcd.size ≠ 0 := Nat.pos_iff_ne_zero.mp hrawGcd_size_pos
                simp [hne]
              rw [hdeg_form]; simp; omega
            -- Step 5: lc rawGcd ≠ 0.
            have hlc_ne :
                Hex.DensePoly.leadingCoeff rawGcd ≠ (0 : Hex.ZMod64 p) :=
              fpPoly_leadingCoeff_ne_zero_of_size_pos rawGcd hrawGcd_size_pos
            -- Step 6: rawGcd.coeff 0 = lc rawGcd.
            have hrawGcd_coeff_zero :
                rawGcd.coeff 0 = Hex.DensePoly.leadingCoeff rawGcd := by
              rw [Hex.FpPoly.leadingCoeff_eq_coeff_pred rawGcd hrawGcd_size_pos]
              congr 1; omega
            -- Step 7: scale lc⁻¹ rawGcd = 1.
            apply Hex.DensePoly.ext_coeff
            intro n
            have hzero_mul :
                (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ * (0 : Hex.ZMod64 p) = 0 :=
              Lean.Grind.Semiring.mul_zero _
            rw [Hex.DensePoly.coeff_scale
              (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ rawGcd n hzero_mul]
            change (Hex.DensePoly.leadingCoeff rawGcd)⁻¹ * rawGcd.coeff n =
              (Hex.DensePoly.C (1 : Hex.ZMod64 p)).coeff n
            rw [Hex.DensePoly.coeff_C]
            cases n with
            | zero =>
                rw [hrawGcd_coeff_zero]
                simp
                exact Hex.ZMod64.inv_mul_eq_one_of_prime
                  (Hex.ZMod64.PrimeModulus.prime (p := p)) hlc_ne
            | succ k =>
                have hcoeff_zero : rawGcd.coeff (k + 1) = (0 : Hex.ZMod64 p) :=
                  Hex.DensePoly.coeff_eq_zero_of_size_le rawGcd (by omega)
                rw [hcoeff_zero, if_neg (Nat.succ_ne_zero k)]
                exact hzero_mul
          · -- Inductive call on `h :: tail`.
            have hrest_dvd :
                Hex.Berlekamp.factorProduct (h :: tail) ∣ X := by
              have hcons_eq :
                  Hex.Berlekamp.factorProduct (g :: h :: tail) =
                    g * Hex.Berlekamp.factorProduct (h :: tail) :=
                Hex.Berlekamp.factorProduct_cons g (h :: tail)
              have htail_dvd_cons :
                  Hex.Berlekamp.factorProduct (h :: tail) ∣
                    Hex.Berlekamp.factorProduct (g :: h :: tail) := by
                refine ⟨g, ?_⟩
                rw [hcons_eq]; exact Hex.DensePoly.mul_comm_poly _ _
              exact fpPoly_dvd_trans htail_dvd_cons h_dvd
            exact ih hrest_dvd

set_option maxHeartbeats 400000 in
/-- Discharge of the coprime-splits boundary premise on
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData`: given the
`factorsModPBerlekampForm` invariant (which records that `primeData.factorsModP`
is the Berlekamp factor array of the monic modular image of the input)
together with a successful `isGoodPrime` check, the recursive sequential-split
coprime predicate `QuadraticMultifactorCoprimeSplits` holds on the stored
factor list.

Proof: extract the Berlekamp witnesses from `hform`; transport modular
squarefreeness from `isGoodPrime` through `monicModularImage`; apply the
generalized `quadraticMultifactorCoprimeSplits_of_factorProduct_no_squared`
helper with `X := monicModularImage (modP p core)` to walk the list.  The
no-squared invariant on the modular image is the local Mathlib-side form
of `gcd_monicModularImage_derivative_eq_one`, instantiated through
`Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd`.

This is the third in the chain of `factorsModP`-side dischargers
(`factorsModP_nodup_of_factorsModPBerlekampForm`,
`factorsModP_natDegree_pos_of_factorsModPBerlekampForm`, this one), each
mapping the abstract `factorsModPBerlekampForm` invariant plus an
`isGoodPrime` certificate to a piece of the four-tuple
`(hfactors_monic, hproduct_mod_p, hcoprime, hnonempty)` that the umbrella
`QuadraticMultifactorLiftInvariant_of_choosePrimeData` consumes.

The Option-3 wrap of `berlekampFactorsModP` (apply `monicModularImage` per
factor) lifts the helper application from the raw Berlekamp factor list to
the mapped list via the multiplicativity lemma
`factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct`. -/
theorem factorsModP_coprime_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true) :
    letI := primeData.bounds
    Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
      primeData.factorsModP.toList := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  -- The modular image is square-free under `isGoodPrime`.
  have hsf_common :
      ∀ d : Hex.FpPoly primeData.p,
        d ∣ Hex.ZPoly.modP primeData.p core →
        d ∣ Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core) →
        Hex.Berlekamp.isUnitPolynomial d = true :=
    squareFree_common_of_squareFreeModP core
      (Hex.isGoodPrime_squareFreeModP core primeData.p hgood)
  -- `monicModularImage` divides `modP p core`, so the no-squared invariant
  -- transports through the unit scaling.
  have hmonicImage_dvd :
      Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) ∣
        Hex.ZPoly.modP primeData.p core :=
    monicModularImage_dvd_self_of_isZero_false hprime hzero
  -- The no-squared invariant on the monic modular image.
  have h_no_squared :
      ∀ d : Hex.FpPoly primeData.p,
        d * d ∣ Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) →
          ¬ (0 < d.degree?.getD 0) := by
    intro d hdd hpos
    have hd_dvd_mod : d * d ∣ Hex.ZPoly.modP primeData.p core :=
      fpPoly_dvd_trans hdd hmonicImage_dvd
    have hunit : Hex.Berlekamp.isUnitPolynomial d = true :=
      Hex.Berlekamp.isUnitPolynomial_of_squareFree_of_squared_dvd hsf_common
        hd_dvd_mod
    have hdeg : Hex.DensePoly.degree? d = some 0 := by
      unfold Hex.Berlekamp.isUnitPolynomial at hunit
      cases hd : Hex.DensePoly.degree? d with
      | none => rw [hd] at hunit; simp at hunit
      | some k =>
          rw [hd] at hunit
          cases k with
          | zero => rfl
          | succ _ => simp at hunit
    rw [hdeg] at hpos
    simp at hpos
  -- Monic image is monic (consumed by Berlekamp's signature and idempotence).
  have hmonicImage_monic :
      Hex.DensePoly.Monic (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  -- Raw Berlekamp factor list: under the Option-3 wrap, `primeData.factorsModP`
  -- is `raw.map monicModularImage` (then `.toArray`), so the helper must be
  -- applied at the mapped list.
  let raw :=
      (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
        hmonicImage_monic hfield).factors
  -- The Berlekamp factor list has product equal to the monic modular image.
  have h_factorProduct :
      Hex.Berlekamp.factorProduct raw =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) :=
    Hex.Berlekamp.factorProduct_berlekampFactor _ _
  -- Monic modular image is nonzero (it's a nonzero scalar of a nonzero poly).
  have hmonicImage_ne :
      Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) ≠ 0 := by
    apply Hex.monicModularImage_ne_zero_of_ne_zero hprime
    intro hmod_zero
    rw [hmod_zero] at hzero
    have hzero_true : (0 : Hex.FpPoly primeData.p).isZero = true := rfl
    rw [hzero_true] at hzero
    exact Bool.noConfusion hzero
  -- Each raw Berlekamp factor is nonzero (positive degree typically, singleton
  -- [monicImg] in the degenerate size-≤-1 case).
  have hraw_ne : ∀ g ∈ raw, g ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic
  -- Push `monicModularImage` through `factorProduct`: the mapped product
  -- equals `monicModularImage (factorProduct raw) = monicModularImage (monicImg)
  -- = monicImg` (the last step uses that `monicImg` is already monic).
  have hprod_mapped :
      Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    rw [Hex.factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct
        hprime raw hraw_ne]
    rw [h_factorProduct]
    exact Hex.monicModularImage_eq_self_of_monic hprime _ hmonicImage_monic
  -- Apply the generalized helper at the mapped list.
  have h_dvd_X_mapped :
      Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage) ∣
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    rw [hprod_mapped]
    exact Hex.DensePoly.dvd_refl_poly _
  have hcps :
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        (raw.map Hex.monicModularImage) :=
    quadraticMultifactorCoprimeSplits_of_factorProduct_no_squared
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_ne h_no_squared _ h_dvd_X_mapped
  -- Transport to the `factorsModP.toList` view.
  rw [heq]
  simpa using hcps

/-- Discharge of the per-modular-factor monicness premise on
`henselLiftData_liftedFactor_monic_of_choosePrimeData` (and the two other
umbrellas at lines 5136 and 5200) from the `factorsModPBerlekampForm` invariant
alone.

`primeData.factorsModP` is, under the Option-3 wrap in `berlekampFactorsModP`,
exactly `((berlekampFactor monicImg).factors.map monicModularImage).toArray`.
Every entry is therefore the `monicModularImage` of some raw Berlekamp factor,
which is monic by `monicModularImage_monic` provided the raw factor is nonzero.
The raw-factor nonzeroness is `berlekampFactor_factors_ne_zero` (positive-degree
case via `berlekampFactor_factors_pos_degree`, degenerate `[monicImg]` case
because `monicImg` is monic).

No `hgood` or `hcore_monic` premise is needed: the discharge follows from the
shape of `factorsModPBerlekampForm` and Berlekamp-output structural facts
alone.  This is the fourth and last of the
`QuadraticMultifactorLiftInvariant` boundary dischargers (together with
`factorsModP_ne_nil_*`, `factorsModP_polyProduct_congr_*`, and
`factorsModP_coprime_*`) that the umbrellas consume via
`QuadraticMultifactorLiftInvariant_of_choosePrimeData`. -/
theorem factorsModP_monic_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm core primeData) :
    letI := primeData.bounds
    ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hmonicImage_monic :
      Hex.DensePoly.Monic (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  -- Each entry of `factorsModP` is `monicModularImage g'` for some `g'` in the
  -- raw Berlekamp output, and each such `g'` is nonzero.
  intro g hg
  rw [heq] at hg
  rw [List.mem_toArray, List.mem_map] at hg
  obtain ⟨g', hg'_mem, hg'_eq⟩ := hg
  have hg'_ne : g' ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic g' hg'_mem
  rw [← hg'_eq]
  exact Hex.monicModularImage_monic hprime g' (Hex.isZero_false_of_ne_zero hg'_ne)

/-- Square-freeness of a nonzero `FpPoly` transfers to its monic representative.

Local copy of the IntReductionMod helper of the same name (the canonical
version lives at `HexBerlekampZassenhausMathlib/IntReductionMod.lean:307`).
Duplicated here because `IntReductionMod` imports `Basic`; the proof routes
through `IsCoprime` in `Polynomial (ZMod p)` using
`toMathlibPolynomial_squareFree_coprime` and the `toMathlibPolynomial_scale`
identification for the unit scalar `(leadingCoeff f)⁻¹`. -/
private theorem gcd_monicModularImage_derivative_eq_one_local
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p) (hzero : f.isZero = false)
    (hsquareFree : Hex.DensePoly.gcd f (Hex.DensePoly.derivative f) = 1) :
    Hex.DensePoly.gcd (Hex.monicModularImage f)
        (Hex.DensePoly.derivative (Hex.monicModularImage f)) = 1 := by
  let u : Hex.ZMod64 p := (Hex.DensePoly.leadingCoeff f)⁻¹
  have hmonic_eq : Hex.monicModularImage f = Hex.DensePoly.scale u f := by
    simpa [u] using
      monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hzero
  have hcop :
      IsCoprime
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))) := by
    have hcop_f :
        IsCoprime
          (HexBerlekampMathlib.toMathlibPolynomial f)
          (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f)) :=
      HexBerlekampMathlib.toMathlibPolynomial_squareFree_coprime f hsquareFree
    have hu_ne : HexModArithMathlib.ZMod64.toZMod u ≠ 0 := by
      have hp_hex : Hex.Nat.Prime p := by
        constructor
        · exact (Fact.out : Nat.Prime p).two_le
        · intro m hmdvd
          rcases (Fact.out : Nat.Prime p).eq_one_or_self_of_dvd m hmdvd with h | h
          · exact Or.inl h
          · exact Or.inr h
      have hlead_ne : Hex.DensePoly.leadingCoeff f ≠ 0 :=
        fpPoly_leadingCoeff_ne_zero_of_size_pos f
          ((Hex.DensePoly.isZero_eq_false_iff _).mp hzero)
      intro hu_zero
      have hone_hex : u * Hex.DensePoly.leadingCoeff f = (1 : Hex.ZMod64 p) := by
        simpa [u] using Hex.ZMod64.inv_mul_eq_one_of_prime hp_hex hlead_ne
      have hone_z :
          HexModArithMathlib.ZMod64.toZMod u *
              HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff f) =
            (1 : ZMod p) := by
        rw [← HexModArithMathlib.ZMod64.toZMod_mul, hone_hex,
          HexModArithMathlib.ZMod64.toZMod_one]
      rw [hu_zero, zero_mul] at hone_z
      exact zero_ne_one hone_z
    have hC_unit :
        IsUnit (Polynomial.C (HexModArithMathlib.ZMod64.toZMod u)) :=
      Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hu_ne)
    rw [hmonic_eq, toMathlibPolynomial_scale]
    rw [Polynomial.derivative_C_mul]
    exact (isCoprime_mul_unit_left hC_unit
      (HexBerlekampMathlib.toMathlibPolynomial f)
      (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f))).mpr hcop_f
  have hmath_gcd :
      gcd
        (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
        (Polynomial.derivative
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))) = 1 := by
    have hunit :
        IsUnit
          (gcd
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
            (Polynomial.derivative
              (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) :=
      gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
    have hnorm :
        normalize
          (gcd
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
            (Polynomial.derivative
              (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) =
        gcd
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
          (Polynomial.derivative
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))) :=
      normalize_gcd _ _
    have hone :
        normalize
          (gcd
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
            (Polynomial.derivative
              (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) = 1 :=
      normalize_eq_one.mpr hunit
    simpa [hnorm] using hone
  apply HexBerlekampMathlib.fpPolyEquiv.injective
  change
    HexBerlekampMathlib.toMathlibPolynomial
        (Hex.DensePoly.gcd (Hex.monicModularImage f)
          (Hex.DensePoly.derivative (Hex.monicModularImage f))) =
      HexBerlekampMathlib.toMathlibPolynomial (1 : Hex.FpPoly p)
  rw [HexBerlekampMathlib.toMathlibPolynomial_gcd,
      HexBerlekampMathlib.toMathlibPolynomial_derivative,
      toMathlibPolynomial_one]
  exact hmath_gcd

private theorem derivative_scale_local
    {p : Nat} [Hex.ZMod64.Bounds p]
    (c : Hex.ZMod64 p) (f : Hex.FpPoly p) :
    Hex.DensePoly.derivative (Hex.DensePoly.scale c f) =
      Hex.DensePoly.scale c (Hex.DensePoly.derivative f) := by
  apply Hex.DensePoly.ext_coeff
  intro n
  have hzero_d : ((n + 1 : Nat) : Hex.ZMod64 p) *
      (Zero.zero : Hex.ZMod64 p) = (Zero.zero : Hex.ZMod64 p) :=
    Lean.Grind.Semiring.mul_zero _
  have hzero_s : c * (Zero.zero : Hex.ZMod64 p) =
      (Zero.zero : Hex.ZMod64 p) :=
    Lean.Grind.Semiring.mul_zero _
  rw [Hex.DensePoly.coeff_derivative _ _ hzero_d,
      Hex.DensePoly.coeff_scale c (Hex.DensePoly.derivative f) n hzero_s,
      Hex.DensePoly.coeff_derivative _ _ hzero_d,
      Hex.DensePoly.coeff_scale c f (n + 1) hzero_s]
  grind

private theorem dvd_trans_FpPoly_local
    {p : Nat} [Hex.ZMod64.Bounds p] {a b c : Hex.FpPoly p}
    (hab : a ∣ b) (hbc : b ∣ c) : a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  calc c
      = b * y := hy
    _ = (a * x) * y := by rw [hx]
    _ = a * (x * y) := Hex.DensePoly.mul_assoc_poly a x y

/-- `factorsModPBerlekampForm`-shaped discharge for per-modular-factor
irreducibility after the Mathlib-side transport.

Given the `factorsModPBerlekampForm` invariant (recording that
`primeData.factorsModP` is the post-`monicModularImage` Berlekamp factor
array of the monic modular image of the input) together with a successful
`isGoodPrime` check (which certifies the modular image is square-free),
the transported Mathlib polynomial of every stored modular factor is
irreducible.

Proof: each entry of `primeData.factorsModP` is `monicModularImage g` for
some raw Berlekamp factor `g`.  `irreducible_of_mem_berlekampFactor` gives
`Irreducible (toMathlibPolynomial g)`.  The transfer to
`monicModularImage g` routes through `toMathlibPolynomial_scale`: since
`monicModularImage g = scale (lc g)⁻¹ g`, the Mathlib image equals
`C ((lc g)⁻¹.toZMod) * toMathlibPolynomial g`, a unit multiple of the
original, and `Associated.irreducible` transfers the irreducibility.

The square-freeness premise of `irreducible_of_mem_berlekampFactor` is
discharged via `gcd_monicModularImage_derivative_eq_one_local` applied to
the modular square-freeness from `Hex.isGoodPrime_squareFreeModP`.

This is the per-index irreducibility component consumed by the
`ModPSubsetPartitionHypotheses` constructor.  The sibling existence /
uniqueness component is `existsUnique_modPFactorSubset_of_choosePrimeData`
(#4687); the constructor wrapper itself is `modPSubsetPartitionHypotheses_of_choosePrimeData`
(#4688). -/
theorem factors_irreducible_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true) :
    ∀ i : ModPFactorIndex primeData,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (modPFactor primeData i)) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hprime_root : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime_root⟩
  have hsf_common :
      ∀ d : Hex.FpPoly primeData.p,
        d ∣ Hex.ZPoly.modP primeData.p core →
        d ∣ Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core) →
        Hex.Berlekamp.isUnitPolynomial d = true :=
    squareFree_common_of_squareFreeModP core
      (Hex.isGoodPrime_squareFreeModP core primeData.p hgood)
  have hsf_common_monic :
      ∀ d : Hex.FpPoly primeData.p,
        d ∣ Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) →
        d ∣ Hex.DensePoly.derivative
            (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) →
        Hex.Berlekamp.isUnitPolynomial d = true := by
    intro d hd_monic hd_deriv_monic
    let u : Hex.ZMod64 primeData.p :=
      (Hex.DensePoly.leadingCoeff (Hex.ZPoly.modP primeData.p core))⁻¹
    have hmmi_eq :
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) =
          Hex.DensePoly.scale u (Hex.ZPoly.modP primeData.p core) := by
      simpa [u] using
        monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hzero
    have hlead_ne : Hex.DensePoly.leadingCoeff
        (Hex.ZPoly.modP primeData.p core) ≠ 0 :=
      fpPoly_leadingCoeff_ne_zero_of_size_pos (Hex.ZPoly.modP primeData.p core)
        ((Hex.DensePoly.isZero_eq_false_iff _).mp hzero)
    have hu_ne : u ≠ 0 := by
      simpa [u] using Hex.ZMod64.inv_ne_zero_of_prime hprime hlead_ne
    rw [hmmi_eq] at hd_monic
    rw [hmmi_eq, derivative_scale_local] at hd_deriv_monic
    have hscale_dvd_mod :
        Hex.DensePoly.scale u (Hex.ZPoly.modP primeData.p core) ∣
          Hex.ZPoly.modP primeData.p core :=
      Hex.FpPoly.dvd_scale_self_of_ne_zero hu_ne (Hex.ZPoly.modP primeData.p core)
    have hscale_dvd_deriv :
        Hex.DensePoly.scale u
            (Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core)) ∣
          Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core) :=
      Hex.FpPoly.dvd_scale_self_of_ne_zero hu_ne
        (Hex.DensePoly.derivative (Hex.ZPoly.modP primeData.p core))
    exact hsf_common d
      (dvd_trans_FpPoly_local hd_monic hscale_dvd_mod)
      (dvd_trans_FpPoly_local hd_deriv_monic hscale_dvd_deriv)
  have hmonicImage_monic :
      Hex.DensePoly.Monic
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  letI := hfield
  have hraw_irr :
      ∀ g ∈ (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
          hmonicImage_monic hfield).factors,
        Irreducible (HexBerlekampMathlib.toMathlibPolynomial g) :=
    HexBerlekampMathlib.irreducible_of_mem_berlekampFactor
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic hsf_common_monic
  have hraw_ne :
      ∀ g ∈ (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
          hmonicImage_monic hfield).factors,
        g ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic
  intro i
  have hi_mem : modPFactor primeData i ∈ primeData.factorsModP := by
    unfold modPFactor
    exact Array.getElem_mem i.isLt
  rw [heq] at hi_mem
  rw [List.mem_toArray, List.mem_map] at hi_mem
  obtain ⟨g', hg'_mem, hg'_eq⟩ := hi_mem
  have hirr_g' : Irreducible (HexBerlekampMathlib.toMathlibPolynomial g') :=
    hraw_irr g' hg'_mem
  have hg'_ne : g' ≠ 0 := hraw_ne g' hg'_mem
  have hg'_isZero : g'.isZero = false := Hex.isZero_false_of_ne_zero hg'_ne
  have hg'_size_pos : 0 < g'.size :=
    (Hex.DensePoly.isZero_eq_false_iff _).mp hg'_isZero
  have hg'_lead_ne :
      Hex.DensePoly.leadingCoeff g' ≠ (0 : Hex.ZMod64 primeData.p) :=
    fpPoly_leadingCoeff_ne_zero_of_size_pos g' hg'_size_pos
  have hg'_inv_ne :
      (Hex.DensePoly.leadingCoeff g')⁻¹ ≠ (0 : Hex.ZMod64 primeData.p) := by
    intro hinv
    have hone := Hex.ZMod64.inv_mul_eq_one_of_prime hprime hg'_lead_ne
    have hinv' :
        Hex.ZMod64.inv (Hex.DensePoly.leadingCoeff g') =
          (0 : Hex.ZMod64 primeData.p) := hinv
    rw [hinv'] at hone
    have hzeromul :
        (0 : Hex.ZMod64 primeData.p) * Hex.DensePoly.leadingCoeff g' =
          (0 : Hex.ZMod64 primeData.p) :=
      Lean.Grind.Semiring.zero_mul _
    rw [hzeromul] at hone
    have h_one_ne_zero : (1 : Hex.ZMod64 primeData.p) ≠ 0 :=
      fun h => Hex.ZMod64.one_ne_zero_of_prime hprime h
    exact h_one_ne_zero hone.symm
  have hinv_zmod_ne :
      HexModArithMathlib.ZMod64.toZMod
        (Hex.DensePoly.leadingCoeff g')⁻¹ ≠ (0 : ZMod primeData.p) := by
    intro h
    apply hg'_inv_ne
    have hinj := (HexModArithMathlib.ZMod64.equiv (p := primeData.p)).injective
    apply hinj
    simpa using h.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
  have hC_unit :
      IsUnit (Polynomial.C
        (HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff g')⁻¹)) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hinv_zmod_ne)
  have hmonic_eq :
      Hex.monicModularImage g' =
        Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff g')⁻¹ g' :=
    monicModularImage_eq_scale_inv_leadingCoeff_of_isZero_false hg'_isZero
  have hmath_eq :
      HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage g') =
        Polynomial.C
            (HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff g')⁻¹) *
          HexBerlekampMathlib.toMathlibPolynomial g' := by
    rw [hmonic_eq, toMathlibPolynomial_scale]
  have hassoc :
      Associated
        (HexBerlekampMathlib.toMathlibPolynomial g')
        (Polynomial.C
            (HexModArithMathlib.ZMod64.toZMod (Hex.DensePoly.leadingCoeff g')⁻¹) *
          HexBerlekampMathlib.toMathlibPolynomial g') :=
    ((associated_isUnit_mul_left_iff hC_unit).mpr (Associated.refl _)).symm
  rw [← hg'_eq, hmath_eq]
  exact hassoc.irreducible hirr_g'

/-- Per-modular-factor irreducibility specialised to the
`Hex.choosePrimeData? core = some primeData` branch.

In this branch, the `factorsModPBerlekampForm` invariant and the `isGoodPrime`
hypothesis are both supplied automatically by
`Hex.choosePrimeData?_factorsModP_berlekamp_form` and
`Hex.choosePrimeData?_isGoodPrime` respectively; the `none` branch is
excluded by the explicit-witness premise `hselected`.  The constructor
wrapper #4688 will compose this with the sibling
`existsUnique_modPFactorSubset_of_choosePrimeData` (#4687) and the
trivial `fModP_eq` / `admissible_prime` / `square_free_reduction` fields. -/
theorem factors_irreducible_of_choosePrimeData_of_some
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.choosePrimeData? core = some primeData) :
    ∀ i : ModPFactorIndex primeData,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (modPFactor primeData i)) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hform : Hex.factorsModPBerlekampForm core primeData := by
    obtain ⟨hzero, hfactors_eq⟩ :=
      Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hselected
    exact ⟨Hex.choosePrimeData?_prime core primeData hselected, hzero, hfactors_eq⟩
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hselected
  exact factors_irreducible_of_factorsModPBerlekampForm core primeData hform hgood

/-- Composed convenience wrapper: combines
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData` with
`henselLiftData_liftedFactor_injective` so that a Mathlib-side caller can
discharge `Function.Injective (liftedFactor (henselLiftData core B primeData))`
from the `choosePrimeData` boundary facts plus `factorsModP.toList.Nodup`,
without having to construct the internal `QuadraticMultifactorLiftInvariant`
themselves.

Consumed by
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
(via `LiftedFactorListMatches.nodup_of_injOn`) and the public wrapper
`exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence` (#4274).

The `factorsModP.toList.Nodup` hypothesis is the load-bearing ingredient;
discharge from the `choosePrimeData?` facts is provided by
`factorsModP_nodup_of_factorsModPBerlekampForm` above (combined with
`Hex.choosePrimeData?_factorsModP_berlekamp_form`).  The companion monicness
umbrella `henselLiftData_liftedFactor_monic_of_choosePrimeData` lives one
theorem above. -/
theorem henselLiftData_liftedFactor_injective_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hp_prime : Hex.Nat.Prime primeData.p)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList)
    (hnonempty : primeData.factorsModP.toList ≠ [])
    (hfactorsModP_nodup : primeData.factorsModP.toList.Nodup) :
    Function.Injective
      (liftedFactor (Hex.henselLiftData core B primeData)) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hinv :
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList :=
    Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      core B primeData hp_prime hp hB hcore_monic
      hfactors_monic hproduct_mod_p hcoprime hnonempty
  exact henselLiftData_liftedFactor_injective core B primeData
    hcore_monic hinv hp hB hfactors_monic hproduct_mod_p hfactorsModP_nodup

/--
Abstract-invariant umbrella for positive natural degree of each lifted factor
produced by `Hex.henselLiftData`.

Mirrors `henselLiftData_liftedFactor_monic` and `_injective`: takes the
recursive `QuadraticMultifactorLiftInvariant` package together with the
per-output mod-`p` product congruence and a per-factor natural-degree
positivity premise on the lift of each input `factorsModP` entry, and
concludes that every lifted factor's transported Mathlib polynomial has
positive natural degree.

The proof routes through `Hex.ZPoly.multifactorLiftQuadratic_each_congr_mod_base`
to identify each lifted factor's mod-`p` reduction with the corresponding
modular factor (after `FpPoly.liftToZ`), then transports through the
`toMathlibPolynomial`/`Polynomial.map` map.  Both the lifted factor and
its modular pre-image are monic, so reduction modulo `p` preserves natural
degree (their `Polynomial.map (Int.castRingHom (ZMod p))` images have the
same natural degree as the unmapped polynomials), and the modular images
agree by congruence.

This is the natDegree-positivity discharge consumed by the outer-bound
slow-path wrapper
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`
(see line 7590 below). -/
theorem henselLiftData_liftedFactor_natDegree_pos
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hfactors_natDegree_pos :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP,
        0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree) :
    ∀ i : Fin (Hex.henselLiftData core B primeData).liftedFactors.size,
      0 < (HexPolyZMathlib.toPolynomial
            (liftedFactor (Hex.henselLiftData core B primeData) i)).natDegree := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  haveI : Fact (1 < primeData.p) := ⟨hp⟩
  intro i
  change 0 < (HexPolyZMathlib.toPolynomial
    (Hex.henselLiftData core B primeData).liftedFactors[i]).natDegree
  -- 1. Each lifted factor is monic.
  have hlifted_monic :
      Hex.DensePoly.Monic
        (Hex.henselLiftData core B primeData).liftedFactors[i] :=
    henselLiftData_liftedFactor_monic core B primeData
      hcore_monic hprime_invariant hp hB i
  -- 2. Index gymnastics: identify the lifted factor with the multifactor output
  --    at the corresponding modular index.
  set arr :=
    Hex.ZPoly.multifactorLiftQuadratic primeData.p B core
      (primeData.factorsModP.map Hex.FpPoly.liftToZ) with harr_def
  have hd_factors :
      (Hex.henselLiftData core B primeData).liftedFactors = arr := by
    simp [Hex.henselLiftData, harr_def]
  have harr_size :
      arr.size = primeData.factorsModP.size := by
    rw [harr_def, Hex.ZPoly.multifactorLiftQuadratic_size_eq_input]
    simp
  have hd_size :
      (Hex.henselLiftData core B primeData).liftedFactors.size =
        primeData.factorsModP.size := by
    rw [hd_factors]; exact harr_size
  have hi_modP : i.val < primeData.factorsModP.size := by
    rw [← hd_size]; exact i.isLt
  have hi_arr : i.val < arr.size := by rw [harr_size]; exact hi_modP
  have hi_map :
      i.val < (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList.length := by
    rw [Array.length_toList, Array.size_map]; exact hi_modP
  have hi_arr_list : i.val < arr.toList.length := by
    rw [Array.length_toList]; exact hi_arr
  -- 3. Per-output mod-`p` congruence at index `i.val`.
  have hfactors_monic_arr :
      ∀ g ∈ (primeData.factorsModP.map Hex.FpPoly.liftToZ),
        Hex.DensePoly.Monic g := by
    intro g hg
    rw [Array.mem_map] at hg
    obtain ⟨f0, hf0_mem, hf0_eq⟩ := hg
    rw [← hf0_eq]
    exact Hex.FpPoly.monic_liftToZ_of_monic f0 hp (hfactors_monic f0 hf0_mem)
  have hcongr_i :=
    Hex.ZPoly.multifactorLiftQuadratic_each_congr_mod_base
      primeData.p B core (primeData.factorsModP.map Hex.FpPoly.liftToZ)
      hB hp hcore_monic hfactors_monic_arr hprime_invariant hproduct_mod_p i.val
  have hgetD_arr :
      arr.toList[i.val]?.getD 0 = arr[i.val]'hi_arr := by
    rw [List.getElem?_eq_getElem hi_arr_list, Option.getD_some, Array.getElem_toList]
  have hgetD_factors :
      (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList[i.val]?.getD 0 =
        Hex.FpPoly.liftToZ (primeData.factorsModP[i.val]'hi_modP) := by
    rw [List.getElem?_eq_getElem hi_map, Option.getD_some,
      Array.getElem_toList, Array.getElem_map]
  rw [hgetD_arr, hgetD_factors] at hcongr_i
  -- Identify `arr[i.val]` with the lifted factor at index `i`.
  -- Both `arr` and `(henselLiftData ...).liftedFactors` are definitionally
  -- the same `multifactorLiftQuadratic` invocation.
  have hlifted_eq :
      arr[i.val]'hi_arr =
        (Hex.henselLiftData core B primeData).liftedFactors[i] := by
    show arr[i.val]'hi_arr =
      (Hex.henselLiftData core B primeData).liftedFactors[i.val]'i.isLt
    rfl
  rw [hlifted_eq] at hcongr_i
  -- 4. Use the identification between executable mod-`p` reduction and Mathlib's
  --    `Polynomial.map (Int.castRingHom (ZMod p))` to identify natural degrees.
  set lifted := (Hex.henselLiftData core B primeData).liftedFactors[i] with hlifted_def
  set modular := primeData.factorsModP[i.val]'hi_modP with hmodular_def
  -- The mod-`p` reduction of the lifted factor equals the modular factor.
  have hmodP_eq :
      Hex.ZPoly.modP primeData.p lifted = modular := by
    have h₁ : Hex.ZPoly.modP primeData.p lifted =
        Hex.ZPoly.modP primeData.p (Hex.FpPoly.liftToZ modular) :=
      Hex.ZPoly.modP_eq_of_congr _ _ _ hcongr_i
    rw [h₁, Hex.FpPoly.modP_liftToZ]
  -- Common helper: `(1 : ZMod p) ≠ 0` since `p > 1`.
  have hone_ne_zero : (1 : ZMod primeData.p) ≠ 0 := one_ne_zero
  -- The lifted factor's transported polynomial has leading coefficient `1`.
  have hlifted_lead :
      (HexPolyZMathlib.toPolynomial lifted).leadingCoeff = (1 : Int) := by
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]; exact hlifted_monic
  have hlifted_lead_cast :
      (Int.castRingHom (ZMod primeData.p))
          (HexPolyZMathlib.toPolynomial lifted).leadingCoeff ≠ 0 := by
    rw [hlifted_lead]; simp [hone_ne_zero]
  -- The lift of the modular factor is monic, so its transported polynomial
  -- also has leading coefficient `1`.
  have hmodular_mem : modular ∈ primeData.factorsModP := by
    simp [hmodular_def, Array.getElem_mem]
  have hliftZ_monic : Hex.DensePoly.Monic (Hex.FpPoly.liftToZ modular) :=
    Hex.FpPoly.monic_liftToZ_of_monic modular hp (hfactors_monic modular hmodular_mem)
  have hliftZ_lead :
      (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ modular)).leadingCoeff =
        (1 : Int) := by
    rw [HexPolyMathlib.leadingCoeff_toPolynomial]; exact hliftZ_monic
  have hliftZ_lead_cast :
      (Int.castRingHom (ZMod primeData.p))
          (HexPolyZMathlib.toPolynomial
            (Hex.FpPoly.liftToZ modular)).leadingCoeff ≠ 0 := by
    rw [hliftZ_lead]; simp [hone_ne_zero]
  -- Identify natural degree of the transported lifted factor with the natural
  -- degree of its mod-`p` image's Mathlib transport.
  have hnatDeg_lifted :
      (HexPolyZMathlib.toPolynomial lifted).natDegree =
        (HexBerlekampMathlib.toMathlibPolynomial
          (Hex.ZPoly.modP primeData.p lifted)).natDegree := by
    rw [toMathlibPolynomial_modP_eq_map_intCast_zmod lifted]
    exact (HexPolyZMathlib.natDegree_map_intCast_zmod_eq_of_leadingCoeff_ne_zero
      primeData.p lifted hlifted_lead_cast).symm
  have hnatDeg_liftZ :
      (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ modular)).natDegree =
        (HexBerlekampMathlib.toMathlibPolynomial
          (Hex.ZPoly.modP primeData.p (Hex.FpPoly.liftToZ modular))).natDegree := by
    rw [toMathlibPolynomial_modP_eq_map_intCast_zmod (Hex.FpPoly.liftToZ modular)]
    exact (HexPolyZMathlib.natDegree_map_intCast_zmod_eq_of_leadingCoeff_ne_zero
      primeData.p (Hex.FpPoly.liftToZ modular) hliftZ_lead_cast).symm
  -- Tie them together: both equal natDegree of toMathlibPolynomial modular.
  have hnatDeg_eq :
      (HexPolyZMathlib.toPolynomial lifted).natDegree =
        (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ modular)).natDegree := by
    rw [hnatDeg_lifted, hnatDeg_liftZ, hmodP_eq, Hex.FpPoly.modP_liftToZ]
  -- Apply the premise on the modular side.
  have hpos_modular :
      0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ modular)).natDegree :=
    hfactors_natDegree_pos modular hmodular_mem
  -- Conclude.
  exact hnatDeg_eq ▸ hpos_modular

/--
Positive natural degree of every lifted local factor for the executable
`Hex.ZPoly.toMonicLiftData`.  This is the surface over
`henselLiftData_liftedFactor_natDegree_pos`.
-/
theorem Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hmonic_core :
      Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p)
        (Hex.ZPoly.toMonic core).monic
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        (Hex.ZPoly.toMonic core).monic primeData.p)
    (hfactors_natDegree_pos :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP,
        0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree) :
    ∀ i : Fin (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size,
      0 < (HexPolyZMathlib.toPolynomial
            (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).natDegree := by
  unfold Hex.ZPoly.toMonicLiftData
  exact henselLiftData_liftedFactor_natDegree_pos
    (Hex.ZPoly.toMonic core).monic
    (Hex.precisionForCoeffBound B primeData.p) primeData
    hmonic_core hprime_invariant hp hprecision hfactors_monic hproduct_mod_p
    hfactors_natDegree_pos

/-- Composed convenience wrapper: combines
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData` with
`henselLiftData_liftedFactor_natDegree_pos` so that a Mathlib-side caller
can discharge positive natural degree of every lifted factor from the
`choosePrimeData` boundary facts plus per-modular-factor natural-degree
positivity.

The per-modular-factor natural-degree positivity premise mirrors the
`hfactorsModP_nodup` premise on the injectivity umbrella (#4525): it is
exposed as an explicit hypothesis here because discharging it from
`choosePrimeData` invariants requires composing with `factorsModPBerlekampForm`
and the underlying Berlekamp factor-degree positivity, which lives in a
separate supporting lemma task. -/
theorem henselLiftData_liftedFactor_natDegree_pos_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hp_prime : Hex.Nat.Prime primeData.p)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList)
    (hnonempty : primeData.factorsModP.toList ≠ [])
    (hfactors_natDegree_pos :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP,
        0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree) :
    ∀ i : Fin (Hex.henselLiftData core B primeData).liftedFactors.size,
      0 < (HexPolyZMathlib.toPolynomial
            (liftedFactor (Hex.henselLiftData core B primeData) i)).natDegree := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hinv :
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList :=
    Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      core B primeData hp_prime hp hB hcore_monic
      hfactors_monic hproduct_mod_p hcoprime hnonempty
  exact henselLiftData_liftedFactor_natDegree_pos core B primeData
    hcore_monic hinv hp hB hfactors_monic hproduct_mod_p hfactors_natDegree_pos

/-- Fully composed natural-degree-positivity umbrella for every lifted factor of
`Hex.henselLiftData`, parametrised on the `factorsModPBerlekampForm` invariant
instead of an explicit per-modular-factor positivity premise.

This is the natural-degree analog of the composition pattern made available by
`factorsModP_nodup_of_factorsModPBerlekampForm` (line 4010) for the `_injective`
family: it drops `hfactors_natDegree_pos` from
`henselLiftData_liftedFactor_natDegree_pos_of_choosePrimeData` (line 4486) by
discharging that premise through
`factorsModP_natDegree_pos_of_factorsModPBerlekampForm` (line 4104), which in
turn folds in `Hex.Berlekamp.berlekampFactor_factors_pos_degree`.

The discharge requires three facts on `core` and `primeData`:

* `hform : Hex.factorsModPBerlekampForm core primeData` — recorded by
  `Hex.choosePrimeData?_factorsModP_berlekamp_form` (`HexBerlekampZassenhaus/
  Basic.lean`);
* `hgood : Hex.isGoodPrime core primeData.p = true` — recorded by
  `Hex.choosePrimeData?_isGoodPrime`;
* `hcore_pos : 0 < core.degree?.getD 0` — supplied by the caller (the slow-path
  arm of the HO-1 capstone uses `normalizeForFactor.squareFreeCore` as `core`,
  which has positive degree on every non-unit input).

The signature otherwise mirrors `_of_choosePrimeData` exactly, so downstream
callers that already construct `hfactors_natDegree_pos` by hand are
unaffected; they continue to use the explicit-premise umbrella. -/
theorem henselLiftData_liftedFactor_natDegree_pos_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hp_prime : Hex.Nat.Prime primeData.p)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList)
    (hnonempty : primeData.factorsModP.toList ≠ [])
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true)
    (hcore_pos : 0 < core.degree?.getD 0) :
    ∀ i : Fin (Hex.henselLiftData core B primeData).liftedFactors.size,
      0 < (HexPolyZMathlib.toPolynomial
            (liftedFactor (Hex.henselLiftData core B primeData) i)).natDegree := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hfactors_natDegree_pos :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP,
        0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree :=
    factorsModP_natDegree_pos_of_factorsModPBerlekampForm
      core primeData hform hgood hcore_pos
  exact henselLiftData_liftedFactor_natDegree_pos_of_choosePrimeData
    core B primeData hcore_monic hp_prime hp hB hfactors_monic
    hproduct_mod_p hcoprime hnonempty hfactors_natDegree_pos

/-- Fully composed injectivity umbrella for the lifted factors of
`Hex.henselLiftData`, parametrised on the `factorsModPBerlekampForm` invariant
instead of an explicit `factorsModP.toList.Nodup` premise.

This is the injective sibling of
`henselLiftData_liftedFactor_natDegree_pos_of_factorsModPBerlekampForm` (the
natural-degree analog just above) and the natural follow-up to the `Nodup`
chain landed in `factorsModP_nodup_of_factorsModPBerlekampForm` (line
4010): it drops `hfactorsModP_nodup` from
`henselLiftData_liftedFactor_injective_of_choosePrimeData` (line 4260) by
discharging that premise through
`factorsModP_nodup_of_factorsModPBerlekampForm`.  No `hcore_pos` premise is
needed (the `Nodup` discharge routes through `isGoodPrime`'s
modular-squarefreeness alone, unlike the natural-degree analog).

The discharge requires two facts on `core` and `primeData`:

* `hform : Hex.factorsModPBerlekampForm core primeData` — recorded by
  `Hex.choosePrimeData?_factorsModP_berlekamp_form` (`HexBerlekampZassenhaus/
  Basic.lean`);
* `hgood : Hex.isGoodPrime core primeData.p = true` — recorded by
  `Hex.choosePrimeData?_isGoodPrime`.

The signature otherwise mirrors `_of_choosePrimeData` exactly, so downstream
callers that already construct `hfactorsModP_nodup` by hand are unaffected;
they continue to use the explicit-premise umbrella. -/
theorem henselLiftData_liftedFactor_injective_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hp_prime : Hex.Nat.Prime primeData.p)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList)
    (hnonempty : primeData.factorsModP.toList ≠ [])
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true) :
    Function.Injective
      (liftedFactor (Hex.henselLiftData core B primeData)) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hfactorsModP_nodup : primeData.factorsModP.toList.Nodup :=
    factorsModP_nodup_of_factorsModPBerlekampForm core primeData hform hgood
  exact henselLiftData_liftedFactor_injective_of_choosePrimeData
    core B primeData hcore_monic hp_prime hp hB hfactors_monic
    hproduct_mod_p hcoprime hnonempty hfactorsModP_nodup

/--
Per-output monicness for the `toMonic` lift whose prime data is selected from
the monic transform itself.

This is the non-monic-core wrapper over
`Hex.ZPoly.toMonicLiftData_liftedFactor_monic`: the original `core` only needs
positive leading coefficient and positive degree, which together make
`(Hex.ZPoly.toMonic core).monic` monic.
-/
theorem Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p) :
    ∀ i : Fin (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size,
      Hex.DensePoly.Monic
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i) := by
  let monicCore := (Hex.ZPoly.toMonic core).monic
  have hmonicCore_monic :
      Hex.DensePoly.Monic monicCore := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree
      core hcore_lc_pos hcore_pos
  have hform : Hex.factorsModPBerlekampForm monicCore primeData := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonicPrimeData?_factorsModP_berlekamp_form
      core primeData hselected
  have hgood :
      letI := primeData.bounds
      Hex.isGoodPrime monicCore primeData.p = true := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonicPrimeData?_isGoodPrime core primeData hselected
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp : 1 < primeData.p := by
    have := hp_prime.two_le
    omega
  have hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    factorsModP_monic_of_factorsModPBerlekampForm monicCore primeData hform
  have hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        monicCore primeData.p :=
    factorsModP_polyProduct_congr_of_factorsModPBerlekampForm
      monicCore primeData hmonicCore_monic hform hgood
  have hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    factorsModP_coprime_of_factorsModPBerlekampForm monicCore primeData hform hgood
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    factorsModP_ne_nil_of_factorsModPBerlekampForm monicCore primeData hform
  have hinv :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p) monicCore
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList := by
    letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
    exact Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      monicCore (Hex.precisionForCoeffBound B primeData.p) primeData
      hp_prime hp hprecision hmonicCore_monic hfactors_monic
      hproduct_mod_p hcoprime hnonempty
  exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic
    core B primeData hmonicCore_monic hinv hp hprecision

/--
Positive natural degree for each output of the `toMonic` lift whose prime
data is selected from the monic transform itself.
-/
theorem Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p) :
    ∀ i : Fin (Hex.ZPoly.toMonicLiftData core B primeData).liftedFactors.size,
      0 < (HexPolyZMathlib.toPolynomial
            (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).natDegree := by
  let monicCore := (Hex.ZPoly.toMonic core).monic
  have hmonicCore_monic :
      Hex.DensePoly.Monic monicCore := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree
      core hcore_lc_pos hcore_pos
  have hmonicCore_degree :
      monicCore.degree?.getD 0 = core.degree?.getD 0 := by
    dsimp [monicCore]
    simpa [Hex.ZPoly.toMonic_degree] using
      Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree
        core hcore_lc_pos hcore_pos
  have hmonicCore_pos : 0 < monicCore.degree?.getD 0 := by
    rw [hmonicCore_degree]
    exact hcore_pos
  have hform : Hex.factorsModPBerlekampForm monicCore primeData := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonicPrimeData?_factorsModP_berlekamp_form
      core primeData hselected
  have hgood :
      letI := primeData.bounds
      Hex.isGoodPrime monicCore primeData.p = true := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonicPrimeData?_isGoodPrime core primeData hselected
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp : 1 < primeData.p := by
    have := hp_prime.two_le
    omega
  have hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    factorsModP_monic_of_factorsModPBerlekampForm monicCore primeData hform
  have hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        monicCore primeData.p :=
    factorsModP_polyProduct_congr_of_factorsModPBerlekampForm
      monicCore primeData hmonicCore_monic hform hgood
  have hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    factorsModP_coprime_of_factorsModPBerlekampForm monicCore primeData hform hgood
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    factorsModP_ne_nil_of_factorsModPBerlekampForm monicCore primeData hform
  have hinv :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p) monicCore
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList := by
    letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
    exact Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      monicCore (Hex.precisionForCoeffBound B primeData.p) primeData
      hp_prime hp hprecision hmonicCore_monic hfactors_monic
      hproduct_mod_p hcoprime hnonempty
  have hfactors_natDegree_pos :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP,
        0 < (HexPolyZMathlib.toPolynomial (Hex.FpPoly.liftToZ g)).natDegree :=
    factorsModP_natDegree_pos_of_factorsModPBerlekampForm
      monicCore primeData hform hgood hmonicCore_pos
  exact Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos
    core B primeData hmonicCore_monic hinv hp hprecision
    hfactors_monic hproduct_mod_p hfactors_natDegree_pos

/--
Injectivity of lifted factors for the `toMonic` lift whose prime data is
selected from the monic transform itself.
-/
theorem Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p) :
    Function.Injective
      (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData)) := by
  let monicCore := (Hex.ZPoly.toMonic core).monic
  have hmonicCore_monic :
      Hex.DensePoly.Monic monicCore := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree
      core hcore_lc_pos hcore_pos
  have hform : Hex.factorsModPBerlekampForm monicCore primeData := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonicPrimeData?_factorsModP_berlekamp_form
      core primeData hselected
  have hgood :
      letI := primeData.bounds
      Hex.isGoodPrime monicCore primeData.p = true := by
    dsimp [monicCore]
    exact Hex.ZPoly.toMonicPrimeData?_isGoodPrime core primeData hselected
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp : 1 < primeData.p := by
    have := hp_prime.two_le
    omega
  have hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g :=
    factorsModP_monic_of_factorsModPBerlekampForm monicCore primeData hform
  have hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        monicCore primeData.p :=
    factorsModP_polyProduct_congr_of_factorsModPBerlekampForm
      monicCore primeData hmonicCore_monic hform hgood
  have hcoprime :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorCoprimeSplits primeData.p
        primeData.factorsModP.toList :=
    factorsModP_coprime_of_factorsModPBerlekampForm monicCore primeData hform hgood
  have hnonempty : primeData.factorsModP.toList ≠ [] :=
    factorsModP_ne_nil_of_factorsModPBerlekampForm monicCore primeData hform
  have hinv :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p (Hex.precisionForCoeffBound B primeData.p) monicCore
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList := by
    letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
    exact Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData
      monicCore (Hex.precisionForCoeffBound B primeData.p) primeData
      hp_prime hp hprecision hmonicCore_monic hfactors_monic
      hproduct_mod_p hcoprime hnonempty
  have hfactorsModP_nodup : primeData.factorsModP.toList.Nodup :=
    factorsModP_nodup_of_factorsModPBerlekampForm monicCore primeData hform hgood
  exact Hex.ZPoly.toMonicLiftData_liftedFactor_injective
    core B primeData hmonicCore_monic hinv hp hprecision
    hfactors_monic hproduct_mod_p hfactorsModP_nodup

/-- Monic integer polynomials are nonzero. -/
theorem zpoly_ne_zero_of_monic {f : Hex.ZPoly}
    (h : Hex.DensePoly.Monic f) : f ≠ 0 := by
  intro hf
  have hpos := zpoly_size_pos_of_monic h
  rw [hf] at hpos
  exact absurd hpos (by simp)

/-- Monic integer polynomials have positive leading coefficient. -/
theorem zpoly_lc_pos_of_monic {f : Hex.ZPoly}
    (h : Hex.DensePoly.Monic f) :
    0 < Hex.DensePoly.leadingCoeff f := by
  rw [show Hex.DensePoly.leadingCoeff f = (1 : Int) from h]
  decide

private theorem zpoly_monic_one : Hex.DensePoly.Monic (1 : Hex.ZPoly) := by
  show Hex.DensePoly.leadingCoeff (1 : Hex.ZPoly) = (1 : Int)
  change Hex.DensePoly.leadingCoeff (Hex.DensePoly.C (1 : Int)) = (1 : Int)
  simp [Hex.DensePoly.leadingCoeff,
    Hex.DensePoly.coeffs_C_of_ne_zero (by decide : (1 : Int) ≠ 0)]

private theorem zpoly_monic_mul {a b : Hex.ZPoly}
    (ha : Hex.DensePoly.Monic a) (hb : Hex.DensePoly.Monic b) :
    Hex.DensePoly.Monic (a * b) := by
  have ha_ne := zpoly_ne_zero_of_monic ha
  have hb_ne := zpoly_ne_zero_of_monic hb
  show Hex.DensePoly.leadingCoeff (a * b) = (1 : Int)
  rw [Hex.ZPoly.leadingCoeff_mul_of_nonzero a b ha_ne hb_ne,
    show Hex.DensePoly.leadingCoeff a = 1 from ha,
    show Hex.DensePoly.leadingCoeff b = 1 from hb]
  decide

/--
Identify `liftedFactorProduct d S` to a `Finset.prod` over `S` after transport to
`Polynomial ℤ`. The executable foldl form unfolds through `toPolynomial_foldl_mul`
and the resulting `List.prod` is then identified with the Mathlib `Finset.prod`
via `Finset.prod_map_toList`.

This is the algebra-to-`Finset.prod` lemma needed by the disjoint-union splitting
lemma `liftedFactorProduct_eq_mul_sdiff_of_subset`.
-/
theorem toPolynomial_liftedFactorProduct
    (d : Hex.LiftData) (S : LiftedFactorSubset d) :
    HexPolyZMathlib.toPolynomial (liftedFactorProduct d S) =
      ∏ i ∈ S, HexPolyZMathlib.toPolynomial (liftedFactor d i) := by
  unfold liftedFactorProduct
  rw [show
      (S.toList.foldl (fun acc i => acc * liftedFactor d i) (1 : Hex.ZPoly)) =
        (S.toList.map (liftedFactor d)).foldl (· * ·) 1 from by
    rw [List.foldl_map]]
  rw [toPolynomial_foldl_mul, toPolynomial_one_zpoly, ← List.prod_eq_foldl,
    List.map_map]
  exact Finset.prod_map_toList S (fun i => HexPolyZMathlib.toPolynomial (liftedFactor d i))

/--
Product-level base-modulus preservation for the lifted factors selected by a
modular-factor subset.

After transporting `S` through `liftedSubsetOfModPSubset`, the product of the
corresponding Hensel-lifted factors is congruent modulo `primeData.p` to the
canonical integer lift of the original modular subset product.
-/
theorem henselLiftData_liftedSubset_product_congr_mod_base
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p) :
    ∀ S : ModPFactorSubset primeData,
      letI := primeData.bounds
      Hex.ZPoly.congr
        (liftedFactorProduct (Hex.henselLiftData core B primeData)
          (liftedSubsetOfModPSubset primeData
            (Hex.henselLiftData core B primeData)
            (henselLiftData_liftedFactors_size_eq core B primeData) S))
        (Hex.FpPoly.liftToZ (modPFactorProduct primeData S))
        primeData.p := by
  letI := primeData.bounds
  intro S
  let d := Hex.henselLiftData core B primeData
  let hsize := henselLiftData_liftedFactors_size_eq core B primeData
  let emb := modPIndexToLiftedEmbedding primeData d hsize
  have hmodP :
      Hex.ZPoly.modP primeData.p
          (liftedFactorProduct d (liftedSubsetOfModPSubset primeData d hsize S)) =
        modPFactorProduct primeData S := by
    apply HexBerlekampMathlib.fpPolyEquiv.injective
    change
      HexBerlekampMathlib.toMathlibPolynomial
          (Hex.ZPoly.modP primeData.p
            (liftedFactorProduct d (liftedSubsetOfModPSubset primeData d hsize S))) =
        HexBerlekampMathlib.toMathlibPolynomial (modPFactorProduct primeData S)
    rw [toMathlibPolynomial_modP_eq_map_intCast_zmod,
      toPolynomial_liftedFactorProduct, toMathlibPolynomial_modPFactorProduct]
    rw [Polynomial.map_prod]
    change
      (∏ i ∈ S.map emb,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).map
          (Int.castRingHom (ZMod primeData.p))) =
        ∏ i ∈ S, HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)
    rw [Finset.prod_map S emb]
    refine Finset.prod_congr rfl ?_
    intro i _hi
    have hfactor_modP :=
      henselLiftData_liftedFactor_modP_eq_modPFactor core B primeData
        hcore_monic hprime_invariant hp hB hfactors_monic hproduct_mod_p i
    have hfactor_modP' :
        Hex.ZPoly.modP primeData.p (liftedFactor d (emb i)) =
          modPFactor primeData i := by
      simpa [d, emb, hsize] using hfactor_modP
    change
      (HexPolyZMathlib.toPolynomial (liftedFactor d (emb i))).map
          (Int.castRingHom (ZMod primeData.p)) =
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)
    rw [← toMathlibPolynomial_modP_eq_map_intCast_zmod
      (liftedFactor d (emb i)), hfactor_modP']
  exact Hex.ZPoly.congr_symm _ _ _
    (Hex.ZPoly.congr_liftToZ_of_modP_eq primeData.p (modPFactorProduct primeData S)
      (liftedFactorProduct d (liftedSubsetOfModPSubset primeData d hsize S)) hmodP)

/-! ### Subset/complement coprimality of Hensel-lifted factors mod `p`

The next group of theorems supplies the `IsCoprime` input over
`(ZMod primeData.p)[X]` required by `HexHenselMathlib.hensel_unique` when
applied to the subset/complement pair of Hensel-lifted factor products.

The subset-product and complement-product reductions modulo `p` are
connected through `henselLiftData_liftedSubset_product_congr_mod_base` and
the canonical `liftToZ` identification, landing in
`HexBerlekampMathlib.toMathlibPolynomial` over the `modPFactorProduct`
view. Pairwise non-association of the monic `modPFactor` entries
(`factorsModP_nodup_of_factorsModPBerlekampForm`) then supplies the
standard UFD-style coprimality over `Polynomial (ZMod primeData.p)`. -/

/-- The `modPIndexToLiftedEmbedding` is surjective once the lift stage
preserves factor count: it is the value-preserving `Fin` cast, which is a
bijection between sets of equal cardinality. -/
private theorem modPIndexToLiftedEmbedding_surjective
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size) :
    Function.Surjective (modPIndexToLiftedEmbedding primeData d hsize) := by
  intro j
  refine ⟨⟨j.val, hsize ▸ j.isLt⟩, ?_⟩
  exact Fin.ext rfl

/-- `Finset.univ.map (modPIndexToLiftedEmbedding ...)` is the lifted-side
universe. -/
private theorem map_univ_modPIndexToLiftedEmbedding
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size) :
    (Finset.univ : ModPFactorSubset primeData).map
        (modPIndexToLiftedEmbedding primeData d hsize) =
      (Finset.univ : LiftedFactorSubset d) :=
  Finset.map_univ_of_surjective
    (modPIndexToLiftedEmbedding_surjective primeData d hsize)

/-- The lifted-side complement of a `liftedSubsetOfModPSubset` is itself
a `liftedSubsetOfModPSubset`, of the mod-`p`-side complement. Lets
subset/complement reasoning on the lifted side reduce to subset/complement
reasoning on the mod-`p` side. -/
private theorem liftedSubsetOfModPSubset_compl_eq
    (primeData : Hex.PrimeChoiceData) (d : Hex.LiftData)
    (hsize : d.liftedFactors.size = primeData.factorsModP.size)
    (S : ModPFactorSubset primeData) :
    liftedSubsetOfModPSubset primeData d hsize (Finset.univ \ S) =
      (Finset.univ : LiftedFactorSubset d) \
        liftedSubsetOfModPSubset primeData d hsize S := by
  unfold liftedSubsetOfModPSubset
  rw [Finset.map_sdiff,
    map_univ_modPIndexToLiftedEmbedding primeData d hsize]

/--
Mathlib transport of a Hensel-lifted-subset product, mapped down to
`Polynomial (ZMod primeData.p)`, equals the Mathlib transport of the
corresponding `modPFactor` subset product.

Combines `henselLiftData_liftedSubset_product_congr_mod_base` (the
`ZPoly.congr` form, lifted to map equality via
`HexHenselMathlib.zpoly_congr_toPolynomial_map_eq`) with
`Hex.FpPoly.modP_liftToZ` and
`toMathlibPolynomial_modP_eq_map_intCast_zmod`. -/
private theorem toPolynomial_liftedSubset_map_intCast_zmod_eq_toMathlibPolynomial
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (S : ModPFactorSubset primeData) :
    letI := primeData.bounds
    let d := Hex.henselLiftData core B primeData
    let hsize := henselLiftData_liftedFactors_size_eq core B primeData
    (HexPolyZMathlib.toPolynomial
        (liftedFactorProduct d (liftedSubsetOfModPSubset primeData d hsize S))).map
          (Int.castRingHom (ZMod primeData.p)) =
      HexBerlekampMathlib.toMathlibPolynomial (modPFactorProduct primeData S) := by
  letI := primeData.bounds
  intro d hsize
  have hcongr :=
    henselLiftData_liftedSubset_product_congr_mod_base core B primeData
      hcore_monic hprime_invariant hp hB hfactors_monic hproduct_mod_p S
  have hmap_eq :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq
      (liftedFactorProduct d (liftedSubsetOfModPSubset primeData d hsize S))
      (Hex.FpPoly.liftToZ (modPFactorProduct primeData S))
      primeData.p hcongr
  rw [hmap_eq]
  rw [← toMathlibPolynomial_modP_eq_map_intCast_zmod
    (Hex.FpPoly.liftToZ (modPFactorProduct primeData S)),
    Hex.FpPoly.modP_liftToZ]

/-- Two `modPFactor` entries with distinct indices are unequal: a direct index
form of the `Nodup` invariant carried by `factorsModPBerlekampForm`. -/
private theorem modPFactor_ne_of_ne
    {primeData : Hex.PrimeChoiceData}
    (hfactors_nodup : primeData.factorsModP.toList.Nodup)
    {i j : ModPFactorIndex primeData} (hij : i ≠ j) :
    letI := primeData.bounds
    modPFactor primeData i ≠ modPFactor primeData j := by
  letI := primeData.bounds
  intro h
  apply hij
  have hi_list : i.val < primeData.factorsModP.toList.length := by
    rw [Array.length_toList]; exact i.isLt
  have hj_list : j.val < primeData.factorsModP.toList.length := by
    rw [Array.length_toList]; exact j.isLt
  have hlist_i :
      primeData.factorsModP.toList[i.val]'hi_list =
        primeData.factorsModP[i.val]'i.isLt := by
    rw [Array.getElem_toList]
  have hlist_j :
      primeData.factorsModP.toList[j.val]'hj_list =
        primeData.factorsModP[j.val]'j.isLt := by
    rw [Array.getElem_toList]
  have hlist_eq :
      primeData.factorsModP.toList[i.val]'hi_list =
        primeData.factorsModP.toList[j.val]'hj_list := by
    rw [hlist_i, hlist_j]; exact h
  exact Fin.ext ((List.Nodup.getElem_inj_iff hfactors_nodup).mp hlist_eq)

/-- Two Mathlib-transported monic irreducible mod-`p` factors with distinct
indices are coprime in `Polynomial (ZMod primeData.p)`.

The proof uses pairwise non-association (distinct monic polynomials are
non-associated) plus `Irreducible.associated_of_dvd` to derive non-divisibility,
then closes via `Irreducible.coprime_iff_not_dvd` in the PID
`Polynomial (ZMod primeData.p)` (which has `IsBezout` once
`Fact (Nat.Prime primeData.p)` makes `ZMod primeData.p` a field). -/
private theorem isCoprime_toMathlibPolynomial_modPFactor_of_ne
    {primeData : Hex.PrimeChoiceData}
    (hprime : _root_.Nat.Prime primeData.p)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hfactors_irr :
      letI := primeData.bounds
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)))
    (hfactors_nodup : primeData.factorsModP.toList.Nodup)
    {i j : ModPFactorIndex primeData} (hij : i ≠ j) :
    letI := primeData.bounds
    IsCoprime
      (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i))
      (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData j)) := by
  letI := primeData.bounds
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  have hi_monic_fp : Hex.DensePoly.Monic (modPFactor primeData i) :=
    hfactors_monic _ (Array.getElem_mem _)
  have hj_monic_fp : Hex.DensePoly.Monic (modPFactor primeData j) :=
    hfactors_monic _ (Array.getElem_mem _)
  have hi_monic :
      (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)).Monic :=
    HexBerlekampMathlib.toMathlibPolynomial_monic _ hi_monic_fp
  have hj_monic :
      (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData j)).Monic :=
    HexBerlekampMathlib.toMathlibPolynomial_monic _ hj_monic_fp
  have hne_fp : modPFactor primeData i ≠ modPFactor primeData j :=
    modPFactor_ne_of_ne hfactors_nodup hij
  have hne_math :
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) ≠
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData j) := by
    intro h
    exact hne_fp (HexBerlekampMathlib.fpPolyEquiv.injective h)
  have hnassoc : ¬ Associated
      (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i))
      (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData j)) := by
    intro hassoc
    exact hne_math (Polynomial.eq_of_monic_of_associated hi_monic hj_monic hassoc)
  rw [(hfactors_irr i).coprime_iff_not_dvd]
  intro hdvd
  exact hnassoc ((hfactors_irr i).associated_of_dvd (hfactors_irr j) hdvd)

/--
Subset/complement coprimality of Hensel-lifted factor products modulo
`primeData.p`.

After mapping both products into `Polynomial (ZMod primeData.p)`, the
selected lifted-factor subset's product and the complementary subset's
product are coprime: each lifted product reduces (via
`henselLiftData_liftedSubset_product_congr_mod_base` and
`Hex.FpPoly.modP_liftToZ`) to the corresponding `modPFactor` subset
product, and the `modPFactor` entries are pairwise distinct monic
irreducibles in `Polynomial (ZMod primeData.p)`, so any subset and its
complement are coprime.

This is the `IsCoprime` input over `(ZMod primeData.p)[X]` consumed by
`HexHenselMathlib.hensel_unique` when applied to the subset/complement
pair of Hensel-lifted factor products (#4761 precursor for #4733).
-/
theorem henselLiftData_liftedSubset_complement_isCoprime_mod_p
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime : _root_.Nat.Prime primeData.p)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hfactors_irr :
      letI := primeData.bounds
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)))
    (hfactors_nodup : primeData.factorsModP.toList.Nodup)
    (S : ModPFactorSubset primeData) :
    letI := primeData.bounds
    let d := Hex.henselLiftData core B primeData
    let hsize := henselLiftData_liftedFactors_size_eq core B primeData
    IsCoprime
      ((HexPolyZMathlib.toPolynomial
          (liftedFactorProduct d (liftedSubsetOfModPSubset primeData d hsize S))).map
        (Int.castRingHom (ZMod primeData.p)))
      ((HexPolyZMathlib.toPolynomial
          (liftedFactorProduct d ((Finset.univ : LiftedFactorSubset d) \
            liftedSubsetOfModPSubset primeData d hsize S))).map
        (Int.castRingHom (ZMod primeData.p))) := by
  letI := primeData.bounds
  intro d hsize
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  -- Rewrite both lifted products via the modP identification with `toMathlibPolynomial`
  -- of `modPFactorProduct`. The complement requires the
  -- `liftedSubsetOfModPSubset_compl_eq` rewrite first.
  rw [← liftedSubsetOfModPSubset_compl_eq primeData d hsize S]
  rw [toPolynomial_liftedSubset_map_intCast_zmod_eq_toMathlibPolynomial
      core B primeData hcore_monic hprime_invariant hp hB
      hfactors_monic hproduct_mod_p S,
    toPolynomial_liftedSubset_map_intCast_zmod_eq_toMathlibPolynomial
      core B primeData hcore_monic hprime_invariant hp hB
      hfactors_monic hproduct_mod_p (Finset.univ \ S)]
  -- Expand both `modPFactorProduct`s into `Finset.prod` of
  -- `toMathlibPolynomial (modPFactor _)` via the identification lemma.
  rw [toMathlibPolynomial_modPFactorProduct,
    toMathlibPolynomial_modPFactorProduct]
  -- Apply `IsCoprime.prod_left_iff` and `IsCoprime.prod_right_iff` to
  -- reduce to per-pair coprimality between distinct modPFactors.
  rw [IsCoprime.prod_left_iff]
  intro i hi
  rw [IsCoprime.prod_right_iff]
  intro j hj
  apply isCoprime_toMathlibPolynomial_modPFactor_of_ne
    hprime hfactors_monic hfactors_irr hfactors_nodup
  intro hij
  rw [hij] at hi
  rcases Finset.mem_sdiff.mp hj with ⟨_, hj_not⟩
  exact hj_not hi

/--
Multiplicative splitting for `liftedFactorProduct` along the disjoint
decomposition `T = S ⊔ (T \ S)` when `S ⊆ T`.

This is the executable analogue of `Finset.prod_sdiff` for the foldl product
over `LiftedFactorSubset d`. Proved by transporting to `Polynomial ℤ` via
`toPolynomial_liftedFactorProduct` and applying `Finset.prod_sdiff` there,
then inverting through `HexPolyZMathlib.equiv.injective`.
-/
theorem liftedFactorProduct_eq_mul_sdiff_of_subset
    {d : Hex.LiftData} {S T : LiftedFactorSubset d} (hST : S ⊆ T) :
    liftedFactorProduct d T =
      liftedFactorProduct d S * liftedFactorProduct d (T \ S) := by
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [HexPolyZMathlib.toPolynomial_mul,
    toPolynomial_liftedFactorProduct, toPolynomial_liftedFactorProduct,
    toPolynomial_liftedFactorProduct]
  rw [← Finset.prod_sdiff hST, mul_comm]

/--
Multiplicative splitting for `liftedFactorProduct` along a disjoint union.

Specialisation of `liftedFactorProduct_eq_mul_sdiff_of_subset` to the case where
`T = S ∪ U` with `S` and `U` disjoint, so `T \ S = U` and the product factors
as `liftedFactorProduct d (S ∪ U) = liftedFactorProduct d S *
liftedFactorProduct d U`.
-/
theorem liftedFactorProduct_union_of_disjoint
    {d : Hex.LiftData} {S U : LiftedFactorSubset d}
    (hdisj : Disjoint S U) :
    liftedFactorProduct d (S ∪ U) =
      liftedFactorProduct d S * liftedFactorProduct d U := by
  have hSsub : S ⊆ S ∪ U := Finset.subset_union_left
  have hsdiff : (S ∪ U) \ S = U := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    refine ⟨?_, ?_⟩
    · rintro ⟨hmem, hnotS⟩
      rcases hmem with hS | hU
      · exact absurd hS hnotS
      · exact hU
    · intro hU
      refine ⟨Or.inr hU, ?_⟩
      intro hS
      exact (Finset.disjoint_left.mp hdisj hS hU).elim
  rw [liftedFactorProduct_eq_mul_sdiff_of_subset hSsub, hsdiff]

/--
The full lifted-factor product over `Finset.univ` collapses to the executable
`Array.polyProduct` of the raw lifted-factor array.

The proof routes through `HexPolyZMathlib.equiv.injective`: under the
`toPolynomial` map, both sides expand to the same finite product over
`Fin d.liftedFactors.size`, using `toPolynomial_liftedFactorProduct`,
`polyProduct_toPolynomial`, and `Finset.prod_univ_fun_getElem` modulo the
`Array.length_toList` size identification.

This is the structural identification needed to feed the multifactor-lift product
spec into subset-based recombination reasoning.
-/
theorem liftedFactorProduct_univ_eq_polyProduct_liftedFactors
    (d : Hex.LiftData) :
    liftedFactorProduct d (Finset.univ : Finset (LiftedFactorIndex d)) =
      Array.polyProduct d.liftedFactors := by
  apply HexPolyZMathlib.equiv.injective
  show HexPolyZMathlib.toPolynomial _ = HexPolyZMathlib.toPolynomial _
  rw [toPolynomial_liftedFactorProduct, polyProduct_toPolynomial,
    ← Fin.prod_univ_fun_getElem d.liftedFactors.toList HexPolyZMathlib.toPolynomial]
  have hlen : d.liftedFactors.toList.length = d.liftedFactors.size :=
    Array.length_toList
  refine Fintype.prod_equiv (finCongr hlen.symm) _ _ ?_
  intro i
  show HexPolyZMathlib.toPolynomial d.liftedFactors[i.val] =
    HexPolyZMathlib.toPolynomial d.liftedFactors.toList[i.val]
  rw [Array.getElem_toList]

/--
Under the recursive quadratic multifactor lift invariant, the product of all
Hensel-lifted local factors is congruent to `core` modulo `primeData.p ^ B`.

This is the umbrella wrapper combining
`liftedFactorProduct_univ_eq_polyProduct_liftedFactors` with
`Hex.ZPoly.multifactorLiftQuadratic_spec` so downstream subset-recombination
proofs can split the full product through
`liftedFactorProduct_eq_mul_sdiff_of_subset`.
-/
theorem henselLiftData_liftedFactorProduct_univ_congr_core
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B) :
    letI := primeData.bounds
    Hex.ZPoly.congr
      (liftedFactorProduct (Hex.henselLiftData core B primeData)
        (Finset.univ : Finset
          (LiftedFactorIndex (Hex.henselLiftData core B primeData))))
      core (primeData.p ^ B) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  rw [liftedFactorProduct_univ_eq_polyProduct_liftedFactors]
  change Hex.ZPoly.congr
    (Array.polyProduct
      (Hex.ZPoly.multifactorLiftQuadratic primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ)))
    core (primeData.p ^ B)
  exact Hex.ZPoly.multifactorLiftQuadratic_spec primeData.p B core
    (primeData.factorsModP.map Hex.FpPoly.liftToZ) hB hp hprime_invariant

/--
The lifted-factor product over a subset times the lifted-factor product over
its complement (within `Finset.univ`) is congruent to `core` modulo
`primeData.p ^ B`, under the recursive quadratic multifactor lift invariant.

This packages the mod-`p^k` factorization input required by Hensel
uniqueness callers (`HexHenselMathlib.hensel_unique`): the subset product
plays the role of `g` and the complement product plays the role of `h` in
`g * h ≡ core (mod p^k)`. The proof combines the full-product congruence
(`henselLiftData_liftedFactorProduct_univ_congr_core`) with the multiplicative
splitting `liftedFactorProduct_eq_mul_sdiff_of_subset`.
-/
theorem henselLiftData_liftedFactorProduct_subset_complement_congr_core
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (S : LiftedFactorSubset (Hex.henselLiftData core B primeData)) :
    letI := primeData.bounds
    Hex.ZPoly.congr
      (liftedFactorProduct (Hex.henselLiftData core B primeData) S *
        liftedFactorProduct (Hex.henselLiftData core B primeData)
          (Finset.univ \ S))
      core (primeData.p ^ B) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hfull :=
    henselLiftData_liftedFactorProduct_univ_congr_core core B primeData
      hprime_invariant hp hB
  have hsplit :
      liftedFactorProduct (Hex.henselLiftData core B primeData)
          (Finset.univ : Finset
            (LiftedFactorIndex (Hex.henselLiftData core B primeData))) =
        liftedFactorProduct (Hex.henselLiftData core B primeData) S *
          liftedFactorProduct (Hex.henselLiftData core B primeData)
            (Finset.univ \ S) :=
    liftedFactorProduct_eq_mul_sdiff_of_subset (Finset.subset_univ S)
  rw [← hsplit]
  exact hfull

/--
`Hex.ZPoly.congr` follows from coefficientwise equality of the canonical
reductions modulo `p ^ k`. The forward direction is
`Hex.ZPoly.reduceModPow_eq_of_congr`; this is the reverse direction, derived
by transitivity through `Hex.ZPoly.congr_reduceModPow` on both sides.
-/
private theorem congr_of_reduceModPow_eq
    (f g : Hex.ZPoly) (p k : Nat) (hpk : 0 < p ^ k)
    (h : Hex.ZPoly.reduceModPow f p k = Hex.ZPoly.reduceModPow g p k) :
    Hex.ZPoly.congr f g (p ^ k) := by
  have hf : Hex.ZPoly.congr (Hex.ZPoly.reduceModPow f p k) f (p ^ k) :=
    Hex.ZPoly.congr_reduceModPow f p k hpk
  have hg : Hex.ZPoly.congr (Hex.ZPoly.reduceModPow g p k) g (p ^ k) :=
    Hex.ZPoly.congr_reduceModPow g p k hpk
  rw [h] at hf
  exact Hex.ZPoly.congr_trans _ _ _ _
    (Hex.ZPoly.congr_symm _ _ _ hf) hg

/--
Multiplicative closure of `RepresentsIntegerFactorAtLift` along a disjoint
decomposition `S ∪ T` of representing subsets under a monic core. If `S`
represents the integer factor `f` and `T` (disjoint from `S`) represents `g`,
then `S ∪ T` represents `f * g`.

Combines `liftedFactorProduct_union_of_disjoint` with the multiplicative
congruence `Hex.ZPoly.congr_mul`.
-/
theorem representsIntegerFactorAtLift_mul_of_monic_core
    {core f g : Hex.ZPoly} {d : Hex.LiftData}
    {S T : LiftedFactorSubset d}
    (hcore_monic : Hex.DensePoly.Monic core)
    (hdisj : Disjoint S T)
    (hf_rep : RepresentsIntegerFactorAtLift core d f S)
    (hg_rep : RepresentsIntegerFactorAtLift core d g T) :
    RepresentsIntegerFactorAtLift core d (f * g) (S ∪ T) := by
  unfold RepresentsIntegerFactorAtLift at hf_rep hg_rep ⊢
  have hlead : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  have hpk_pos : 0 < d.p ^ d.k := Nat.pow_pos d.p_pos
  have hscaled :
      ∀ (U : LiftedFactorSubset d),
        scaledLiftedFactorProduct core d U = liftedFactorProduct d U := by
    intro U
    unfold scaledLiftedFactorProduct
    rw [hlead]
    exact densePoly_scale_one_int (liftedFactorProduct d U)
  rw [hscaled S] at hf_rep
  rw [hscaled T] at hg_rep
  rw [hscaled (S ∪ T), liftedFactorProduct_union_of_disjoint hdisj]
  have hcongr_f : Hex.ZPoly.congr (liftedFactorProduct d S) f (d.p ^ d.k) :=
    congr_of_reduceModPow_eq _ _ _ _ hpk_pos hf_rep
  have hcongr_g : Hex.ZPoly.congr (liftedFactorProduct d T) g (d.p ^ d.k) :=
    congr_of_reduceModPow_eq _ _ _ _ hpk_pos hg_rep
  have hcongr_mul :
      Hex.ZPoly.congr (liftedFactorProduct d S * liftedFactorProduct d T)
        (f * g) (d.p ^ d.k) :=
    Hex.ZPoly.congr_mul _ _ _ _ _ hcongr_f hcongr_g
  exact Hex.ZPoly.reduceModPow_eq_of_congr _ _ _ _ hcongr_mul

/--
Monic-product closure for `liftedFactorProduct`: when every selected lifted
factor is monic, the executable foldl product over the subset is monic too.
The induction unfolds `Finset.toList` and chains `zpoly_monic_mul` through each
`*` step starting from `Monic (1 : ZPoly)`.
-/
theorem liftedFactorProduct_monic
    (d : Hex.LiftData) (S : LiftedFactorSubset d)
    (hmonic : ∀ i ∈ S, Hex.DensePoly.Monic (liftedFactor d i)) :
    Hex.DensePoly.Monic (liftedFactorProduct d S) := by
  unfold liftedFactorProduct
  suffices h : ∀ (l : List (LiftedFactorIndex d)) (acc : Hex.ZPoly),
      Hex.DensePoly.Monic acc →
      (∀ i ∈ l, Hex.DensePoly.Monic (liftedFactor d i)) →
      Hex.DensePoly.Monic
        (l.foldl (fun acc i => acc * liftedFactor d i) acc) by
    refine h S.toList 1 zpoly_monic_one ?_
    intro i hi
    exact hmonic i ((Finset.mem_toList).mp hi)
  intro l
  induction l with
  | nil =>
    intro acc hacc _
    simpa using hacc
  | cons x rest ih =>
    intro acc hacc hl
    simp only [List.foldl_cons]
    apply ih
    · exact zpoly_monic_mul hacc (hl x List.mem_cons_self)
    · intro i hi; exact hl i (List.mem_cons_of_mem _ hi)

/--
Monicity of the Hensel-lifted subset product under the quadratic multifactor
lift invariant.

Each Hensel-lifted local factor is monic
(`henselLiftData_liftedFactor_monic`), and the foldl product of monic factors
is monic (`liftedFactorProduct_monic`), so any selected subset product is
monic. This is the monicity input required by
`HexHenselMathlib.hensel_unique` for the selected factor.
-/
theorem henselLiftData_liftedFactorProduct_monic
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hp : 1 < primeData.p)
    (hB : 1 ≤ B)
    (S : LiftedFactorSubset (Hex.henselLiftData core B primeData)) :
    Hex.DensePoly.Monic
      (liftedFactorProduct (Hex.henselLiftData core B primeData) S) :=
  liftedFactorProduct_monic (Hex.henselLiftData core B primeData) S
    (fun i _ =>
      henselLiftData_liftedFactor_monic core B primeData hcore_monic
        hprime_invariant hp hB i)

/-! ### Forward Hensel transport for the canonical lifted subset

The next theorem closes the forward `represents_lifted_of_modP` direction of
`HenselSubsetLiftHypotheses`: if `factor` is a monic integer divisor of `core`
that is represented modulo `primeData.p` by the modular-factor subset `S`,
then the canonical Hensel lift `liftedSubsetOfModPSubset` of `S` represents
`factor` modulo `primeData.p ^ B` on the integer side. The proof feeds the
packaged subset/complement product (`#4752`) and coprimality (`#4761`) inputs
into `HexHenselMathlib.hensel_unique` and converts the resulting Mathlib
`Polynomial.map` equality back to the executable `Hex.ZPoly.reduceModPow`
equality stored by `RepresentsIntegerFactorAtLift`. -/

/-- Monic integer polynomials reduce to non-`isZero` `FpPoly` images modulo
any prime `p > 1`: the leading coefficient `1` survives reduction, so the
stored size is preserved. -/
private theorem modP_isZero_false_of_monic
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    {f : Hex.ZPoly} (hf_monic : Hex.DensePoly.Monic f) (hp : 1 < p) :
    (Hex.ZPoly.modP p f).isZero = false := by
  have hf_size_pos : 0 < f.size := zpoly_size_pos_of_monic hf_monic
  have hf_lead : f.coeff (f.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hf_size_pos]
    exact hf_monic
  have hmod1 : 1 % p = 1 := Nat.mod_eq_of_lt hp
  have htoNat_one : (1 : Hex.ZMod64 p).toNat = 1 := by
    show Hex.ZMod64.one.toNat = 1
    rw [Hex.ZMod64.toNat_one, hmod1]
  have hone_ne_zero : (1 : Hex.ZMod64 p) ≠ (0 : Hex.ZMod64 p) := by
    intro h
    have hnat := congrArg Hex.ZMod64.toNat h
    rw [htoNat_one, show (0 : Hex.ZMod64 p) = Hex.ZMod64.zero from rfl,
        Hex.ZMod64.toNat_zero] at hnat
    exact absurd hnat (by decide)
  have hmodP_coeff_lead :
      (Hex.ZPoly.modP p f).coeff (f.size - 1) = (1 : Hex.ZMod64 p) := by
    rw [Hex.ZPoly.coeff_modP, hf_lead]
    have hintModNat : Hex.ZPoly.intModNat (1 : Int) p = 1 := by
      show Int.toNat ((1 : Int) % Int.ofNat p) = 1
      have hppos : (1 : Int) < Int.ofNat p := Int.ofNat_lt.mpr hp
      rw [Int.emod_eq_of_lt (by decide) hppos]
      rfl
    rw [hintModNat]
    rfl
  have hmodP_size_pos : 0 < (Hex.ZPoly.modP p f).size := by
    rcases Nat.eq_zero_or_pos (Hex.ZPoly.modP p f).size with hsz | hsz
    · exfalso
      have hcoeff_zero :
          (Hex.ZPoly.modP p f).coeff (f.size - 1) = 0 := by
        apply Hex.DensePoly.coeff_eq_zero_of_size_le
        omega
      rw [hcoeff_zero] at hmodP_coeff_lead
      exact hone_ne_zero hmodP_coeff_lead.symm
    · exact hsz
  exact (Hex.DensePoly.isZero_eq_false_iff _).mpr hmodP_size_pos

/-- `monicModPImage` is the identity on the mod-`p` reduction of a monic
integer polynomial, since the leading coefficient `1` reduces to `1` and
`(1 : ZMod64 p)⁻¹ = 1`. -/
private theorem monicModPImage_modP_eq_self_of_monic
    {p : Nat} [Hex.ZMod64.Bounds p] [Hex.ZMod64.PrimeModulus p]
    {f : Hex.ZPoly} (hf_monic : Hex.DensePoly.Monic f)
    (hprime : Hex.Nat.Prime p) (hp : 1 < p) :
    monicModPImage (Hex.ZPoly.modP p f) = Hex.ZPoly.modP p f := by
  rw [monicModPImage_eq_monicModularImage]
  exact monicModularImage_modP_eq_of_monic f hf_monic hprime hp
    (modP_isZero_false_of_monic hf_monic hp)

/-- Forward Hensel-lift transport for the canonical lifted subset: a monic
integer factor of `core` that is represented modulo `primeData.p` by a
modular-factor subset `S` is represented modulo `primeData.p ^ B` on the
integer side by the corresponding canonical lifted subset
`liftedSubsetOfModPSubset primeData d hsize S`.

The proof packages the subset/complement product modulo `p ^ B`
(`henselLiftData_liftedFactorProduct_subset_complement_congr_core`) and the
subset/complement coprimality modulo `p`
(`henselLiftData_liftedSubset_complement_isCoprime_mod_p`) into the
hypothesis list of `HexHenselMathlib.hensel_unique`, alongside the integer
factorization `core = factor * q` derived from `factor ∣ core` and the
mod-`p` subset representation hypothesis. Converting the resulting Mathlib
`Polynomial.map` equality back to the executable
`Hex.ZPoly.reduceModPow` form via
`HexHenselMathlib.zpoly_congr_of_toPolynomial_map_eq` and
`Hex.ZPoly.reduceModPow_eq_of_congr` discharges
`RepresentsIntegerFactorAtLift`.

This is the forward `represents_lifted_of_modP` field of
`HenselSubsetLiftHypotheses` (#4733 for parent #4695); the analytic
hypotheses listed here are the inputs that the constructor successor #4697
will package from `Hex.choosePrimeData`/`Hex.henselLiftData` boundary
facts. -/
theorem henselLiftData_represents_lifted_of_modP
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprime : _root_.Nat.Prime primeData.p)
    (hprime_invariant :
      letI := primeData.bounds
      Hex.ZPoly.QuadraticMultifactorLiftInvariant
        primeData.p B core
        (primeData.factorsModP.map Hex.FpPoly.liftToZ).toList)
    (hB : 1 ≤ B)
    (hfactors_monic :
      letI := primeData.bounds
      ∀ g ∈ primeData.factorsModP, Hex.DensePoly.Monic g)
    (hproduct_mod_p :
      letI := primeData.bounds
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        core primeData.p)
    (hfactors_irr :
      letI := primeData.bounds
      ∀ i : ModPFactorIndex primeData,
        Irreducible
          (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)))
    (hfactors_nodup : primeData.factorsModP.toList.Nodup)
    {factor : Hex.ZPoly} {S : ModPFactorSubset primeData}
    (hfactor_monic : Hex.DensePoly.Monic factor)
    (_hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd : factor ∣ core)
    (hrepP : RepresentsIntegerFactorModP primeData factor S) :
    letI := primeData.bounds
    RepresentsIntegerFactorAtLift core (Hex.henselLiftData core B primeData) factor
      (liftedSubsetOfModPSubset primeData (Hex.henselLiftData core B primeData)
        (henselLiftData_liftedFactors_size_eq core B primeData) S) := by
  letI := primeData.bounds
  haveI hprime_fact : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime⟩
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime
      (by
        constructor
        · exact hprime.two_le
        · intro m hmdvd
          rcases hprime.eq_one_or_self_of_dvd m hmdvd with h | h
          · exact Or.inl h
          · exact Or.inr h)
  have hp : 1 < primeData.p := hprime.one_lt
  have hprime_hex : Hex.Nat.Prime primeData.p := by
    constructor
    · exact hprime.two_le
    · intro m hmdvd
      rcases hprime.eq_one_or_self_of_dvd m hmdvd with h | h
      · exact Or.inl h
      · exact Or.inr h
  obtain ⟨q, hcoreq⟩ := hfactor_dvd
  -- Mathlib aliases for the Hensel-unique inputs.
  set d := Hex.henselLiftData core B primeData with hd_def
  set hsize := henselLiftData_liftedFactors_size_eq core B primeData with hsize_def
  set liftedS := liftedSubsetOfModPSubset primeData d hsize S with hliftedS_def
  set complementS : LiftedFactorSubset d := (Finset.univ : LiftedFactorSubset d) \ liftedS
    with hcomplementS_def
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  set g := HexPolyZMathlib.toPolynomial (liftedFactorProduct d liftedS) with hg_def
  set h := HexPolyZMathlib.toPolynomial (liftedFactorProduct d complementS) with hh_def
  set g' := HexPolyZMathlib.toPolynomial factor with hg'_def
  set h' := HexPolyZMathlib.toPolynomial q with hh'_def
  -- Monicness.
  have hg_dense_monic : Hex.DensePoly.Monic (liftedFactorProduct d liftedS) :=
    henselLiftData_liftedFactorProduct_monic core B primeData
      hcore_monic hprime_invariant hp hB liftedS
  have hg_monic : g.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hg_dense_monic
  have hg'_monic : g'.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hfactor_monic
  -- Subset/complement product modulo `p ^ B` on the lifted side.
  have hgh_congr :
      Hex.ZPoly.congr
        (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)
        core (primeData.p ^ B) :=
    henselLiftData_liftedFactorProduct_subset_complement_congr_core
      core B primeData hprime_invariant hp hB liftedS
  have hgh_map_pB :
      (HexPolyZMathlib.toPolynomial
          (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)).map
          (Int.castRingHom (ZMod (primeData.p ^ B))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _ hgh_congr
  have hprod :
      (g.map (Int.castRingHom (ZMod (primeData.p ^ B)))) *
          (h.map (Int.castRingHom (ZMod (primeData.p ^ B)))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) := by
    have hmul := hgh_map_pB
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul] at hmul
    exact hmul
  -- Integer-side product (`core = factor * q`).
  have hf_eq : f = g' * h' := by
    rw [hf_def, hg'_def, hh'_def, hcoreq, HexPolyZMathlib.toPolynomial_mul]
  have hprod' :
      (g'.map (Int.castRingHom (ZMod (primeData.p ^ B)))) *
          (h'.map (Int.castRingHom (ZMod (primeData.p ^ B)))) =
        f.map (Int.castRingHom (ZMod (primeData.p ^ B))) := by
    rw [hf_eq, Polynomial.map_mul]
  -- Identify `RepresentsIntegerFactorModP` with the Mathlib mod-`p` map equality.
  have hg1 :
      g.map (Int.castRingHom (ZMod primeData.p)) =
        g'.map (Int.castRingHom (ZMod primeData.p)) := by
    have h1 :=
      toPolynomial_liftedSubset_map_intCast_zmod_eq_toMathlibPolynomial
        core B primeData hcore_monic hprime_invariant hp hB
        hfactors_monic hproduct_mod_p S
    have h2 : modPFactorProduct primeData S =
        monicModPImage (Hex.ZPoly.modP primeData.p factor) := hrepP
    have h3 := monicModPImage_modP_eq_self_of_monic
      (f := factor) hfactor_monic hprime_hex hp
    have h4 := toMathlibPolynomial_modP_eq_map_intCast_zmod (p := primeData.p) factor
    show (HexPolyZMathlib.toPolynomial (liftedFactorProduct d liftedS)).map
          (Int.castRingHom (ZMod primeData.p)) =
        (HexPolyZMathlib.toPolynomial factor).map (Int.castRingHom (ZMod primeData.p))
    rw [show liftedS = liftedSubsetOfModPSubset primeData d hsize S from rfl,
      h1, h2, h3, h4]
  -- Derive `hdeg` from `hg1` and monicness via `Monic.natDegree_map`.
  haveI : Nontrivial (ZMod primeData.p) := inferInstance
  have hdeg : g.natDegree = g'.natDegree := by
    have hg_map_natDeg :
        (g.map (Int.castRingHom (ZMod primeData.p))).natDegree = g.natDegree :=
      hg_monic.natDegree_map (Int.castRingHom (ZMod primeData.p))
    have hg'_map_natDeg :
        (g'.map (Int.castRingHom (ZMod primeData.p))).natDegree = g'.natDegree :=
      hg'_monic.natDegree_map (Int.castRingHom (ZMod primeData.p))
    rw [← hg_map_natDeg, ← hg'_map_natDeg, hg1]
  -- Mod-`p` map equality on the complement, via cancellation in `Polynomial (ZMod p)`.
  have hp_dvd_pB : primeData.p ∣ primeData.p ^ B := by
    have h := Nat.pow_dvd_pow primeData.p hB
    simpa using h
  have hgh_congr_p :
      Hex.ZPoly.congr
        (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)
        core primeData.p :=
    Hex.ZPoly.congr_of_dvd_modulus _ _ hp_dvd_pB hgh_congr
  have hgh_map_p :
      (HexPolyZMathlib.toPolynomial
          (liftedFactorProduct d liftedS * liftedFactorProduct d complementS)).map
          (Int.castRingHom (ZMod primeData.p)) =
        f.map (Int.castRingHom (ZMod primeData.p)) :=
    HexHenselMathlib.zpoly_congr_toPolynomial_map_eq _ _ _ hgh_congr_p
  have hprod_p :
      (g.map (Int.castRingHom (ZMod primeData.p))) *
          (h.map (Int.castRingHom (ZMod primeData.p))) =
        f.map (Int.castRingHom (ZMod primeData.p)) := by
    have hmul := hgh_map_p
    rw [HexPolyZMathlib.toPolynomial_mul, Polynomial.map_mul] at hmul
    exact hmul
  have hprod'_p :
      (g'.map (Int.castRingHom (ZMod primeData.p))) *
          (h'.map (Int.castRingHom (ZMod primeData.p))) =
        f.map (Int.castRingHom (ZMod primeData.p)) := by
    rw [hf_eq, Polynomial.map_mul]
  have hg_map_p_monic : (g.map (Int.castRingHom (ZMod primeData.p))).Monic :=
    hg_monic.map _
  have hg'_map_p_monic : (g'.map (Int.castRingHom (ZMod primeData.p))).Monic :=
    hg'_monic.map _
  have hg'_map_p_ne_zero : g'.map (Int.castRingHom (ZMod primeData.p)) ≠ 0 :=
    hg'_map_p_monic.ne_zero
  have hh1 :
      h.map (Int.castRingHom (ZMod primeData.p)) =
        h'.map (Int.castRingHom (ZMod primeData.p)) := by
    have hsame :
        (g'.map (Int.castRingHom (ZMod primeData.p))) *
            (h.map (Int.castRingHom (ZMod primeData.p))) =
          (g'.map (Int.castRingHom (ZMod primeData.p))) *
            (h'.map (Int.castRingHom (ZMod primeData.p))) := by
      calc (g'.map (Int.castRingHom (ZMod primeData.p))) *
              (h.map (Int.castRingHom (ZMod primeData.p)))
          = (g.map (Int.castRingHom (ZMod primeData.p))) *
              (h.map (Int.castRingHom (ZMod primeData.p))) := by rw [hg1]
        _ = f.map (Int.castRingHom (ZMod primeData.p)) := hprod_p
        _ = (g'.map (Int.castRingHom (ZMod primeData.p))) *
              (h'.map (Int.castRingHom (ZMod primeData.p))) := hprod'_p.symm
    exact mul_left_cancel₀ hg'_map_p_ne_zero hsame
  -- Subset/complement coprimality modulo `p` (#4761).
  have hcop :
      IsCoprime (g.map (Int.castRingHom (ZMod primeData.p)))
        (h.map (Int.castRingHom (ZMod primeData.p))) :=
    henselLiftData_liftedSubset_complement_isCoprime_mod_p
      core B primeData hcore_monic hprime hprime_invariant hp hB
      hfactors_monic hproduct_mod_p hfactors_irr hfactors_nodup S
  -- Apply `hensel_unique`.
  obtain ⟨hgg', _⟩ :=
    HexHenselMathlib.hensel_unique f g h g' h' primeData.p B hB
      hg_monic hg'_monic hdeg hprod hprod' hg1 hh1 hcop
  -- Convert back to `RepresentsIntegerFactorAtLift`.
  show Hex.ZPoly.reduceModPow (scaledLiftedFactorProduct core d liftedS) d.p d.k =
    Hex.ZPoly.reduceModPow factor d.p d.k
  have hscaled :
      scaledLiftedFactorProduct core d liftedS = liftedFactorProduct d liftedS := by
    unfold scaledLiftedFactorProduct
    rw [show Hex.DensePoly.leadingCoeff core = (1 : Int) from hcore_monic]
    exact densePoly_scale_one_int (liftedFactorProduct d liftedS)
  rw [hscaled]
  have hcongr_pk :
      Hex.ZPoly.congr (liftedFactorProduct d liftedS) factor (primeData.p ^ B) :=
    HexHenselMathlib.zpoly_congr_of_toPolynomial_map_eq _ _ _ hgg'
  have hdp : d.p = primeData.p := rfl
  have hdk : d.k = B := rfl
  rw [hdp, hdk]
  exact Hex.ZPoly.reduceModPow_eq_of_congr _ _ _ _ hcongr_pk

/-- `centeredModNat 1 m = 1` when `m ≥ 2`: the value `1` lies in the centred
half-window and is preserved by the centred-reduction operation. -/
private theorem centeredModNat_one_of_two_le {m : Nat} (hm : 2 ≤ m) :
    Hex.centeredModNat (1 : Int) m = (1 : Int) := by
  by_cases hm3 : 3 ≤ m
  · have hbound : (1 : Int).natAbs ≤ (1 : Nat) := by decide
    have hsep : 2 * (1 : Nat) < m := by omega
    have h := Hex.centeredModNat_emod_eq_of_natAbs_le (1 : Int) m 1 hbound hsep
    have h1mod : (1 : Int) % (m : Int) = 1 :=
      Int.emod_eq_of_lt (by decide) (by exact_mod_cast (show 1 < m by omega))
    rwa [h1mod] at h
  · have hm2 : m = 2 := by omega
    subst hm2
    rfl

/--
Centred-lift preserves monicness once the modulus is at least two.

The leading coefficient `1` of a monic input survives the centred-reduction
(`centeredModNat 1 m = 1` for `m ≥ 2`) and `DensePoly.ofCoeffs` does not trim
it, so the output preserves both size and leading coefficient.
-/
theorem monic_centeredLiftPoly_of_monic
    {g : Hex.ZPoly} (hg : Hex.DensePoly.Monic g) {m : Nat} (hm : 2 ≤ m) :
    Hex.DensePoly.Monic (Hex.centeredLiftPoly g m) := by
  have hg_size_pos : 0 < g.size := zpoly_size_pos_of_monic hg
  have hg_lead : g.coeff (g.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_size_pos]; exact hg
  set g' := Hex.centeredLiftPoly g m with hg'_def
  have hcoeff : ∀ i, g'.coeff i = Hex.centeredModNat (g.coeff i) m :=
    fun i => Hex.coeff_centeredLiftPoly g m i
  have hcoeff_top : g'.coeff (g.size - 1) = (1 : Int) := by
    rw [hcoeff, hg_lead]; exact centeredModNat_one_of_two_le hm
  have hg'_size_ge : g.size ≤ g'.size := by
    by_contra hlt
    have hlt' : g'.size < g.size := Nat.lt_of_not_ge hlt
    have hle : g'.size ≤ g.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g' hle
    rw [hcoeff_top] at h_zero
    exact absurd h_zero (by decide)
  have hg'_size_le : g'.size ≤ g.size := by
    rw [hg'_def]
    unfold Hex.centeredLiftPoly
    have h := Hex.DensePoly.size_ofCoeffs_le
      (g.toArray.map fun coeff => Hex.centeredModNat coeff m)
    rw [Array.size_map] at h
    -- `g.toArray.size = g.coeffs.size = g.size` definitionally
    exact h
  have hg'_size_eq : g'.size = g.size := le_antisymm hg'_size_le hg'_size_ge
  show Hex.DensePoly.leadingCoeff g' = (1 : Int)
  rw [Hex.DensePoly.leadingCoeff_eq_coeff_last g' (hg'_size_eq ▸ hg_size_pos),
    hg'_size_eq]
  exact hcoeff_top

/-- Centred-lift preserves stored size when the input is monic and the modulus
is at least two. The leading coefficient `1` survives the centred reduction
(forcing `g'.size ≥ g.size`) and `DensePoly.ofCoeffs` never grows the array
(forcing `g'.size ≤ g.size`). -/
private theorem size_centeredLiftPoly_eq_of_monic
    {g : Hex.ZPoly} (hg : Hex.DensePoly.Monic g) {m : Nat} (hm : 2 ≤ m) :
    (Hex.centeredLiftPoly g m).size = g.size := by
  have hg_size_pos : 0 < g.size := zpoly_size_pos_of_monic hg
  have hg_lead : g.coeff (g.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_size_pos]; exact hg
  set g' := Hex.centeredLiftPoly g m with hg'_def
  have hcoeff : ∀ i, g'.coeff i = Hex.centeredModNat (g.coeff i) m :=
    fun i => Hex.coeff_centeredLiftPoly g m i
  have hcoeff_top : g'.coeff (g.size - 1) = (1 : Int) := by
    rw [hcoeff, hg_lead]; exact centeredModNat_one_of_two_le hm
  have hg'_size_ge : g.size ≤ g'.size := by
    by_contra hlt
    have hlt' : g'.size < g.size := Nat.lt_of_not_ge hlt
    have hle : g'.size ≤ g.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g' hle
    rw [hcoeff_top] at h_zero
    exact absurd h_zero (by decide)
  have hg'_size_le : g'.size ≤ g.size := by
    rw [hg'_def]
    unfold Hex.centeredLiftPoly
    have h := Hex.DensePoly.size_ofCoeffs_le
      (g.toArray.map fun coeff => Hex.centeredModNat coeff m)
    rw [Array.size_map] at h
    exact h
  exact le_antisymm hg'_size_le hg'_size_ge

/--
The Mathlib-transported `natDegree` of the executable recombination candidate
over a lifted-factor subset equals the sum of the Mathlib-transported
`natDegree`s of the selected lifted factors.

Under the modulus condition `2 ≤ d.p ^ d.k` and monicness of every lifted
factor, the candidate's `centeredLiftPoly`/`primitivePart`/`normalizeFactorSign`
chain collapses to a single monic polynomial whose stored size is the same as
the underlying lifted-factor product, so its Mathlib-side `natDegree` is the
sum over the subset.

This is the candidate-side ingredient of the reverse-coverage degree-counting
argument in the `representedFactor_dvd_recombinationCandidate_of_subset`
divisibility theorem; see issue #4439.
-/
theorem natDegree_toPolynomial_recombinationCandidate_eq_sum
    {d : Hex.LiftData}
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
      ∑ i ∈ T,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  set lp := liftedFactorProduct d T with hlp_def
  -- lp is monic from monicness of each lifted factor.
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  -- centeredLiftPoly preserves monicness under the modulus condition.
  have hcl_monic := monic_centeredLiftPoly_of_monic hlp_monic hd_modulus
  set cl := Hex.centeredLiftPoly lp (d.p ^ d.k) with hcl_def
  -- A monic poly has trivial content and trivial sign normalisation.
  have hnorm : Hex.normalizeFactorSign cl = cl :=
    zpoly_normalize_factor_sign_of_monic hcl_monic
  have hprim : Hex.ZPoly.primitivePart cl = cl :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive cl
      (zpoly_primitive_of_monic hcl_monic)
  -- Combining, the candidate is just the centered lift of the product.
  have hrec_eq : recombinationCandidate d T = cl := by
    unfold recombinationCandidate
    rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct,
      ← hlp_def, ← hcl_def, hprim, hnorm]
  rw [hrec_eq]
  -- The centered lift has the same stored size as the product.
  have hsize_eq : cl.size = lp.size :=
    size_centeredLiftPoly_eq_of_monic hlp_monic hd_modulus
  -- `natDegree (toPolynomial _)` is `size - 1` on a nonzero (monic) poly.
  have hcl_size_pos : 0 < cl.size := zpoly_size_pos_of_monic hcl_monic
  have hlp_size_pos : 0 < lp.size := zpoly_size_pos_of_monic hlp_monic
  have hcl_natDeg :
      (HexPolyZMathlib.toPolynomial cl).natDegree = cl.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hcl_size_pos]
  have hlp_natDeg :
      (HexPolyZMathlib.toPolynomial lp).natDegree = lp.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hlp_size_pos]
  rw [hcl_natDeg, hsize_eq, ← hlp_natDeg, hlp_def, toPolynomial_liftedFactorProduct]
  -- Mathlib `natDegree_prod_of_monic` over monic factors.
  apply Polynomial.natDegree_prod_of_monic
  intro i _
  -- Monicness of `toPolynomial (liftedFactor d i)` from monicness of the
  -- lifted factor itself via `HexPolyMathlib.leadingCoeff_toPolynomial`.
  show (HexPolyZMathlib.toPolynomial (liftedFactor d i)).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact hd_liftedFactor_monic i

/-- Abstract-bound variant of `natDegree_toPolynomial_eq_sum_of_represents`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The proof mirrors
the core-shape original but invokes the `_of_bound` siblings
`recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound` and
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`. -/
theorem natDegree_toPolynomial_eq_sum_of_represents_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hdvd : factor ∣ core)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    (HexPolyZMathlib.toPolynomial factor).natDegree =
      ∑ i ∈ S,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  have hrec_eq : recombinationCandidate d S = factor :=
    recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound
      B' hvalid hcore_ne hcore_monic hfactor_prim hfactor_norm hfactor_irr
      hrep hprecision
  have hlead : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  have hscaled :
      scaledLiftedFactorProduct core d S = liftedFactorProduct d S := by
    unfold scaledLiftedFactorProduct
    rw [hlead]
    exact densePoly_scale_one_int (liftedFactorProduct d S)
  have hcenter :
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k) = factor := by
    have h :=
      centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
        B' hvalid hrep hprecision
    rwa [hscaled] at h
  have hfactor_ne : factor ≠ 0 := by
    intro hf
    rcases hdvd with ⟨q, hq⟩
    rw [hf, Hex.DensePoly.zero_mul (S := Int) q] at hq
    exact hcore_ne hq
  have hpk_pos : 0 < d.p ^ d.k := Nat.pow_pos d.p_pos
  have hpk_ge_two : 2 ≤ d.p ^ d.k := by
    rcases Nat.eq_or_lt_of_le
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpk_pos)) with hpk1 | hpk_gt
    · exfalso
      apply hfactor_ne
      apply Hex.DensePoly.ext_coeff
      intro i
      rw [← hcenter, Hex.coeff_centeredLiftPoly, ← hpk1,
        Hex.DensePoly.coeff_zero]
      unfold Hex.centeredModNat
      have h1ne : (1 : Nat) ≠ 0 := by decide
      simp only [if_neg h1ne]
      simp
    · omega
  rw [← hrec_eq]
  exact natDegree_toPolynomial_recombinationCandidate_eq_sum
    hpk_ge_two hd_liftedFactor_monic S

/--
The Mathlib-transported `natDegree` of a represented integer factor equals the
sum of the Mathlib-transported `natDegree`s of the lifted factors in the
representing subset.

The proof identifies the represented factor with its recombination candidate
by centered-lift recovery, then reuses
`natDegree_toPolynomial_recombinationCandidate_eq_sum`.

This is a thin wrapper over `natDegree_toPolynomial_eq_sum_of_represents_of_bound`
that instantiates `B' := defaultFactorCoeffBound core` and discharges `hvalid`
via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd`.
-/
theorem natDegree_toPolynomial_eq_sum_of_represents
    {core factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hdvd : factor ∣ core)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S) :
    (HexPolyZMathlib.toPolynomial factor).natDegree =
      ∑ i ∈ S,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree :=
  natDegree_toPolynomial_eq_sum_of_represents_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_ne hcore_monic hd_liftedFactor_monic hdvd hfactor_irr
    hfactor_prim hfactor_norm hrep hprecision

/--
Abstract-bound variant of `representsIntegerFactorAtLift_monic`: takes
`B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint. All remaining
hypotheses are unchanged; the proof mirrors
`representsIntegerFactorAtLift_monic` with the recovery call delegated to
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`.
-/
theorem representsIntegerFactorAtLift_monic_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hfactor_dvd_target : factor ∣ target)
    (htarget_dvd_core : target ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    Hex.DensePoly.Monic factor := by
  have hfactor_dvd_core : factor ∣ core :=
    zpoly_dvd_trans hfactor_dvd_target htarget_dvd_core
  have hprod_monic : Hex.DensePoly.Monic (liftedFactorProduct d S) :=
    liftedFactorProduct_monic d S (fun i _ => hd_liftedFactor_monic i)
  have hlead : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  have hscaled :
      scaledLiftedFactorProduct core d S = liftedFactorProduct d S := by
    unfold scaledLiftedFactorProduct
    rw [hlead]
    exact densePoly_scale_one_int (liftedFactorProduct d S)
  have hcenter :
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k) = factor := by
    have h :=
      centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
        B' hvalid hrep hprecision
    rwa [hscaled] at h
  have hfactor_ne : factor ≠ 0 := by
    intro hf
    rcases hfactor_dvd_core with ⟨q, hq⟩
    rw [hf, Hex.DensePoly.zero_mul (S := Int) q] at hq
    exact hcore_ne hq
  have hpk_pos : 0 < d.p ^ d.k := Nat.pow_pos d.p_pos
  have hpk_ge_two : 2 ≤ d.p ^ d.k := by
    rcases Nat.eq_or_lt_of_le
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpk_pos)) with hpk1 | hpk_gt
    · exfalso
      apply hfactor_ne
      apply Hex.DensePoly.ext_coeff
      intro i
      rw [← hcenter, Hex.coeff_centeredLiftPoly, ← hpk1,
        Hex.DensePoly.coeff_zero]
      unfold Hex.centeredModNat
      have h1ne : (1 : Nat) ≠ 0 := by decide
      simp only [if_neg h1ne]
      simp
    · omega
  rw [← hcenter]
  exact monic_centeredLiftPoly_of_monic hprod_monic hpk_ge_two

/--
Integer-factor monic capstone for the Hensel-lifted subset correspondence.

Given an integer factor `factor` of `target ∣ core` that is represented at the
Hensel lift by the subset `S`, plus monicness of the core and of every lifted
local factor, and the Mignotte precision bound, the represented factor is
itself monic.

This is the caller-side packaging that discharges the `Monic factor`
hypothesis needed by `recombinationCandidate_eq_factor_of_recovery` (via
`monic_primitive_sign_normalized_of_monic`). The proof chains
`liftedFactorProduct_monic` with the centred-lift recovery
(`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery`) and
`monic_centeredLiftPoly_of_monic`; the precision hypothesis upgrades to
`2 ≤ d.p ^ d.k` because otherwise the centred lift collapses to zero,
contradicting `factor ∣ core` with `core ≠ 0`.

Thin wrapper over `representsIntegerFactorAtLift_monic_of_bound` that
instantiates `B' := defaultFactorCoeffBound core` and discharges `hvalid`
via `defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd_core`.
-/
theorem representsIntegerFactorAtLift_monic
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hfactor_dvd_target : factor ∣ target)
    (htarget_dvd_core : target ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor S) :
    Hex.DensePoly.Monic factor := by
  have hfactor_dvd_core : factor ∣ core :=
    zpoly_dvd_trans hfactor_dvd_target htarget_dvd_core
  exact representsIntegerFactorAtLift_monic_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd_core)
    hcore_ne hcore_monic hd_liftedFactor_monic
    hfactor_dvd_target htarget_dvd_core hrep hprecision

/--
Identification of the executable `Hex.ZPoly.Primitive` predicate with Mathlib's
`Polynomial.IsPrimitive` on the transported polynomial.
-/
private theorem toPolynomial_isPrimitive_of_zpoly_primitive_basic
    {f : Hex.ZPoly} (hprim : Hex.ZPoly.Primitive f) :
    (HexPolyZMathlib.toPolynomial f).IsPrimitive := by
  intro r hdvd
  have hcoeff : ∀ n, r ∣ f.coeff n := by
    intro n
    have h :=
      (Polynomial.C_dvd_iff_dvd_coeff r (HexPolyZMathlib.toPolynomial f)).mp hdvd n
    rwa [HexPolyZMathlib.coeff_toPolynomial] at h
  have hnatAbs_dvd : ∀ n, (r.natAbs : ℤ) ∣ f.coeff n := fun n =>
    Int.natAbs_dvd.mpr (hcoeff n)
  have hr_dvd_content : (r.natAbs : ℤ) ∣ Hex.ZPoly.content f :=
    Hex.ZPoly.dvd_content_of_nat_dvd_coeff f r.natAbs hnatAbs_dvd
  rw [show Hex.ZPoly.content f = 1 from hprim] at hr_dvd_content
  have hone : r.natAbs ∣ 1 := by exact_mod_cast hr_dvd_content
  exact Int.isUnit_iff_natAbs_eq.mpr (Nat.eq_one_of_dvd_one hone)

/--
Reverse identification from Mathlib's `Polynomial.IsPrimitive` on the transported
polynomial to the executable `Hex.ZPoly.Primitive` predicate.
-/
private theorem zpoly_primitive_of_toPolynomial_isPrimitive_basic
    {f : Hex.ZPoly}
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive) :
    Hex.ZPoly.Primitive f := by
  show Hex.ZPoly.content f = 1
  have hC_dvd :
      Polynomial.C (Hex.ZPoly.content f) ∣ HexPolyZMathlib.toPolynomial f := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    intro n
    rw [HexPolyZMathlib.coeff_toPolynomial]
    exact Hex.ZPoly.content_dvd_coeff f n
  have hIsUnit : IsUnit (Hex.ZPoly.content f) := hprim _ hC_dvd
  have hcontent_nonneg : 0 ≤ Hex.ZPoly.content f := by
    show 0 ≤ Hex.DensePoly.content _
    unfold Hex.DensePoly.content
    exact Int.natCast_nonneg _
  rcases Int.isUnit_iff.mp hIsUnit with hone | hneg
  · exact hone
  · rw [hneg] at hcontent_nonneg
    omega

/-- A `Hex.ZPoly` with positive leading coefficient is nonzero. -/
theorem zpoly_ne_zero_of_pos_lc {f : Hex.ZPoly}
    (hpos : 0 < Hex.DensePoly.leadingCoeff f) : f ≠ 0 := by
  intro hf
  rw [hf] at hpos
  have hzero_lc : Hex.DensePoly.leadingCoeff (0 : Hex.ZPoly) = 0 := rfl
  rw [hzero_lc] at hpos
  omega

/-- A `Hex.ZPoly` with positive leading coefficient has positive stored size. -/
private theorem zpoly_size_pos_of_pos_lc {f : Hex.ZPoly}
    (hpos : 0 < Hex.DensePoly.leadingCoeff f) : 0 < f.size := by
  rcases Nat.eq_zero_or_pos f.coeffs.size with hcs_zero | hcs_pos
  · exfalso
    have hback_none : f.coeffs.back? = none := by
      rw [Array.back?_eq_getElem?]; simp [hcs_zero]
    have hlc_zero : Hex.DensePoly.leadingCoeff f = (0 : Int) := by
      unfold Hex.DensePoly.leadingCoeff; rw [hback_none]; rfl
    rw [hlc_zero] at hpos
    omega
  · exact hcs_pos

private theorem zpoly_eq_one_of_toPolynomial_isUnit_of_pos_lc
    {f : Hex.ZPoly}
    (hpos : 0 < Hex.DensePoly.leadingCoeff f)
    (hunit : IsUnit (HexPolyZMathlib.toPolynomial f)) :
    f = 1 := by
  have hunit_z : Hex.ZPoly.IsUnit f :=
    (HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mpr hunit
  rcases hunit_z with hunit_one | hunit_neg
  · rw [hunit_one]
    rfl
  · exfalso
    rw [hunit_neg] at hpos
    change 0 < Hex.DensePoly.leadingCoeff (Hex.DensePoly.C (-1 : Int)) at hpos
    simp [Hex.DensePoly.leadingCoeff, Hex.DensePoly.coeffs_C_of_ne_zero] at hpos

private theorem zpoly_primitive_of_dvd_primitive_basic
    {factor target : Hex.ZPoly}
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (hfactor_dvd_target : factor ∣ target) :
    Hex.ZPoly.Primitive factor := by
  apply zpoly_primitive_of_toPolynomial_isPrimitive_basic
  exact isPrimitive_of_dvd
    (toPolynomial_isPrimitive_of_zpoly_primitive_basic htarget_primitive)
    (HexPolyMathlib.toPolynomial_dvd hfactor_dvd_target)

private theorem zpoly_left_pos_lc_of_mul_eq_of_pos_lc
    {left right target : Hex.ZPoly}
    (hmul : left * right = target)
    (hright_pos : 0 < Hex.DensePoly.leadingCoeff right)
    (htarget_pos : 0 < Hex.DensePoly.leadingCoeff target) :
    0 < Hex.DensePoly.leadingCoeff left := by
  have hright_ne : right ≠ 0 := zpoly_ne_zero_of_pos_lc hright_pos
  have htarget_ne : target ≠ 0 := zpoly_ne_zero_of_pos_lc htarget_pos
  have hleft_ne : left ≠ 0 := by
    intro hleft
    apply htarget_ne
    rw [← hmul, hleft, Hex.DensePoly.zero_mul]
  have hlc :=
    Hex.ZPoly.leadingCoeff_mul_of_nonzero left right hleft_ne hright_ne
  have hprod_pos :
      0 < Hex.DensePoly.leadingCoeff left *
        Hex.DensePoly.leadingCoeff right := by
    rw [← hlc, hmul]
    exact htarget_pos
  nlinarith

private theorem centeredModNat_eq_of_pos_natAbs_le
    {z : Int} {m B : Nat}
    (hz_pos : 0 < z) (hbound : z.natAbs ≤ B) (hsep : 2 * B < m) :
    Hex.centeredModNat z m = z := by
  have hz_nonneg : 0 ≤ z := le_of_lt hz_pos
  have hltNat : z.natAbs < m := by omega
  have hlt : z < (m : Int) := by
    have hz_le_abs : z ≤ (z.natAbs : Int) := by
      rw [Int.natAbs_of_nonneg hz_nonneg]
    have habs_lt : (z.natAbs : Int) < (m : Int) := by exact_mod_cast hltNat
    exact lt_of_le_of_lt hz_le_abs habs_lt
  have hmod : z % (m : Int) = z := Int.emod_eq_of_lt hz_nonneg hlt
  have hcenter :=
    Hex.centeredModNat_emod_eq_of_natAbs_le z m B hbound hsep
  rwa [hmod] at hcenter

/--
Centred-lift preserves a strictly positive leading coefficient that lies inside
the Mignotte half-window.
-/
private theorem leadingCoeff_centeredLiftPoly_of_pos_leadingCoeff_bound
    {g : Hex.ZPoly} {m B : Nat}
    (hg_lc_pos : 0 < Hex.DensePoly.leadingCoeff g)
    (hbound_lc : (Hex.DensePoly.leadingCoeff g).natAbs ≤ B)
    (hsep : 2 * B < m) :
    Hex.DensePoly.leadingCoeff (Hex.centeredLiftPoly g m) =
      Hex.DensePoly.leadingCoeff g := by
  have hg_size_pos : 0 < g.size := zpoly_size_pos_of_pos_lc hg_lc_pos
  have hg_lead :
      g.coeff (g.size - 1) = Hex.DensePoly.leadingCoeff g := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_size_pos]
  set g' := Hex.centeredLiftPoly g m with hg'_def
  have hcoeff : ∀ i, g'.coeff i = Hex.centeredModNat (g.coeff i) m :=
    fun i => Hex.coeff_centeredLiftPoly g m i
  have hcoeff_top :
      g'.coeff (g.size - 1) = Hex.DensePoly.leadingCoeff g := by
    rw [hcoeff, hg_lead]
    exact centeredModNat_eq_of_pos_natAbs_le hg_lc_pos hbound_lc hsep
  have hg'_size_ge : g.size ≤ g'.size := by
    by_contra hlt
    have hlt' : g'.size < g.size := Nat.lt_of_not_ge hlt
    have hle : g'.size ≤ g.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g' hle
    rw [hcoeff_top] at h_zero
    exact (ne_of_gt hg_lc_pos) h_zero
  have hg'_size_le : g'.size ≤ g.size := by
    rw [hg'_def]
    unfold Hex.centeredLiftPoly
    have h := Hex.DensePoly.size_ofCoeffs_le
      (g.toArray.map fun coeff => Hex.centeredModNat coeff m)
    rw [Array.size_map] at h
    exact h
  have hg'_size_eq : g'.size = g.size := le_antisymm hg'_size_le hg'_size_ge
  show Hex.DensePoly.leadingCoeff g' = Hex.DensePoly.leadingCoeff g
  rw [Hex.DensePoly.leadingCoeff_eq_coeff_last g' (hg'_size_eq ▸ hg_size_pos),
    hg'_size_eq]
  exact hcoeff_top

/--
Abstract-bound variant of `representsIntegerFactorAtLift_primitive`: takes
`B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`,
`hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

The leading-coefficient transport step
(`leadingCoeff_centeredLiftPoly_of_pos_leadingCoeff_bound`) requires its
bound and precision arguments to match — abstracting only over `factor`'s
coefficient bound is not enough, since the transport runs on
`scaledLiftedFactorProduct core d S` whose leading coefficient equals
`lc core`.  The `hcore_lc_le` hypothesis supplies the needed bound on
`lc core` in terms of the abstract `B'`.
-/
theorem representsIntegerFactorAtLift_primitive_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hfactor_dvd_target : factor ∣ target)
    (htarget_dvd_core : target ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    Hex.ZPoly.Primitive factor ∧ 0 < Hex.DensePoly.leadingCoeff factor := by
  have hfactor_dvd_core : factor ∣ core :=
    zpoly_dvd_trans hfactor_dvd_target htarget_dvd_core
  have hfactor_poly_primitive :
      (HexPolyZMathlib.toPolynomial factor).IsPrimitive := by
    have hcore_poly_primitive :
        (HexPolyZMathlib.toPolynomial core).IsPrimitive :=
      toPolynomial_isPrimitive_of_zpoly_primitive_basic hcore_primitive
    exact isPrimitive_of_dvd hcore_poly_primitive
      (HexPolyMathlib.toPolynomial_dvd hfactor_dvd_core)
  have hfactor_primitive : Hex.ZPoly.Primitive factor :=
    zpoly_primitive_of_toPolynomial_isPrimitive_basic hfactor_poly_primitive
  have hprod_monic : Hex.DensePoly.Monic (liftedFactorProduct d S) :=
    liftedFactorProduct_monic d S (fun i _ => hd_liftedFactor_monic i)
  have hcore_lc_ne : Hex.DensePoly.leadingCoeff core ≠ (0 : Int) :=
    ne_of_gt hcore_lc_pos
  have hscaled_lc :
      Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d S) =
        Hex.DensePoly.leadingCoeff core := by
    unfold scaledLiftedFactorProduct
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero
      (Hex.DensePoly.leadingCoeff core) (liftedFactorProduct d S) hcore_lc_ne,
      show Hex.DensePoly.leadingCoeff (liftedFactorProduct d S) = (1 : Int)
        from hprod_monic]
    ring
  have hscaled_lc_pos :
      0 < Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d S) := by
    rw [hscaled_lc]
    exact hcore_lc_pos
  have hscaled_lc_bound :
      (Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d S)).natAbs ≤
        B' := by
    rw [hscaled_lc]
    exact hcore_lc_le
  have hcenter :
      Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k) =
        factor :=
    centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
      B' hvalid hrep hprecision
  have hcenter_lc :
      Hex.DensePoly.leadingCoeff
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S)
            (d.p ^ d.k)) =
        Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d S) :=
    leadingCoeff_centeredLiftPoly_of_pos_leadingCoeff_bound
      hscaled_lc_pos hscaled_lc_bound hprecision
  have hfactor_lc_pos : 0 < Hex.DensePoly.leadingCoeff factor := by
    rw [hcenter] at hcenter_lc
    rw [hcenter_lc, hscaled_lc]
    exact hcore_lc_pos
  exact ⟨hfactor_primitive, hfactor_lc_pos⟩

/--
Primitive/positive-leading capstone for represented factors under a primitive
non-monic core.

Given an integer factor `factor` of `target ∣ core` represented at the Hensel
lift, primitive `core`, positive leading coefficient for `core`, monic lifted
local factors, and Mignotte precision, the represented factor is primitive and
has positive leading coefficient.

This is a thin wrapper over
`representsIntegerFactorAtLift_primitive_of_bound` that instantiates
`B' := defaultFactorCoeffBound core` and discharges the abstract bound
hypotheses via `defaultFactorCoeffBound_valid`.
-/
theorem representsIntegerFactorAtLift_primitive
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hfactor_dvd_target : factor ∣ target)
    (htarget_dvd_core : target ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor S) :
    Hex.ZPoly.Primitive factor ∧ 0 < Hex.DensePoly.leadingCoeff factor := by
  have hfactor_dvd_core : factor ∣ core :=
    zpoly_dvd_trans hfactor_dvd_target htarget_dvd_core
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact representsIntegerFactorAtLift_primitive_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd_core)
    hcore_lc_le
    hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
    hfactor_dvd_target htarget_dvd_core hrep hprecision

/-- Scaling a monic integer polynomial by a nonzero constant preserves its
stored size: the leading coefficient becomes `c * 1 = c ≠ 0`, and `scale` never
grows the array. -/
private theorem size_scale_eq_of_monic_of_ne_zero
    {c : Int} (hc : c ≠ 0) {f : Hex.ZPoly} (hmonic : Hex.DensePoly.Monic f) :
    (Hex.DensePoly.scale c f).size = f.size := by
  have hf_size_pos : 0 < f.size := zpoly_size_pos_of_monic hmonic
  have hf_lead : f.coeff (f.size - 1) = (1 : Int) := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last f hf_size_pos]; exact hmonic
  set g := Hex.DensePoly.scale c f with hg_def
  have hcoeff_top : g.coeff (f.size - 1) = c := by
    rw [hg_def, Hex.DensePoly.coeff_scale (R := Int) c f _ (Int.mul_zero _),
      hf_lead]; ring
  have hg_size_ge : f.size ≤ g.size := by
    by_contra hlt
    have hlt' : g.size < f.size := Nat.lt_of_not_ge hlt
    have hle : g.size ≤ f.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g hle
    rw [hcoeff_top] at h_zero
    exact hc h_zero
  have hg_size_le : g.size ≤ f.size := by
    rw [hg_def]
    unfold Hex.DensePoly.scale
    have h := Hex.DensePoly.size_ofCoeffs_le
      ((f.toArray.toList.map fun a => c * a).toArray)
    rw [List.size_toArray, List.length_map] at h
    simpa [Hex.DensePoly.size] using h
  exact le_antisymm hg_size_le hg_size_ge

/-- Centred-lift preserves stored size when the leading coefficient is strictly
positive and lies inside the Mignotte half-window. Companion to
`leadingCoeff_centeredLiftPoly_of_pos_leadingCoeff_bound`. -/
private theorem size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound
    {g : Hex.ZPoly} {m B : Nat}
    (hg_lc_pos : 0 < Hex.DensePoly.leadingCoeff g)
    (hbound_lc : (Hex.DensePoly.leadingCoeff g).natAbs ≤ B)
    (hsep : 2 * B < m) :
    (Hex.centeredLiftPoly g m).size = g.size := by
  have hg_size_pos : 0 < g.size := zpoly_size_pos_of_pos_lc hg_lc_pos
  have hg_lead :
      g.coeff (g.size - 1) = Hex.DensePoly.leadingCoeff g := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hg_size_pos]
  set g' := Hex.centeredLiftPoly g m with hg'_def
  have hcoeff : ∀ i, g'.coeff i = Hex.centeredModNat (g.coeff i) m :=
    fun i => Hex.coeff_centeredLiftPoly g m i
  have hcoeff_top : g'.coeff (g.size - 1) = Hex.DensePoly.leadingCoeff g := by
    rw [hcoeff, hg_lead]
    exact centeredModNat_eq_of_pos_natAbs_le hg_lc_pos hbound_lc hsep
  have hg'_size_ge : g.size ≤ g'.size := by
    by_contra hlt
    have hlt' : g'.size < g.size := Nat.lt_of_not_ge hlt
    have hle : g'.size ≤ g.size - 1 := Nat.le_pred_of_lt hlt'
    have h_zero := Hex.DensePoly.coeff_eq_zero_of_size_le g' hle
    rw [hcoeff_top] at h_zero
    exact (ne_of_gt hg_lc_pos) h_zero
  have hg'_size_le : g'.size ≤ g.size := by
    rw [hg'_def]
    unfold Hex.centeredLiftPoly
    have h := Hex.DensePoly.size_ofCoeffs_le
      (g.toArray.map fun coeff => Hex.centeredModNat coeff m)
    rw [Array.size_map] at h
    exact h
  exact le_antisymm hg'_size_le hg'_size_ge

/-- `Hex.normalizeFactorSign` preserves stored size: it either returns the input
unchanged or negates every coefficient via `DensePoly.scale (-1)`, and scaling by
the nonzero integer `-1` preserves stored size. -/
private theorem size_normalizeFactorSign_eq (f : Hex.ZPoly) :
    (Hex.normalizeFactorSign f).size = f.size := by
  unfold Hex.normalizeFactorSign
  by_cases hneg : Hex.DensePoly.leadingCoeff f < 0
  · rw [if_pos hneg]
    exact Hex.ZPoly.scale_size_of_nonzero (-1 : Int) f (by decide)
  · rw [if_neg hneg]

/-- `Hex.ZPoly.primitivePart` preserves stored size on nonzero inputs.

Reconstruct `f = scale (content f) (primitivePart f)` via
`content_mul_primitivePart`, then apply `Hex.ZPoly.scale_size_of_nonzero` with
the fact that `content f ≠ 0` whenever `f ≠ 0`. -/
private theorem size_primitivePart_eq_of_ne_zero {f : Hex.ZPoly} (hf : f ≠ 0) :
    (Hex.ZPoly.primitivePart f).size = f.size := by
  have hcontent_ne : (Hex.ZPoly.content f : Int) ≠ 0 := by
    intro hcontent
    apply hf
    have hpart_zero : Hex.ZPoly.primitivePart f = 0 := by
      simpa [Hex.ZPoly.primitivePart] using
        Hex.DensePoly.primitivePart_eq_zero_of_content_eq_zero f
          (by simpa [Hex.ZPoly.content] using hcontent)
    have hreconstruct := Hex.ZPoly.content_mul_primitivePart f
    rw [hcontent, hpart_zero] at hreconstruct
    have : Hex.DensePoly.scale (0 : Int) (0 : Hex.ZPoly) = (0 : Hex.ZPoly) := by
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_scale (R := Int) (0 : Int) (0 : Hex.ZPoly) n
        (Int.zero_mul 0), Hex.DensePoly.coeff_zero]
      exact Int.zero_mul _
    rw [this] at hreconstruct
    exact hreconstruct.symm
  have h_rec := Hex.ZPoly.content_mul_primitivePart f
  have h_scale_size :
      (Hex.DensePoly.scale (Hex.ZPoly.content f) (Hex.ZPoly.primitivePart f)).size =
        (Hex.ZPoly.primitivePart f).size :=
    Hex.ZPoly.scale_size_of_nonzero (Hex.ZPoly.content f)
      (Hex.ZPoly.primitivePart f) hcontent_ne
  calc (Hex.ZPoly.primitivePart f).size
      = (Hex.DensePoly.scale (Hex.ZPoly.content f)
          (Hex.ZPoly.primitivePart f)).size := h_scale_size.symm
    _ = f.size := by rw [h_rec]

/-- Abstract-bound variant of
`natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum`: takes
`B' : Nat`, `hcore_lc_le : (lc core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

The single precision caller in the proof body is
`size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound`, which requires a
leading-coefficient bound on `scaledLiftedFactorProduct core d T`. That
leading coefficient is `lc core`, so the hypothesis-supplied
`hcore_lc_le` discharges the precondition directly.

Follows the `(B', hcore_lc_le, hprecision)` parameter ordering
established by `representsIntegerFactorAtLift_primitive_of_bound`,
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound`,
and `zpoly_primitive_scaledRecombinationCandidate_of_bound`. -/
theorem natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (_hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hprecision : 2 * B' < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T)).natDegree =
      ∑ i ∈ T,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  set lp := liftedFactorProduct d T with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  have hlp_size_pos : 0 < lp.size := zpoly_size_pos_of_monic hlp_monic
  have hcore_lc_ne : Hex.DensePoly.leadingCoeff core ≠ (0 : Int) :=
    ne_of_gt hcore_lc_pos
  have hslp_size :
      (scaledLiftedFactorProduct core d T).size = lp.size := by
    unfold scaledLiftedFactorProduct
    exact size_scale_eq_of_monic_of_ne_zero hcore_lc_ne hlp_monic
  have hslp_lc :
      Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T) =
        Hex.DensePoly.leadingCoeff core := by
    unfold scaledLiftedFactorProduct
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero
      (Hex.DensePoly.leadingCoeff core) lp hcore_lc_ne,
      show Hex.DensePoly.leadingCoeff lp = (1 : Int) from hlp_monic]
    ring
  have hslp_lc_pos :
      0 < Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T) := by
    rw [hslp_lc]; exact hcore_lc_pos
  have hslp_lc_bound :
      (Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T)).natAbs ≤
        B' := by
    rwa [hslp_lc]
  have hcl_size :
      (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
          (d.p ^ d.k)).size =
        (scaledLiftedFactorProduct core d T).size :=
    size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound
      hslp_lc_pos hslp_lc_bound hprecision
  have hcl_size_pos :
      0 < (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
          (d.p ^ d.k)).size := by
    rw [hcl_size, hslp_size]; exact hlp_size_pos
  have hcl_ne :
      Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T) (d.p ^ d.k)
        ≠ 0 := by
    intro h
    have h0 :
        (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)).size = 0 := by
      rw [h]; rfl
    omega
  have hpp_size :
      (Hex.ZPoly.primitivePart
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k))).size =
        (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)).size :=
    size_primitivePart_eq_of_ne_zero hcl_ne
  have hsc_size :
      (scaledRecombinationCandidate core d T).size = lp.size := by
    show (Hex.normalizeFactorSign
        (Hex.ZPoly.primitivePart
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)))).size = lp.size
    rw [size_normalizeFactorSign_eq, hpp_size, hcl_size, hslp_size]
  have hsc_size_pos : 0 < (scaledRecombinationCandidate core d T).size := by
    rw [hsc_size]; exact hlp_size_pos
  have hsc_natDeg :
      (HexPolyZMathlib.toPolynomial
          (scaledRecombinationCandidate core d T)).natDegree =
        (scaledRecombinationCandidate core d T).size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hsc_size_pos]
  have hlp_natDeg :
      (HexPolyZMathlib.toPolynomial lp).natDegree = lp.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hlp_size_pos]
  rw [hsc_natDeg, hsc_size, ← hlp_natDeg, hlp_def, toPolynomial_liftedFactorProduct]
  apply Polynomial.natDegree_prod_of_monic
  intro i _
  show (HexPolyZMathlib.toPolynomial (liftedFactor d i)).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact hd_liftedFactor_monic i

/-- The Mathlib-transported `natDegree` of the scaled recombination candidate
over a lifted-factor subset equals the sum of the Mathlib-transported
`natDegree`s of the selected lifted factors, given primitive + positive-leading
`core` and the Mignotte precision bound.

The candidate goes through `centeredLiftPoly ∘ primitivePart ∘ normalizeFactorSign`
on top of `scaledLiftedFactorProduct = scale (lc core) (liftedFactorProduct)`.
Each step preserves stored size: scaling by the nonzero leading coefficient,
centred-lift under the positive-leading bound, primitive part on a nonzero
input, and sign normalisation. Combined with `lp.size = ∑ + 1` for the monic
lifted-factor product, the candidate's natDegree decomposes as a sum.

Thin wrapper over
`natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum_of_bound` that
instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and discharges
`hcore_lc_le` via `defaultFactorCoeffBound_valid core hcore_ne core
hcore_dvd_self` at index `core.size - 1`, converted to the leading
coefficient via `leadingCoeff_eq_coeff_last`.

Companion scaled variant of `natDegree_toPolynomial_recombinationCandidate_eq_sum`.
Consumed by the scaled cover-at-min chain for the primitive recursive
recombination coverage proof (#4647 / #4737). -/
theorem natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T)).natDegree =
      ∑ i ∈ T,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_ne hcore_lc_pos hd_liftedFactor_monic hcore_lc_le hprecision T

/-- Abstract-bound variant of
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`,
`hcore_lc_le : (lc core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

The unscaled `_hrec_scaled` step from the existing proof is dropped
entirely — its result was never consumed — and the centred-lift
recovery call is routed through
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`
in place of the core-shape recovery. Both changes make this sibling
independent of `scaledRecombinationCandidate_eq_factor_of_recovery`
and hence of the scaled recovery-candidate `_of_bound` chain (#4882).

Note: this sibling needs `hcore_lc_le` in addition to `hvalid`
because the size-preservation step
`size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound` consumes a
leading-coefficient bound on `scaledLiftedFactorProduct core d S`,
whose leading coefficient is `lc core`. Without a `B'`-shape bound
on `lc core` itself, the abstract-precision hypothesis cannot
discharge that lemma's separation requirement. The existing
core-shape wrapper supplies this from
`defaultFactorCoeffBound_valid core hcore_ne core hcore_dvd_self`.
-/
theorem natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (_hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (_hdvd : factor ∣ core)
    (_hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (_hfactor_prim : Hex.ZPoly.content factor = 1)
    (_hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * B' < d.p ^ d.k) :
    (HexPolyZMathlib.toPolynomial factor).natDegree =
      ∑ i ∈ S,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  -- Centred-lift form of the recovery, abstract-bound variant.
  have hcenter :
      Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k) =
        factor :=
    centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
      B' hvalid hrep hprecision
  -- Monic lifted-factor product.
  set lp := liftedFactorProduct d S with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d S (fun i _ => hd_liftedFactor_monic i)
  have hlp_size_pos : 0 < lp.size := zpoly_size_pos_of_monic hlp_monic
  -- Scaled product has lc = lc core (> 0) and the same size as `lp`.
  have hcore_lc_ne : Hex.DensePoly.leadingCoeff core ≠ (0 : Int) :=
    ne_of_gt hcore_lc_pos
  have hslp_size : (scaledLiftedFactorProduct core d S).size = lp.size := by
    unfold scaledLiftedFactorProduct
    exact size_scale_eq_of_monic_of_ne_zero hcore_lc_ne hlp_monic
  have hslp_lc :
      Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d S) =
        Hex.DensePoly.leadingCoeff core := by
    unfold scaledLiftedFactorProduct
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero
      (Hex.DensePoly.leadingCoeff core) lp hcore_lc_ne,
      show Hex.DensePoly.leadingCoeff lp = (1 : Int) from hlp_monic]
    ring
  have hslp_lc_pos :
      0 < Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d S) := by
    rw [hslp_lc]; exact hcore_lc_pos
  have hslp_lc_bound :
      (Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d S)).natAbs ≤
        B' := by
    rwa [hslp_lc]
  -- Centred lift preserves the size of the scaled product.
  have hcl_size :
      (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k)).size =
        (scaledLiftedFactorProduct core d S).size :=
    size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound
      hslp_lc_pos hslp_lc_bound hprecision
  -- Combine the size identities to get `factor.size = lp.size`.
  have hfactor_size : factor.size = lp.size := by
    rw [← hcenter, hcl_size, hslp_size]
  -- Convert to `natDegree` via `HexPolyMathlib.natDegree_toPolynomial`.
  have hfactor_natDeg :
      (HexPolyZMathlib.toPolynomial factor).natDegree = factor.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt (hfactor_size ▸ hlp_size_pos)]
  have hlp_natDeg :
      (HexPolyZMathlib.toPolynomial lp).natDegree = lp.size - 1 := by
    rw [HexPolyMathlib.natDegree_toPolynomial]
    simp [Hex.DensePoly.degree?, Nat.ne_of_gt hlp_size_pos]
  rw [hfactor_natDeg, hfactor_size, ← hlp_natDeg, hlp_def, toPolynomial_liftedFactorProduct]
  -- Sum decomposition over monic lifted factors.
  apply Polynomial.natDegree_prod_of_monic
  intro i _
  show (HexPolyZMathlib.toPolynomial (liftedFactor d i)).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact hd_liftedFactor_monic i

/--
Primitive + positive-leading-core variant of
`natDegree_toPolynomial_eq_sum_of_represents` (#4646).

For primitive non-monic `core`, the represented factor's natDegree equals the
sum of natDegrees of the selected lifted factors. The proof routes through the
scaled recovery identity `scaledRecombinationCandidate core d S = factor`
(#4652) and the size identities
`factor.size = (scaledLiftedFactorProduct core d S).size =
 (liftedFactorProduct d S).size`. Scaling by `C (lc core)` and the centred lift
both preserve stored size under the Mignotte half-window bound on `lc core`,
so the sum decomposition `natDegree_prod_of_monic` over `liftedFactorProduct`
applies unchanged. The `hcore_primitive` and `hfactor_irr` hypotheses are
threaded for API uniformity with the monic variant but are not used by the
proof; the natDegree extraction depends only on the leading-coefficient bound
and the primitive/sign-normalised facts on `factor` consumed by #4652.

This is a thin wrapper over
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hdvd` and the
leading-coefficient bound via
`defaultFactorCoeffBound_valid core hcore_ne core hcore_dvd_self`.
-/
theorem natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core
    {core factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hdvd : factor ∣ core)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_prim : Hex.ZPoly.content factor = 1)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor)
    (hrep : RepresentsIntegerFactorAtLift core d factor S) :
    (HexPolyZMathlib.toPolynomial factor).natDegree =
      ∑ i ∈ S,
        (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
    hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
    hdvd hfactor_irr hfactor_prim hfactor_norm hrep hprecision

/-- Converse to `toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord`: if the
transported polynomial is non-zero and a non-unit, then the executable
`shouldRecordPolynomialFactor` check passes.  Used to package executable
witnesses for one recombination split from Mathlib-side irreducibility. -/
theorem shouldRecordPolynomialFactor_of_toPolynomial_ne_zero_not_isUnit
    {f : Hex.ZPoly}
    (hne_zero : HexPolyZMathlib.toPolynomial f ≠ 0)
    (hnonunit : ¬ IsUnit (HexPolyZMathlib.toPolynomial f)) :
    Hex.shouldRecordPolynomialFactor f = true := by
  have hf_ne_zero : f ≠ 0 := fun hf => hne_zero (by
    rw [hf]; exact HexPolyZMathlib.toPolynomial_zero)
  have hf_ne_one : f ≠ 1 := fun hf => hnonunit
    ((HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mp (by rw [hf]; left; rfl))
  have hf_ne_neg_one : f ≠ Hex.DensePoly.C (-1) := fun hf => hnonunit
    ((HexPolyZMathlib.isUnit_iff_toPolynomial_isUnit f).mp (by rw [hf]; right; rfl))
  unfold Hex.shouldRecordPolynomialFactor
  simp [hf_ne_zero, hf_ne_one, hf_ne_neg_one]

/-- An irreducible (after transport) `Hex.ZPoly` value passes the executable
`shouldRecordPolynomialFactor` check.  Combines the previous lemma with
`Irreducible`'s structural projections. -/
theorem shouldRecordPolynomialFactor_of_irreducible_toPolynomial
    {f : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial f)) :
    Hex.shouldRecordPolynomialFactor f = true :=
  shouldRecordPolynomialFactor_of_toPolynomial_ne_zero_not_isUnit
    hirr.ne_zero hirr.not_isUnit

/-- One-step `shouldRecord` discharge for a recombination split: when the
candidate equals an irreducible integer factor, the executable check passes. -/
theorem shouldRecord_recombinationCandidate_of_eq_factor
    {factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    Hex.shouldRecordPolynomialFactor (recombinationCandidate d S) = true := by
  rw [heq]
  exact shouldRecordPolynomialFactor_of_irreducible_toPolynomial hirr

/-- One-step `exactQuotient?` discharge for a recombination split: when the
candidate equals an integer divisor of `core` and is monic of positive degree,
the executable exact-division check returns `some` of the proof-side cofactor. -/
theorem exactQuotient?_recombinationCandidate_eq_some_of_eq_factor
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (heq : recombinationCandidate d S = factor)
    (hmonic : Hex.DensePoly.Monic factor)
    (hpos : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ core) :
    ∃ quotient,
      Hex.exactQuotient? core (recombinationCandidate d S) = some quotient ∧
        quotient * recombinationCandidate d S = core := by
  obtain ⟨q, hq⟩ := hdvd
  -- hq : core = factor * q
  have hmul : q * factor = core := by
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hq.symm
  refine ⟨q, ?_, ?_⟩
  · rw [heq]
    exact Hex.exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree hmonic hpos hmul
  · rw [heq]; exact hmul

/-- Scaled-candidate counterpart of `shouldRecord_recombinationCandidate_of_eq_factor`.
When the scaled candidate equals an irreducible integer factor, the executable
record check passes. -/
theorem shouldRecord_scaledRecombinationCandidate_of_eq_factor
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (heq : scaledRecombinationCandidate core d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    Hex.shouldRecordPolynomialFactor (scaledRecombinationCandidate core d S) =
      true := by
  rw [heq]
  exact shouldRecordPolynomialFactor_of_irreducible_toPolynomial hirr

/-- Scaled-candidate counterpart of `exactQuotient?_recombinationCandidate_eq_some_of_eq_factor`.
When the scaled candidate equals a monic integer divisor of `target` of
positive degree, the executable exact-division check on `target` returns
`some` of the proof-side cofactor.

Used by the primitive recursive coverage proof in #4647 against the new
`Hex.scaledRecombinationSearchModAux` executable, paired with the recovery
identity `scaledRecombinationCandidate_eq_factor_of_recovery` from #4652. -/
theorem exactQuotient?_scaledRecombinationCandidate_eq_some_of_eq_factor
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (heq : scaledRecombinationCandidate core d S = factor)
    (hmonic : Hex.DensePoly.Monic factor)
    (hpos : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ target) :
    ∃ quotient,
      Hex.exactQuotient? target (scaledRecombinationCandidate core d S) =
        some quotient ∧
        quotient * scaledRecombinationCandidate core d S = target := by
  obtain ⟨q, hq⟩ := hdvd
  -- hq : target = factor * q
  have hmul : q * factor = target := by
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hq.symm
  refine ⟨q, ?_, ?_⟩
  · rw [heq]
    exact Hex.exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree hmonic hpos hmul
  · rw [heq]; exact hmul

/-- Non-monic counterpart of
`exactQuotient?_scaledRecombinationCandidate_eq_some_of_eq_factor`.
When the scaled candidate equals an integer divisor of `target` with positive
leading coefficient and positive degree, the executable exact-division check
on `target` returns `some` of the proof-side cofactor.

Drops `Monic factor` in favour of `0 < lc factor`, routing through
`exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq` instead of the
monic-only `exactQuotient?_eq_some_of_mul_eq_monic_of_pos_degree`.  Consumed
by the primitive recursive coverage proof in #4647, paired with the recovery
identity `scaledRecombinationCandidate_eq_factor_of_recovery` from #4652 and
the primitive + positive-leading bound from
`representsIntegerFactorAtLift_primitive` (#4644). -/
theorem exactQuotient?_scaledRecombinationCandidate_eq_some_of_eq_factor_of_primitive_pos_lc
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (heq : scaledRecombinationCandidate core d S = factor)
    (hpos_lc : 0 < Hex.DensePoly.leadingCoeff factor)
    (hpos : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ target) :
    ∃ quotient,
      Hex.exactQuotient? target (scaledRecombinationCandidate core d S) =
        some quotient ∧
        quotient * scaledRecombinationCandidate core d S = target := by
  obtain ⟨q, hq⟩ := hdvd
  -- hq : target = factor * q
  have hmul : q * factor = target := by
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hq.symm
  refine ⟨q, ?_, ?_⟩
  · rw [heq]
    exact Hex.exactQuotient?_eq_some_of_pos_lc_pos_degree_mul_eq hpos_lc hpos hmul
  · rw [heq]; exact hmul

/--
Executable recombination-search success for one lifted subset.

Once a proof-side lifted subset is known to contain the first remaining local
factor, its ordered `(selected, rest)` partition is one of the splits traversed
by `recombinationSearchMod`.  If the subset's executable candidate is an
irreducible integer divisor of the current target and the recursive search on
the quotient/rest problem succeeds, the surface recombination search succeeds.
-/
theorem recombinationSearchMod_isSome_of_liftedSubset_candidate_eq_factor
    {core factor quotient : Hex.ZPoly} {d : Hex.LiftData}
    {S : LiftedFactorSubset d}
    (hcore_ne_one : core ≠ 1)
    (hsize_pos : 0 < d.liftedFactors.size)
    (hfirst : (⟨0, hsize_pos⟩ : LiftedFactorIndex d) ∈ S)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hsearch_rest :
      (Hex.recombinationSearchModAux quotient (d.p ^ d.k)
        (liftedSubsetRejectedList d S) d.liftedFactors.toList.length).isSome = true)
    (hquot :
      Hex.exactQuotient? core (recombinationCandidate d S) = some quotient) :
    (Hex.recombinationSearchMod core (d.p ^ d.k)
        d.liftedFactors.toList).isSome = true := by
  refine
    Hex.recombinationSearchMod_isSome_of_step
      (target := core)
      (candidate := factor)
      (quotient := quotient)
      (modulus := d.p ^ d.k)
      (localFactors := d.liftedFactors.toList)
      (selected := liftedSubsetSelectedList d S)
      (rest := liftedSubsetRejectedList d S)
      hcore_ne_one
      (liftedSubsetSplit_mem_subsetSplitsWithFirst d S hsize_pos hfirst)
      ?_
      (by
        simpa [heq] using
          shouldRecord_recombinationCandidate_of_eq_factor heq hirr)
      ?_
      hsearch_rest
  · simpa [recombinationCandidate] using heq.symm
  · simpa [heq] using hquot

/--
Matched-rest variant of
`recombinationSearchMod_isSome_of_liftedSubset_candidate_eq_factor`.

At a recursive recombination state, `localFactors` is no longer the full
lifted-factor list; it is the order-preserving list of the remaining proof-side
indices `J`.  If a represented subset `S ⊆ J` contains the current minimum
remaining index, the matching predicate identifies its executable split and
the ordinary one-step search lemma applies.
-/
theorem recombinationSearchModAux_isSome_of_liftedSubset_candidate_eq_factor_of_matches
    {target factor quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    (htarget_ne_one : target ≠ 1)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hSJ : S ⊆ J)
    (hne : J.Nonempty)
    (hmin : J.min' hne ∈ S)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hsearch_rest :
      (Hex.recombinationSearchModAux quotient (d.p ^ d.k)
        (liftedSubsetSelectedList d (J \ S)) fuel).isSome = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d S) = some quotient) :
    (Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors (fuel + 1)).isSome =
      true := by
  refine
    Hex.recombinationSearchModAux_isSome_of_step
      (target := target)
      (candidate := factor)
      (quotient := quotient)
      (modulus := d.p ^ d.k)
      (localFactors := localFactors)
      (selected := liftedSubsetSelectedList d S)
      (rest := liftedSubsetSelectedList d (J \ S))
      (fuel := fuel)
      htarget_ne_one
      (liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
        hmatches hSJ hne hmin)
      ?_
      (by
        simpa [heq] using
          shouldRecord_recombinationCandidate_of_eq_factor heq hirr)
      ?_
      hsearch_rest
  · simpa [recombinationCandidate] using heq.symm
  · simpa [heq] using hquot

/--
Exact-output matched-rest variant of
`recombinationSearchModAux_isSome_of_liftedSubset_candidate_eq_factor_of_matches`.

When the split selected from a matched remaining-index set is the first
successful executable split, the returned factor list has the represented
factor at its head. This is the local first-success lemma needed by the
recursive coverage proof before it reasons about earlier successful splits.
-/
theorem recombinationSearchModAux_first_success_witness_of_liftedSubset_candidate_eq_factor_of_matches
    {target factor quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat} {restFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hSJ : S ⊆ J)
    (hne : J.Nonempty)
    (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) ::
            suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          Hex.normalizeFactorSign <|
            Hex.ZPoly.primitivePart <|
              Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
                (d.p ^ d.k)
        if Hex.shouldRecordPolynomialFactor candidate' then
          match Hex.exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match Hex.recombinationSearchModAux quotient' (d.p ^ d.k) split.2 fuel with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hsearch_rest :
      Hex.recombinationSearchModAux quotient (d.p ^ d.k)
        (liftedSubsetSelectedList d (J \ S)) fuel = some restFactors)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d S) = some quotient) :
    ∃ result,
      Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors (fuel + 1) =
          some result ∧
        ∃ emitted ∈ result,
          Associated (HexPolyZMathlib.toPolynomial emitted)
            (HexPolyZMathlib.toPolynomial factor) := by
  have _hsplit_mem :
      (liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S)) ∈
        Hex.subsetSplitsWithFirst localFactors :=
    liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
      hmatches hSJ hne hmin
  refine ⟨factor :: restFactors, ?_, ?_⟩
  · exact
      Hex.recombinationSearchModAux_eq_some_of_step_of_prefix_none
        (target := target)
        (candidate := factor)
        (quotient := quotient)
        (modulus := d.p ^ d.k)
        (localFactors := localFactors)
        (selected := liftedSubsetSelectedList d S)
        (rest := liftedSubsetSelectedList d (J \ S))
        (restFactors := restFactors)
        (pre := pre)
        (suffix := suffix)
        (fuel := fuel)
        htarget_ne_one hsplits hprefix
        (by simpa [recombinationCandidate] using heq.symm)
        (by
          simpa [heq] using
            shouldRecord_recombinationCandidate_of_eq_factor heq hirr)
        (by simpa [heq] using hquot)
        hsearch_rest
  · refine ⟨factor, by simp, ?_⟩
    exact Associated.refl (HexPolyZMathlib.toPolynomial factor)

/--
Variant of
`recombinationSearchMod_isSome_of_liftedSubset_candidate_eq_factor` that
discharges the executable quotient check from ordinary divisibility plus the
monic positive-degree hypotheses required by `exactQuotient?`.
-/
theorem recombinationSearchMod_isSome_of_liftedSubset_factor_dvd
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne_one : core ≠ 1)
    (hsize_pos : 0 < d.liftedFactors.size)
    (hfirst : (⟨0, hsize_pos⟩ : LiftedFactorIndex d) ∈ S)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hmonic : Hex.DensePoly.Monic factor)
    (hdegree : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ core)
    (hsearch_rest :
      ∀ quotient,
        Hex.exactQuotient? core (recombinationCandidate d S) = some quotient →
        (Hex.recombinationSearchModAux quotient (d.p ^ d.k)
          (liftedSubsetRejectedList d S) d.liftedFactors.toList.length).isSome = true) :
    (Hex.recombinationSearchMod core (d.p ^ d.k)
        d.liftedFactors.toList).isSome = true := by
  rcases
    exactQuotient?_recombinationCandidate_eq_some_of_eq_factor
      (core := core) (factor := factor) (d := d) (S := S)
      heq hmonic hdegree hdvd with
    ⟨quotient, hquot, _hmul⟩
  exact
    recombinationSearchMod_isSome_of_liftedSubset_candidate_eq_factor
      (core := core) (factor := factor) (quotient := quotient) (d := d)
      (S := S) hcore_ne_one hsize_pos hfirst heq hirr
      (hsearch_rest quotient hquot) hquot

/--
Matched-rest variant of
`recombinationSearchMod_isSome_of_liftedSubset_factor_dvd`: discharges the
executable quotient check from divisibility plus monic positive-degree
hypotheses at the recursive recombination state, where the running
`localFactors` list matches an arbitrary remaining-index set `J` and the
candidate subset `S ⊆ J` contains the current minimum remaining index.
-/
theorem recombinationSearchModAux_isSome_of_liftedSubset_factor_dvd_of_matches
    {target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    (htarget_ne_one : target ≠ 1)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hSJ : S ⊆ J)
    (hne : J.Nonempty)
    (hmin : J.min' hne ∈ S)
    (heq : recombinationCandidate d S = factor)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hmonic : Hex.DensePoly.Monic factor)
    (hdegree : 0 < factor.degree?.getD 0)
    (hdvd : factor ∣ target)
    (hsearch_rest :
      ∀ quotient,
        Hex.exactQuotient? target (recombinationCandidate d S) = some quotient →
        (Hex.recombinationSearchModAux quotient (d.p ^ d.k)
          (liftedSubsetSelectedList d (J \ S)) fuel).isSome = true) :
    (Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors
        (fuel + 1)).isSome = true := by
  rcases
    exactQuotient?_recombinationCandidate_eq_some_of_eq_factor
      (core := target) (factor := factor) (d := d) (S := S)
      heq hmonic hdegree hdvd with
    ⟨quotient, hquot, _hmul⟩
  exact
    recombinationSearchModAux_isSome_of_liftedSubset_candidate_eq_factor_of_matches
      (target := target) (factor := factor) (quotient := quotient) (d := d)
      (J := J) (S := S) (localFactors := localFactors) (fuel := fuel)
      htarget_ne_one hmatches hSJ hne hmin heq hirr
      (hsearch_rest quotient hquot) hquot

/--
Proof-facing package for a first successful recombination split.

The executable theorem in `HexBerlekampZassenhaus.Basic` returns an exact
`some (candidate :: restFactors)` value.  This wrapper exposes the pieces that
Mathlib-side coverage proofs need without requiring downstream statements to
mention the internals of `firstSome`: the returned list, head membership,
`shouldRecord`, exact quotient witness, and recursive-rest success.
-/
theorem recombinationSearchMod_first_success_witness_of_step_of_prefix_none
    {target candidate quotient : Hex.ZPoly} {modulus : Nat}
    {localFactors selected rest restFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (htarget_ne_one : target ≠ 1)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors = pre ++ (selected, rest) :: suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          Hex.normalizeFactorSign <|
            Hex.ZPoly.primitivePart <|
              Hex.centeredLiftPoly (Array.polyProduct split.1.toArray) modulus
        if Hex.shouldRecordPolynomialFactor candidate' then
          match Hex.exactQuotient? target candidate' with
          | none => none
          | some quotient' =>
              match Hex.recombinationSearchModAux quotient' modulus split.2
                  localFactors.length with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hcandidate_def :
      candidate = Hex.normalizeFactorSign
        (Hex.ZPoly.primitivePart
          (Hex.centeredLiftPoly (Array.polyProduct selected.toArray) modulus)))
    (hrecord : Hex.shouldRecordPolynomialFactor candidate = true)
    (hquot : Hex.exactQuotient? target candidate = some quotient)
    (hsearch_rest :
      Hex.recombinationSearchModAux quotient modulus rest localFactors.length =
        some restFactors) :
    ∃ factors,
      Hex.recombinationSearchMod target modulus localFactors = some factors ∧
        candidate ∈ factors ∧
        Hex.shouldRecordPolynomialFactor candidate = true ∧
        (∃ quotient,
          Hex.exactQuotient? target candidate = some quotient ∧
            Hex.recombinationSearchModAux quotient modulus rest
                localFactors.length = some restFactors) := by
  refine ⟨candidate :: restFactors, ?_, ?_, hrecord, ?_⟩
  · exact
      Hex.recombinationSearchMod_eq_some_of_step_of_prefix_none
        htarget_ne_one hsplits hprefix hcandidate_def hrecord hquot
        hsearch_rest
  · simp
  · exact ⟨quotient, hquot, hsearch_rest⟩

/--
Membership lemma carrying a successful fixed-lift recombination search into the
public exhaustive-core wrapper.  The non-empty branch is discharged by the
factor membership witness, so downstream coverage proofs can use an exact
`recombinationSearchMod` success without unfolding `exhaustiveCoreFactorsWithBound`.

The monic core hypothesis is required because `exhaustiveCoreFactorsWithBound`
runs the *scaled* recombination at `coreLc = Hex.DensePoly.leadingCoeff core`,
while the supplied witness comes from the *unscaled* search; under
`hcore_monic` the two coincide via the
`recombineScaledExhaustive_eq_recombineExhaustive_of_one` collapse.  A
companion `_of_scaledRecombinationSearchMod_some` wrapper that drops the
monic hypothesis is a follow-up sub-issue.
-/
theorem exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {factors : List Hex.ZPoly}
    (hB : B ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd :
      d = Hex.ZPoly.toMonicLiftData core B primeData)
    (hsearch :
      Hex.recombinationSearchMod core (d.p ^ d.k)
        d.liftedFactors.toList = some factors)
    (hmem : factor ∈ factors) :
    factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList := by
  subst d
  have hlc : Hex.DensePoly.leadingCoeff core = 1 := hcore_monic
  have hrecombine :
      Hex.recombineExhaustive core
          (Hex.ZPoly.toMonicLiftData core B primeData) =
        factors.toArray :=
    Hex.recombineExhaustive_eq_of_recombinationSearchMod_some hsearch
  have hscaled :
      Hex.recombineScaledExhaustive (Hex.DensePoly.leadingCoeff core) core
          (Hex.ZPoly.toMonicLiftData core B primeData) =
        factors.toArray := by
    rw [hlc, Hex.recombineScaledExhaustive_eq_recombineExhaustive_of_one]
    exact hrecombine
  have hnot_empty : factors.toArray.isEmpty = false := by
    cases factors with
    | nil => simp at hmem
    | cons head tail => simp
  simp [Hex.exhaustiveCoreFactorsWithBound, hB, hscaled, hnot_empty, hmem]

/--
Scaled-candidate counterpart of
`exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some`.

`Hex.exhaustiveCoreFactorsWithBound` calls the scaled recombination
`recombineScaledExhaustive` at `coreLc = Hex.DensePoly.leadingCoeff core`, so
coverage proofs that reach a successful scaled search return a membership
statement in the public wrapper directly through this lemma — no
`Monic core` hypothesis and no unfolding of `exhaustiveCoreFactorsWithBound`
needed at the call site.
-/
theorem exhaustiveCoreFactorsWithBound_mem_of_scaledRecombinationSearchMod_some
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {factors : List Hex.ZPoly}
    (hB : B ≠ 0)
    (hd : d = Hex.ZPoly.toMonicLiftData core B primeData)
    (hsearch :
      Hex.scaledRecombinationSearchMod (Hex.DensePoly.leadingCoeff core)
          core (d.p ^ d.k) d.liftedFactors.toList =
        some factors)
    (hmem : factor ∈ factors) :
    factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList := by
  subst d
  have hrecombine :
      Hex.recombineScaledExhaustive (Hex.DensePoly.leadingCoeff core) core
          (Hex.ZPoly.toMonicLiftData core B primeData) =
        factors.toArray :=
    Hex.recombineScaledExhaustive_eq_of_scaledRecombinationSearchMod_some hsearch
  have hnot_empty : factors.toArray.isEmpty = false := by
    cases factors with
    | nil => simp at hmem
    | cons head tail => simp
  simp [Hex.exhaustiveCoreFactorsWithBound, hB, hrecombine, hnot_empty, hmem]

/--
Public-wrapper membership lemma for a first successful fixed-lift split.

This composes the proof-facing first-success witness with
`exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some`, so later
coverage proofs can discharge the executable-wrapper step without separately
unpacking `recombinationSearchMod`.
-/
theorem exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_first_success
    {core factor quotient : Hex.ZPoly} {B : Nat}
    {primeData : Hex.PrimeChoiceData} {d : Hex.LiftData}
    {selected rest restFactors : List Hex.ZPoly}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hB : B ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd : d = Hex.ZPoly.toMonicLiftData core B primeData)
    (hcore_ne_one : core ≠ 1)
    (hsplits :
      Hex.subsetSplitsWithFirst d.liftedFactors.toList =
        pre ++ (selected, rest) :: suffix)
    (hprefix :
      ∀ split ∈ pre,
        (let candidate' :=
          Hex.normalizeFactorSign <|
            Hex.ZPoly.primitivePart <|
              Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
                (d.p ^ d.k)
        if Hex.shouldRecordPolynomialFactor candidate' then
          match Hex.exactQuotient? core candidate' with
          | none => none
          | some quotient' =>
              match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                  split.2 d.liftedFactors.toList.length with
              | none => none
              | some r => some (candidate' :: r)
        else none) = none)
    (hfactor_def :
      factor =
        Hex.normalizeFactorSign
          (Hex.ZPoly.primitivePart
            (Hex.centeredLiftPoly (Array.polyProduct selected.toArray)
              (d.p ^ d.k))))
    (hrecord : Hex.shouldRecordPolynomialFactor factor = true)
    (hquot : Hex.exactQuotient? core factor = some quotient)
    (hsearch_rest :
      Hex.recombinationSearchModAux quotient (d.p ^ d.k) rest
          d.liftedFactors.toList.length =
        some restFactors) :
    factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList := by
  rcases
    recombinationSearchMod_first_success_witness_of_step_of_prefix_none
      (target := core)
      (candidate := factor)
      (quotient := quotient)
      (modulus := d.p ^ d.k)
      (localFactors := d.liftedFactors.toList)
      (selected := selected)
      (rest := rest)
      (restFactors := restFactors)
      (pre := pre)
      (suffix := suffix)
      hcore_ne_one hsplits hprefix hfactor_def hrecord hquot hsearch_rest with
    ⟨factors, hsearch, hmem, _hrecord, _hrest⟩
  exact
    exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some
      (core := core) (factor := factor) (B := B) (primeData := primeData)
      (d := d) (factors := factors) hB hcore_monic hd hsearch hmem

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

/--
Forward lemma carrying a successful executable recombination candidate quotient
to a proof-side irreducible divisor of `target` together with its representing
subset under a `LiftedFactorSubsetPartition`.

Given a `LiftedFactorSubsetPartition core d J target` and an arbitrary lifted
subset `T`, the hypotheses

* `Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true`, and
* `Hex.exactQuotient? target (recombinationCandidate d T) = some quotient`

are the two executable facts that any "non-`none` body" of one step in the
recombination search produces.  The lemma packages from these:

* the explicit product witness `quotient * recombinationCandidate d T = target`
  (via `Hex.exactQuotient?_product`),
* the proof-side divisibility `recombinationCandidate d T ∣ target`, and
* an irreducible factor `g` of the candidate (via UFD existence in
  `Polynomial ℤ`) that, via the partition's inherited
  `HenselSubsetCorrespondenceRest.exists_subset`, is itself an irreducible
  divisor of `target` with representing subset `S ⊆ J`.

Used by the prefix-none assembler in the recursive coverage proof for
`Hex.recombinationSearchModAux` (#4367/#4301) to compare an earlier executable
split's selected subset against the partition's representing subsets using
`pairwise_disjoint` / `unique_up_to_associated`.
-/
theorem exists_representingSubset_dvd_recombinationCandidate_of_exactQuotient
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    quotient * recombinationCandidate d T = target ∧
      recombinationCandidate d T ∣ target ∧
        ∃ (g : Hex.ZPoly) (S : LiftedFactorSubset d),
          Irreducible (HexPolyZMathlib.toPolynomial g) ∧
          g ∣ target ∧
          g ∣ recombinationCandidate d T ∧
          S ⊆ J ∧
          RepresentsIntegerFactorAtLift core d g S := by
  -- Quotient equation and divisibility from `exactQuotient?_product`.
  have hmul : quotient * recombinationCandidate d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  -- Candidate is nonzero and not a unit after transport to `Polynomial ℤ`.
  obtain ⟨hcand_poly_ne_zero, hcand_poly_nonunit⟩ :=
    toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord
  -- UFD existence: extract an irreducible factor of the candidate in
  -- `Polynomial ℤ`.
  obtain ⟨gPoly, hg_irr, hg_dvd_cand_poly⟩ :=
    WfDvdMonoid.exists_irreducible_factor hcand_poly_nonunit hcand_poly_ne_zero
  -- Carry the irreducible factor back to a `Hex.ZPoly` divisor of the
  -- candidate.
  let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
  have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
    HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    rw [hg_toPolynomial]
    exact hr
  have hg_dvd_target : g ∣ target := zpoly_dvd_trans hg_dvd_cand hcand_dvd_target
  have hg_irr_toPoly : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPolynomial]; exact hg_irr
  -- Apply the partition's inherited `exists_subset` to obtain the representing
  -- subset for `g`.
  obtain ⟨S, hSJ, hSrep⟩ :=
    hpartition.exists_subset hg_irr_toPoly hg_dvd_target
  exact ⟨hmul, hcand_dvd_target, g, S, hg_irr_toPoly, hg_dvd_target, hg_dvd_cand,
    hSJ, hSrep⟩

/-! ### Monicness of the executable recombination candidate -/

/--
Under monic lifted local factors and modulus `2 ≤ d.p ^ d.k`, the executable
recombination candidate `recombinationCandidate d T` is monic for every lifted
subset `T`.

The proof mirrors the chain inside
`natDegree_toPolynomial_recombinationCandidate_eq_sum`: the lifted-factor product
is monic by `liftedFactorProduct_monic`, the centered lift preserves monicness
under the modulus bound (`monic_centeredLiftPoly_of_monic`), and a monic
polynomial is fixed by `primitivePart` and `normalizeFactorSign` (via
`monic_primitive_sign_normalized_of_monic`), so the full normalisation chain
collapses to the centred lift, which is monic.
-/
theorem recombinationCandidate_monic
    {d : Hex.LiftData}
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    Hex.DensePoly.Monic (recombinationCandidate d T) := by
  set lp := liftedFactorProduct d T with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  have hcl_monic :
      Hex.DensePoly.Monic (Hex.centeredLiftPoly lp (d.p ^ d.k)) :=
    monic_centeredLiftPoly_of_monic hlp_monic hd_modulus
  have hnorm : Hex.normalizeFactorSign (Hex.centeredLiftPoly lp (d.p ^ d.k)) =
      Hex.centeredLiftPoly lp (d.p ^ d.k) :=
    zpoly_normalize_factor_sign_of_monic hcl_monic
  have hprim :
      Hex.ZPoly.primitivePart (Hex.centeredLiftPoly lp (d.p ^ d.k)) =
        Hex.centeredLiftPoly lp (d.p ^ d.k) :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive _
      (zpoly_primitive_of_monic hcl_monic)
  have hrec_eq :
      recombinationCandidate d T = Hex.centeredLiftPoly lp (d.p ^ d.k) := by
    unfold recombinationCandidate
    rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct, ← hlp_def,
      hprim, hnorm]
  rw [hrec_eq]
  exact hcl_monic

/-- The `Polynomial ℤ` image of a monic-conditions recombination candidate is
monic. Caller-side packaging of `recombinationCandidate_monic` through
`HexPolyMathlib.leadingCoeff_toPolynomial`. -/
theorem toPolynomial_recombinationCandidate_monic
    {d : Hex.LiftData}
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (T : LiftedFactorSubset d) :
    (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic := by
  show (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).leadingCoeff = 1
  rw [HexPolyMathlib.leadingCoeff_toPolynomial]
  exact recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T

/-- The `Polynomial ℤ` image of a recombination candidate inherits squarefreeness
from a square-free `target`, given `candidate ∣ target` (supplied by the
executable quotient witness `hquot`).

The reverse-coverage proof for the main candidate divisibility theorem
(see `representedFactor_dvd_recombinationCandidate_of_subset`, #4457) needs
`toPolynomial candidate` square-free to factor it into a Multiset of pairwise
non-associated irreducibles. -/
theorem toPolynomial_recombinationCandidate_squarefree
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    Squarefree (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) := by
  have hmul : quotient * recombinationCandidate d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  exact Squarefree.squarefree_of_dvd
    (HexPolyMathlib.toPolynomial_dvd hcand_dvd_target) hpartition.target_squarefree

/-- Scaled-candidate counterpart of `toPolynomial_recombinationCandidate_squarefree`:
inherits squarefreeness from a squarefree `target` via the exact-quotient witness.
Consumed by the scaled `mem_T_iff_*` chain for the primitive recursive
recombination coverage proof (#4647 / #4737). -/
theorem toPolynomial_scaledRecombinationCandidate_squarefree
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient) :
    Squarefree (HexPolyZMathlib.toPolynomial
      (scaledRecombinationCandidate core d T)) := by
  have hmul : quotient * scaledRecombinationCandidate core d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : scaledRecombinationCandidate core d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  exact Squarefree.squarefree_of_dvd
    (HexPolyMathlib.toPolynomial_dvd hcand_dvd_target) hpartition.target_squarefree

/-- Abstract-bound variant of `exists_mem_representedSubset_of_degree_cover`:
takes `B' : Nat`, a per-factor coefficient bound
`hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint. The proof mirrors
the core-shape original but invokes the `_of_bound` sibling
`natDegree_toPolynomial_eq_sum_of_represents_of_bound` at the per-factor
`natDegree` identity step. -/
theorem exists_mem_representedSubset_of_degree_cover_of_bound
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B')
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  set f : LiftedFactorIndex d → Nat :=
    fun j => (HexPolyZMathlib.toPolynomial (liftedFactor d j)).natDegree
  -- Candidate-side: natDegree(recombinationCandidate d T) = ∑ j ∈ T, f j.
  have h_cand_eq :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ j ∈ T, f j :=
    natDegree_toPolynomial_recombinationCandidate_eq_sum
      hd_modulus hd_liftedFactor_monic T
  -- Each represented factor: natDegree(g) = ∑ j ∈ S_of g, f j.
  have h_g_eq : ∀ g ∈ gs,
      (HexPolyZMathlib.toPolynomial g).natDegree = ∑ j ∈ S_of g, f j := by
    intro g hg
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, _, _, hg_cont, hg_norm⟩ := h_each g hg
    have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd htarget_dvd_core
    exact natDegree_toPolynomial_eq_sum_of_represents_of_bound
      B' (hvalid g hg) hcore_ne hcore_monic hd_liftedFactor_monic
      hg_dvd_core hg_irr hg_cont hg_norm hg_rep hprecision
  -- Pairwise disjointness of the representing subsets, via partition.
  have h_pwdisj : Set.PairwiseDisjoint (↑gs : Set Hex.ZPoly) S_of := by
    intro g hg h hh hgh
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    obtain ⟨hh_irr, hh_dvd, _, hh_rep, hh_SJ, _, _, _⟩ := h_each h hh
    exact hpartition.pairwise_disjoint hg_irr hg_dvd hg_SJ hg_rep
      hh_irr hh_dvd hh_SJ hh_rep
      (h_pairwise_not_associated hg hh hgh)
  -- The biUnion is contained in T.
  have h_sub : gs.biUnion S_of ⊆ T := by
    intro j hj
    obtain ⟨g, hg, hjg⟩ := Finset.mem_biUnion.mp hj
    exact (h_each g hg).2.2.2.2.2.1 hjg
  -- ∑ T f = ∑ (gs.biUnion S_of) f.
  have h_sum_eq :
      ∑ j ∈ T, f j = ∑ j ∈ gs.biUnion S_of, f j := by
    have h_step : ∑ j ∈ gs.biUnion S_of, f j = ∑ g ∈ gs, ∑ j ∈ S_of g, f j :=
      Finset.sum_biUnion h_pwdisj
    rw [h_step, ← h_cand_eq, h_degree_total]
    exact Finset.sum_congr rfl h_g_eq
  -- ∑ (T \ biUnion) f = 0 by additive splitting on the subset.
  have h_zero : ∑ j ∈ T \ gs.biUnion S_of, f j = 0 := by
    have h_split :
        (∑ j ∈ T \ gs.biUnion S_of, f j) +
            (∑ j ∈ gs.biUnion S_of, f j) =
          ∑ j ∈ T, f j :=
      Finset.sum_sdiff h_sub
    omega
  -- Positivity of each summand forces T \ biUnion to be empty.
  have h_empty : T \ gs.biUnion S_of = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h_le : f j ≤ ∑ k ∈ T \ gs.biUnion S_of, f k :=
      Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hj
    have h_pos : 0 < f j := hd_liftedFactor_natDegree_pos j
    omega
  -- Conclude pointwise coverage.
  intro i hi
  have hi_in_bU : i ∈ gs.biUnion S_of := by
    by_contra h_not
    have h_in_sdiff : i ∈ T \ gs.biUnion S_of :=
      Finset.mem_sdiff.mpr ⟨hi, h_not⟩
    rw [h_empty] at h_in_sdiff
    exact Finset.notMem_empty _ h_in_sdiff
  exact Finset.mem_biUnion.mp hi_in_bU

/-- Reverse-coverage finite degree-counting step (issue #4468).

Given a `LiftedFactorSubsetPartition core d J target` and a subset `T ⊆ J`,
suppose `gs` is a finite family of `Hex.ZPoly` elements such that each
`g ∈ gs` is

* an irreducible divisor of `target` and of `recombinationCandidate d T`,
* represented at the lift by a subset `S_of g ⊆ T ⊆ J`,
* primitive (`content = 1`) and sign-normalized,

and the family is pairwise non-associated in `Polynomial ℤ` (so that the
partition's `pairwise_disjoint` field makes the `S_of g` pairwise disjoint).
If the candidate's `natDegree` decomposes as the sum of the `natDegree`s of
the family, then every index `i ∈ T` lies in some `S_of g`.

This is the finite Finset bookkeeping ingredient of the reverse-coverage
existence lemma (successor split from #4465). It does not extract irreducible
factors itself; the downstream `mem_T_iff_exists_irreducibleFactor_representingSubset`
assembler (#4467) supplies `gs` from `UniqueFactorizationMonoid.normalizedFactors`
together with the non-association hypothesis.

This is a thin wrapper over `exists_mem_representedSubset_of_degree_cover_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and discharges
`hvalid` per-factor: each `g ∈ gs` divides `target` via `h_each`, hence divides
`core` via `htarget_dvd_core`, and `defaultFactorCoeffBound_valid` supplies the
coefficient bound. -/
theorem exists_mem_representedSubset_of_degree_cover
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  have hvalid : ∀ g ∈ gs, ∀ i,
      (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound core := by
    intro g hg i
    obtain ⟨_, hg_dvd_target, _, _, _, _, _, _⟩ := h_each g hg
    have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_target htarget_dvd_core
    exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i
  intro i hi
  exact exists_mem_representedSubset_of_degree_cover_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition
    htarget_dvd_core _hTJ gs S_of h_each hvalid
    h_pairwise_not_associated h_degree_total hi

/-- Abstract-bound variant of
`exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core`:
takes `B' : Nat`, a per-factor coefficient bound
`hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B'`, the leading-coefficient
bound `hcore_lc_le : (leadingCoeff core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint. The proof mirrors the
core-shape original but invokes the `_of_bound` sibling
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound`
at the per-factor `natDegree` identity step. -/
theorem exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core_of_bound
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B')
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  set f : LiftedFactorIndex d → Nat :=
    fun j => (HexPolyZMathlib.toPolynomial (liftedFactor d j)).natDegree
  have h_cand_eq :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ j ∈ T, f j :=
    natDegree_toPolynomial_recombinationCandidate_eq_sum
      hd_modulus hd_liftedFactor_monic T
  have h_g_eq : ∀ g ∈ gs,
      (HexPolyZMathlib.toPolynomial g).natDegree = ∑ j ∈ S_of g, f j := by
    intro g hg
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, _, _, hg_cont, hg_norm⟩ := h_each g hg
    have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd htarget_dvd_core
    exact natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
      B' (hvalid g hg) hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos
      hd_liftedFactor_monic hg_dvd_core hg_irr hg_cont hg_norm hg_rep hprecision
  have h_pwdisj : Set.PairwiseDisjoint (↑gs : Set Hex.ZPoly) S_of := by
    intro g hg h hh hgh
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    obtain ⟨hh_irr, hh_dvd, _, hh_rep, hh_SJ, _, _, _⟩ := h_each h hh
    exact hpartition.pairwise_disjoint hg_irr hg_dvd hg_SJ hg_rep
      hh_irr hh_dvd hh_SJ hh_rep
      (h_pairwise_not_associated hg hh hgh)
  have h_sub : gs.biUnion S_of ⊆ T := by
    intro j hj
    obtain ⟨g, hg, hjg⟩ := Finset.mem_biUnion.mp hj
    exact (h_each g hg).2.2.2.2.2.1 hjg
  have h_sum_eq :
      ∑ j ∈ T, f j = ∑ j ∈ gs.biUnion S_of, f j := by
    have h_step : ∑ j ∈ gs.biUnion S_of, f j = ∑ g ∈ gs, ∑ j ∈ S_of g, f j :=
      Finset.sum_biUnion h_pwdisj
    rw [h_step, ← h_cand_eq, h_degree_total]
    exact Finset.sum_congr rfl h_g_eq
  have h_zero : ∑ j ∈ T \ gs.biUnion S_of, f j = 0 := by
    have h_split :
        (∑ j ∈ T \ gs.biUnion S_of, f j) +
            (∑ j ∈ gs.biUnion S_of, f j) =
          ∑ j ∈ T, f j :=
      Finset.sum_sdiff h_sub
    omega
  have h_empty : T \ gs.biUnion S_of = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h_le : f j ≤ ∑ k ∈ T \ gs.biUnion S_of, f k :=
      Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hj
    have h_pos : 0 < f j := hd_liftedFactor_natDegree_pos j
    omega
  intro i hi
  have hi_in_bU : i ∈ gs.biUnion S_of := by
    by_contra h_not
    have h_in_sdiff : i ∈ T \ gs.biUnion S_of :=
      Finset.mem_sdiff.mpr ⟨hi, h_not⟩
    rw [h_empty] at h_in_sdiff
    exact Finset.notMem_empty _ h_in_sdiff
  exact Finset.mem_biUnion.mp hi_in_bU

/--
Primitive + positive-leading-core variant of
`exists_mem_representedSubset_of_degree_cover` (#4646 chain).

Identical to the monic variant except the per-factor natDegree identity routes
through `natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core`
instead of the monic-core version.

This is a thin wrapper over
`exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core`. The per-factor
`hvalid` is discharged via the divisor chain `g ∣ target ∣ core` plus
`defaultFactorCoeffBound_valid`; `hcore_lc_le` is discharged via
`defaultFactorCoeffBound_valid core hcore_ne core hcore_dvd_self (core.size - 1)`
together with `leadingCoeff_eq_coeff_last`.
-/
theorem exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hvalid : ∀ g ∈ gs, ∀ i,
      (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound core := by
    intro g hg i
    obtain ⟨_, hg_dvd_target, _, _, _, _, _, _⟩ := h_each g hg
    have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_target htarget_dvd_core
    exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i
  intro i hi
  exact exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le hd_modulus
    hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
    htarget_dvd_core _hTJ gs S_of h_each hvalid
    h_pairwise_not_associated h_degree_total hi

/--
Abstract-bound variant of
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate`:
takes a universal bound `B'` valid on every normalised `Polynomial ℤ` factor
of the recombination candidate, together with the precision hypothesis
`2 * B' < d.p ^ d.k`, in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

The abstract bound is consumed only at the call to the abstract-bound
support-containment lemma
`representingSubset_subset_of_dvd_recombinationCandidate_of_bound`, which is
vestigial in precision (the structural support field of the partition does
not depend on it). The bound is threaded purely for API parity with the
broader `_of_bound` propagation chain. -/
theorem exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (_htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  obtain ⟨hcand_poly_ne_zero, _hcand_poly_nonunit⟩ :=
    toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord
  have hg_norm :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p := gPoly) (x := HexPolyZMathlib.toPolynomial (recombinationCandidate d T))
      hcand_poly_ne_zero).mp hg_mem
  rcases hg_norm with ⟨hg_irr, hg_normalized, hg_dvd_cand_poly⟩
  let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
  have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
    HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
  have hg_irr_toPoly : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPolynomial]
    exact hg_irr
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    rw [hg_toPolynomial]
    exact hr
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hg_dvd_target : g ∣ target := zpoly_dvd_trans hg_dvd_cand hcand_dvd_target
  obtain ⟨S_g, hSJ, hSrep⟩ :=
    hpartition.exists_subset hg_irr_toPoly hg_dvd_target
  have hST : S_g ⊆ T :=
    representingSubset_subset_of_dvd_recombinationCandidate_of_bound
      B' (hvalid g (by rw [hg_toPolynomial]; exact hg_mem))
      hcore_ne hcore_monic hprecision hpartition hTJ hg_irr_toPoly
      hg_dvd_target hg_dvd_cand hSJ hSrep
  have hcand_monic_poly :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic :=
    toPolynomial_recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T
  have hg_monic_poly : gPoly.Monic := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      apply hcand_monic_poly.ne_zero
      rw [hr, hr_zero, mul_zero]
    have hlead_mul : gPoly.leadingCoeff * r.leadingCoeff = (1 : Int) := by
      have hlead := Polynomial.leadingCoeff_mul gPoly r
      rw [← hr, hcand_monic_poly.leadingCoeff] at hlead
      simpa using hlead.symm
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have hlead := congrArg Polynomial.leadingCoeff hg_normalized
      rwa [Polynomial.leadingCoeff_normalize] at hlead
    have hlead_nonneg : 0 ≤ gPoly.leadingCoeff :=
      Int.nonneg_of_normalize_eq_self hlead_normalized
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlead_mul with hpos | hneg
    · exact hpos.1
    · exfalso
      rw [hneg.1] at hlead_nonneg
      omega
  have hg_monic_hex : Hex.DensePoly.Monic g := by
    have hlead : (HexPolyZMathlib.toPolynomial g).leadingCoeff = 1 := by
      rw [hg_toPolynomial]
      exact hg_monic_poly
    rwa [HexPolyMathlib.leadingCoeff_toPolynomial] at hlead
  have hg_content : Hex.ZPoly.content g = 1 :=
    zpoly_primitive_of_monic hg_monic_hex
  have hg_norm_sign : Hex.normalizeFactorSign g = g :=
    zpoly_normalize_factor_sign_of_monic hg_monic_hex
  exact ⟨g, S_g, hg_toPolynomial, hg_irr_toPoly, hg_dvd_target, hg_dvd_cand,
    hSrep, hSJ, hST, hg_content, hg_norm_sign⟩

/--
Package a normalized irreducible factor of a recombination candidate as an
executable `Hex.ZPoly` factor with the represented subset facts needed by the
reverse-coverage degree argument.

The normalized-factor membership supplies an irreducible divisor of
`toPolynomial (recombinationCandidate d T)`. Since the candidate is monic, that
normalized divisor is monic too. Transporting the divisor back through
`HexPolyZMathlib.ofPolynomial` gives a `Hex.ZPoly` divisor of the candidate and
hence of `target`; the partition then provides its representing subset, and the
support-containment field forces that subset to lie in `T`.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_bound`:
each normalised factor `g` of the candidate divides the candidate, which
divides `target` (via `hquot`), which divides `core` (via `htarget_dvd_core`),
so `defaultFactorCoeffBound_valid` discharges the universal bound hypothesis.
-/
theorem exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  refine exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic hprecision
    hpartition htarget_dvd_core hTJ hrecord hquot hg_mem
  -- Discharge `hvalid` for arbitrary normalised factor `g` of the candidate
  -- by chaining `g ∣ candidate ∣ target ∣ core` and invoking
  -- `defaultFactorCoeffBound_valid`.
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := by
    rcases hg_dvd_cand with ⟨r₁, hr₁⟩
    rcases hcand_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Abstract-bound variant of
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core`:
takes a universal bound `B'` valid on every normalised `Polynomial ℤ` factor
of the recombination candidate, together with the precision hypothesis
`2 * B' < d.p ^ d.k`, in place of the core-shape `defaultFactorCoeffBound core`
precision constraint.

As in the support-containment chain, the abstract bound is consumed only at
the call to
`representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound`,
which is vestigial in precision (the structural support field of the
partition does not depend on it). The bound is threaded purely for API parity
with the broader `_of_bound` propagation chain. -/
theorem exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (_htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  obtain ⟨hcand_poly_ne_zero, _hcand_poly_nonunit⟩ :=
    toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord
  have hg_norm :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p := gPoly) (x := HexPolyZMathlib.toPolynomial (recombinationCandidate d T))
      hcand_poly_ne_zero).mp hg_mem
  rcases hg_norm with ⟨hg_irr, hg_normalized, hg_dvd_cand_poly⟩
  let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
  have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
    HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
  have hg_irr_toPoly : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPolynomial]
    exact hg_irr
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    rw [hg_toPolynomial]
    exact hr
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hg_dvd_target : g ∣ target := by
    rcases hg_dvd_cand with ⟨r₁, hr₁⟩
    rcases hcand_dvd_target with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  obtain ⟨S_g, hSJ, hSrep⟩ :=
    hpartition.exists_subset hg_irr_toPoly hg_dvd_target
  have hST : S_g ⊆ T :=
    representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound
      B' (hvalid g (by rw [hg_toPolynomial]; exact hg_mem))
      hcore_ne hcore_primitive hcore_lc_pos hprecision hpartition hTJ
      hg_irr_toPoly hg_dvd_target hg_dvd_cand hSJ hSrep
  have hcand_monic_poly :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic :=
    toPolynomial_recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T
  have hg_monic_poly : gPoly.Monic := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      apply hcand_monic_poly.ne_zero
      rw [hr, hr_zero, mul_zero]
    have hlead_mul : gPoly.leadingCoeff * r.leadingCoeff = (1 : Int) := by
      have hlead := Polynomial.leadingCoeff_mul gPoly r
      rw [← hr, hcand_monic_poly.leadingCoeff] at hlead
      simpa using hlead.symm
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have hlead := congrArg Polynomial.leadingCoeff hg_normalized
      rwa [Polynomial.leadingCoeff_normalize] at hlead
    have hlead_nonneg : 0 ≤ gPoly.leadingCoeff :=
      Int.nonneg_of_normalize_eq_self hlead_normalized
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlead_mul with hpos | hneg
    · exact hpos.1
    · exfalso
      rw [hneg.1] at hlead_nonneg
      omega
  have hg_monic_hex : Hex.DensePoly.Monic g := by
    have hlead : (HexPolyZMathlib.toPolynomial g).leadingCoeff = 1 := by
      rw [hg_toPolynomial]
      exact hg_monic_poly
    rwa [HexPolyMathlib.leadingCoeff_toPolynomial] at hlead
  obtain ⟨_, hg_content, hg_norm_sign⟩ :=
    monic_primitive_sign_normalized_of_monic hg_monic_hex
  exact ⟨g, S_g, hg_toPolynomial, hg_irr_toPoly, hg_dvd_target, hg_dvd_cand,
    hSrep, hSJ, hST, hg_content, hg_norm_sign⟩

/-- Primitive + positive-leading-core variant of
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate`
(#4646 chain).

The monic-core hypothesis is threaded only through
`representingSubset_subset_of_dvd_recombinationCandidate` (vestigial there);
all essential algebra runs on the always-monic recombination candidate, so
the proof body is identical to the monic version except for the routing
through the primitive-core variants of the helpers.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core_of_bound`:
each normalised factor `g` of the candidate divides the candidate, which
divides `target` (via `hquot`), which divides `core` (via `htarget_dvd_core`),
so `defaultFactorCoeffBound_valid` discharges the universal bound hypothesis. -/
theorem exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  refine exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hprecision hpartition htarget_dvd_core hTJ hrecord hquot hg_mem
  -- Discharge `hvalid` for arbitrary normalised factor `g` of the candidate
  -- by chaining `g ∣ candidate ∣ target ∣ core` and invoking
  -- `defaultFactorCoeffBound_valid`.
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := by
    rcases hg_dvd_cand with ⟨r₁, hr₁⟩
    rcases hcand_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Reverse-coverage existence theorem for the recombination candidate.

Given a `LiftedFactorSubsetPartition core d J target` and a subset `T ⊆ J`,
suppose the candidate `recombinationCandidate d T` is recordable and admits an
exact quotient against `target`. Then every local index `i ∈ T` lies in the
representing subset `S_g` of some irreducible `Hex.ZPoly` divisor `g` of the
candidate, with `S_g ⊆ J`.

The proof packages the UFD normalized factorisation of
`HexPolyZMathlib.toPolynomial (recombinationCandidate d T)` through the
per-factor lemma `exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate`
(#4467), then closes the degree-counting obligation of
`exists_mem_representedSubset_of_degree_cover` (#4468) using monicness and
squarefreeness of the candidate together with
`Polynomial.natDegree_multiset_prod_of_monic`.

Together with the forward divisor extraction
`exists_representingSubset_dvd_recombinationCandidate_of_exactQuotient`, this
theorem supplies the bidirectional content the main candidate divisibility
theorem (#4457) needs to relate every `i ∈ T` to a partition-representing
irreducible divisor of the recombination candidate. -/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  -- Candidate properties: nonzero, monic, squarefree.
  have hcand_ne :
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) ≠ 0 :=
    (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
  have hcand_monic :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic :=
    toPolynomial_recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T
  have hcand_squarefree :
      Squarefree (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) :=
    toPolynomial_recombinationCandidate_squarefree hpartition hquot
  set normFactors :=
    UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) with hnf_def
  -- Squarefreeness ↦ Nodup of the normalized factor multiset.
  have hnf_nodup : normFactors.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hcand_ne).mp
      hcand_squarefree
  -- Per-normalized-factor monicness: each normalized divisor of a monic poly is monic.
  have hnf_monic : ∀ gPoly ∈ normFactors, gPoly.Monic := by
    intro gPoly hgPoly
    have hg_norm_eq : normalize gPoly = gPoly :=
      UniqueFactorizationMonoid.normalize_normalized_factor gPoly hgPoly
    have hg_dvd_cand :
        gPoly ∣ HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hgPoly
    obtain ⟨r, hr⟩ := hg_dvd_cand
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      apply hcand_monic.ne_zero
      rw [hr, hr_zero, mul_zero]
    have hlead_mul : gPoly.leadingCoeff * r.leadingCoeff = (1 : Int) := by
      have hlead := Polynomial.leadingCoeff_mul gPoly r
      rw [← hr, hcand_monic.leadingCoeff] at hlead
      simpa using hlead.symm
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have := congrArg Polynomial.leadingCoeff hg_norm_eq
      rwa [Polynomial.leadingCoeff_normalize] at this
    have hlead_nonneg : 0 ≤ gPoly.leadingCoeff :=
      Int.nonneg_of_normalize_eq_self hlead_normalized
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlead_mul with hpos | hneg
    · exact hpos.1
    · exfalso
      rw [hneg.1] at hlead_nonneg
      omega
  -- Product of normalized factors equals the (monic) candidate.
  have hnf_prod_eq :
      normFactors.prod =
        HexPolyZMathlib.toPolynomial (recombinationCandidate d T) := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hcand_ne,
      hcand_monic.normalize_eq_self]
  -- Per-normalized-factor data, indexed by hex factor `g = ofPolynomial gPoly`.
  have bridge_for : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈ normFactors →
      ∃ S_g : LiftedFactorSubset d,
        Irreducible (HexPolyZMathlib.toPolynomial g) ∧
        g ∣ target ∧
        g ∣ recombinationCandidate d T ∧
        RepresentsIntegerFactorAtLift core d g S_g ∧
        S_g ⊆ J ∧
        S_g ⊆ T ∧
        Hex.ZPoly.content g = 1 ∧
        Hex.normalizeFactorSign g = g := by
    intro g hgPoly
    obtain ⟨g', S_g, h_eq, h_irr, h_dvd_t, h_dvd_c, h_rep, h_SJ, h_ST,
        h_cont, h_norm⟩ :=
      exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_bound
        B' hvalid hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic hprecision
        hpartition htarget_dvd_core hTJ hrecord hquot hgPoly
    have hg_eq : g' = g := by
      have := congrArg HexPolyZMathlib.ofPolynomial h_eq
      simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
    refine ⟨S_g, ?_, ?_, ?_, ?_, h_SJ, h_ST, ?_, ?_⟩
    · rw [← hg_eq]; exact h_irr
    · rw [← hg_eq]; exact h_dvd_t
    · rw [← hg_eq]; exact h_dvd_c
    · rw [← hg_eq]; exact h_rep
    · rw [← hg_eq]; exact h_cont
    · rw [← hg_eq]; exact h_norm
  -- Choose `S_of g` via the lemma for `g`'s normalized-factor membership.
  let S_of : Hex.ZPoly → LiftedFactorSubset d := fun g =>
    if h : HexPolyZMathlib.toPolynomial g ∈ normFactors then
      Classical.choose (bridge_for g h)
    else (∅ : LiftedFactorSubset d)
  let gs : Finset Hex.ZPoly :=
    normFactors.toFinset.image HexPolyZMathlib.ofPolynomial
  -- Membership in `gs` is membership of `toPolynomial g` in `normFactors`.
  have mem_gs : ∀ {g : Hex.ZPoly},
      g ∈ gs ↔ HexPolyZMathlib.toPolynomial g ∈ normFactors := by
    intro g
    refine ⟨?_, ?_⟩
    · intro hg
      rcases Finset.mem_image.mp hg with ⟨gPoly, hgPoly_mem, h_eq⟩
      rw [Multiset.mem_toFinset] at hgPoly_mem
      rw [← h_eq, HexPolyZMathlib.toPolynomial_ofPolynomial]
      exact hgPoly_mem
    · intro hg
      refine Finset.mem_image.mpr ⟨HexPolyZMathlib.toPolynomial g, ?_, ?_⟩
      · exact Multiset.mem_toFinset.mpr hg
      · exact HexPolyZMathlib.ofPolynomial_toPolynomial g
  -- Per-element data for `exists_mem_representedSubset_of_degree_cover`.
  have h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
    intro g hg
    have hg_norm := mem_gs.mp hg
    have hS_of_eq :
        S_of g = Classical.choose (bridge_for g hg_norm) := by
      simp [S_of, dif_pos hg_norm]
    have hspec := Classical.choose_spec (bridge_for g hg_norm)
    rw [hS_of_eq]
    exact hspec
  -- Pairwise non-association via normalize_eq + injectivity of `toPolynomial`.
  have h_pairwise : ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
      ¬ Associated (HexPolyZMathlib.toPolynomial g)
        (HexPolyZMathlib.toPolynomial h) := by
    intro g h hg_in hh_in hgh hassoc
    have hg_norm := mem_gs.mp hg_in
    have hh_norm := mem_gs.mp hh_in
    have hg_eq :
        normalize (HexPolyZMathlib.toPolynomial g) =
          HexPolyZMathlib.toPolynomial g :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hg_norm
    have hh_eq :
        normalize (HexPolyZMathlib.toPolynomial h) =
          HexPolyZMathlib.toPolynomial h :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hh_norm
    have hpoly_eq :
        HexPolyZMathlib.toPolynomial g = HexPolyZMathlib.toPolynomial h := by
      rw [← hg_eq, ← hh_eq]
      exact normalize_eq_normalize hassoc.dvd hassoc.symm.dvd
    apply hgh
    have := congrArg HexPolyZMathlib.ofPolynomial hpoly_eq
    simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
  -- Degree of candidate equals the sum of degrees of `gs` (via prod of monic).
  have h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree := by
    have h_image_sum :
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree =
          ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree := by
      show ∑ g ∈ normFactors.toFinset.image HexPolyZMathlib.ofPolynomial,
          (HexPolyZMathlib.toPolynomial g).natDegree =
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro gPoly _
        simp
      · intro a _ b _ heq
        have := congrArg HexPolyZMathlib.toPolynomial heq
        simpa using this
    have h_toFinset_sum :
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree =
          (normFactors.map Polynomial.natDegree).sum := by
      change (normFactors.toFinset.val.map Polynomial.natDegree).sum =
        (normFactors.map Polynomial.natDegree).sum
      rw [Multiset.toFinset_val, hnf_nodup.dedup]
    rw [h_image_sum, h_toFinset_sum, ← hnf_prod_eq,
      Polynomial.natDegree_multiset_prod_of_monic _ hnf_monic]
  -- Apply the finite degree-cover lemma.
  obtain ⟨g, hg_in_gs, hi_in_Sg⟩ :=
    exists_mem_representedSubset_of_degree_cover_of_bound
      B' hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
      hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
      gs S_of h_each (fun g hg => hvalid g (mem_gs.mp hg))
      h_pairwise h_degree_total hi
  -- Extract the witness for `g`.
  have hg_norm := mem_gs.mp hg_in_gs
  obtain ⟨h_irr, _, h_dvd_c, h_rep, h_SJ, _, _, _⟩ := h_each g hg_in_gs
  exact ⟨g, S_of g, h_irr, h_dvd_c, h_rep, h_SJ, hi_in_Sg⟩

/-- Default-bound wrapper for
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_bound`. -/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  refine mem_T_iff_exists_irreducibleFactor_representingSubset_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core
    hTJ hrecord hquot hi
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := by
    rcases hg_dvd_cand with ⟨r₁, hr₁⟩
    rcases hcand_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Primitive + positive-leading-core variant of
`mem_T_iff_exists_irreducibleFactor_representingSubset` (#4646 chain).

Same proof structure as the monic variant, but the per-factor representing
subset is obtained via
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core`
and the final degree-cover application uses the primitive-core variant
`exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core`.
-/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcand_ne :
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) ≠ 0 :=
    (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
  have hcand_monic :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).Monic :=
    toPolynomial_recombinationCandidate_monic hd_modulus hd_liftedFactor_monic T
  have hcand_squarefree :
      Squarefree (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) :=
    toPolynomial_recombinationCandidate_squarefree hpartition hquot
  set normFactors :=
    UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) with hnf_def
  have hnf_nodup : normFactors.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hcand_ne).mp
      hcand_squarefree
  have hnf_monic : ∀ gPoly ∈ normFactors, gPoly.Monic := by
    intro gPoly hgPoly
    have hg_norm_eq : normalize gPoly = gPoly :=
      UniqueFactorizationMonoid.normalize_normalized_factor gPoly hgPoly
    have hg_dvd_cand :
        gPoly ∣ HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hgPoly
    obtain ⟨r, hr⟩ := hg_dvd_cand
    have hr_ne : r ≠ 0 := by
      intro hr_zero
      apply hcand_monic.ne_zero
      rw [hr, hr_zero, mul_zero]
    have hlead_mul : gPoly.leadingCoeff * r.leadingCoeff = (1 : Int) := by
      have hlead := Polynomial.leadingCoeff_mul gPoly r
      rw [← hr, hcand_monic.leadingCoeff] at hlead
      simpa using hlead.symm
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have := congrArg Polynomial.leadingCoeff hg_norm_eq
      rwa [Polynomial.leadingCoeff_normalize] at this
    have hlead_nonneg : 0 ≤ gPoly.leadingCoeff :=
      Int.nonneg_of_normalize_eq_self hlead_normalized
    rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hlead_mul with hpos | hneg
    · exact hpos.1
    · exfalso
      rw [hneg.1] at hlead_nonneg
      omega
  have hnf_prod_eq :
      normFactors.prod =
        HexPolyZMathlib.toPolynomial (recombinationCandidate d T) := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hcand_ne,
      hcand_monic.normalize_eq_self]
  have bridge_for : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈ normFactors →
      ∃ S_g : LiftedFactorSubset d,
        Irreducible (HexPolyZMathlib.toPolynomial g) ∧
        g ∣ target ∧
        g ∣ recombinationCandidate d T ∧
        RepresentsIntegerFactorAtLift core d g S_g ∧
        S_g ⊆ J ∧
        S_g ⊆ T ∧
        Hex.ZPoly.content g = 1 ∧
        Hex.normalizeFactorSign g = g := by
    intro g hgPoly
    obtain ⟨g', S_g, h_eq, h_irr, h_dvd_t, h_dvd_c, h_rep, h_SJ, h_ST,
        h_cont, h_norm⟩ :=
      exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core_of_bound
        B' hvalid hcore_ne hcore_primitive hcore_lc_pos hd_modulus
        hd_liftedFactor_monic hprecision hpartition htarget_dvd_core hTJ
        hrecord hquot hgPoly
    have hg_eq : g' = g := by
      have := congrArg HexPolyZMathlib.ofPolynomial h_eq
      simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
    refine ⟨S_g, ?_, ?_, ?_, ?_, h_SJ, h_ST, ?_, ?_⟩
    · rw [← hg_eq]; exact h_irr
    · rw [← hg_eq]; exact h_dvd_t
    · rw [← hg_eq]; exact h_dvd_c
    · rw [← hg_eq]; exact h_rep
    · rw [← hg_eq]; exact h_cont
    · rw [← hg_eq]; exact h_norm
  let S_of : Hex.ZPoly → LiftedFactorSubset d := fun g =>
    if h : HexPolyZMathlib.toPolynomial g ∈ normFactors then
      Classical.choose (bridge_for g h)
    else (∅ : LiftedFactorSubset d)
  let gs : Finset Hex.ZPoly :=
    normFactors.toFinset.image HexPolyZMathlib.ofPolynomial
  have mem_gs : ∀ {g : Hex.ZPoly},
      g ∈ gs ↔ HexPolyZMathlib.toPolynomial g ∈ normFactors := by
    intro g
    refine ⟨?_, ?_⟩
    · intro hg
      rcases Finset.mem_image.mp hg with ⟨gPoly, hgPoly_mem, h_eq⟩
      rw [Multiset.mem_toFinset] at hgPoly_mem
      rw [← h_eq, HexPolyZMathlib.toPolynomial_ofPolynomial]
      exact hgPoly_mem
    · intro hg
      refine Finset.mem_image.mpr ⟨HexPolyZMathlib.toPolynomial g, ?_, ?_⟩
      · exact Multiset.mem_toFinset.mpr hg
      · exact HexPolyZMathlib.ofPolynomial_toPolynomial g
  have h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
    intro g hg
    have hg_norm := mem_gs.mp hg
    have hS_of_eq :
        S_of g = Classical.choose (bridge_for g hg_norm) := by
      simp [S_of, dif_pos hg_norm]
    have hspec := Classical.choose_spec (bridge_for g hg_norm)
    rw [hS_of_eq]
    exact hspec
  have h_pairwise : ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
      ¬ Associated (HexPolyZMathlib.toPolynomial g)
        (HexPolyZMathlib.toPolynomial h) := by
    intro g h hg_in hh_in hgh hassoc
    have hg_norm := mem_gs.mp hg_in
    have hh_norm := mem_gs.mp hh_in
    have hg_eq :
        normalize (HexPolyZMathlib.toPolynomial g) =
          HexPolyZMathlib.toPolynomial g :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hg_norm
    have hh_eq :
        normalize (HexPolyZMathlib.toPolynomial h) =
          HexPolyZMathlib.toPolynomial h :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hh_norm
    have hpoly_eq :
        HexPolyZMathlib.toPolynomial g = HexPolyZMathlib.toPolynomial h := by
      rw [← hg_eq, ← hh_eq]
      exact normalize_eq_normalize hassoc.dvd hassoc.symm.dvd
    apply hgh
    have := congrArg HexPolyZMathlib.ofPolynomial hpoly_eq
    simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
  have h_degree_total :
      (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree := by
    have h_image_sum :
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree =
          ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree := by
      show ∑ g ∈ normFactors.toFinset.image HexPolyZMathlib.ofPolynomial,
          (HexPolyZMathlib.toPolynomial g).natDegree =
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro gPoly _
        simp
      · intro a _ b _ heq
        have := congrArg HexPolyZMathlib.toPolynomial heq
        simpa using this
    have h_toFinset_sum :
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree =
          (normFactors.map Polynomial.natDegree).sum := by
      change (normFactors.toFinset.val.map Polynomial.natDegree).sum =
        (normFactors.map Polynomial.natDegree).sum
      rw [Multiset.toFinset_val, hnf_nodup.dedup]
    rw [h_image_sum, h_toFinset_sum, ← hnf_prod_eq,
      Polynomial.natDegree_multiset_prod_of_monic _ hnf_monic]
  obtain ⟨g, hg_in_gs, hi_in_Sg⟩ :=
    exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core_of_bound
      B' hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le hd_modulus
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
      htarget_dvd_core hTJ gs S_of h_each
      (fun g hg => hvalid g (mem_gs.mp hg)) h_pairwise h_degree_total hi
  have hg_norm := mem_gs.mp hg_in_gs
  obtain ⟨h_irr, _, h_dvd_c, h_rep, h_SJ, _, _, _⟩ := h_each g hg_in_gs
  exact ⟨g, S_of g, h_irr, h_dvd_c, h_rep, h_SJ, hi_in_Sg⟩

/-- Primitive + positive-leading-core variant of
`mem_T_iff_exists_irreducibleFactor_representingSubset` (#4646 chain).

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound`.
-/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ recombinationCandidate d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' i => by
      have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
          HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
        UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
      have hg_dvd_cand : g ∣ recombinationCandidate d T := by
        rcases hg_poly_dvd with ⟨r, hr⟩
        refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
        apply HexPolyZMathlib.equiv.injective
        simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
          HexPolyZMathlib.toPolynomial_ofPolynomial]
        exact hr
      have hg_dvd_core : g ∣ core := by
        rcases hg_dvd_cand with ⟨r₁, hr₁⟩
        rcases hcand_dvd_core with ⟨r₂, hr₂⟩
        refine ⟨r₁ * r₂, ?_⟩
        rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
      exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i)
    hcore_ne hcore_primitive hcore_lc_pos
    (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
    hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
    hprecision hpartition htarget_dvd_core hTJ hrecord hquot hi

/--
Package reverse candidate support in the form consumed by the cover-at-min
assembler: every selected local index in a recorded recombination candidate
belongs to the representing subset of an irreducible integer factor that
divides both the recursive target and the candidate.
-/
theorem exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ recombinationCandidate d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  obtain ⟨f, S, hf_irr, hf_dvd_candidate, hrep, hSJ, hiS⟩ :=
    mem_T_iff_exists_irreducibleFactor_representingSubset_of_bound
      B' hvalid hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
      hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
      hrecord hquot hi
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hf_dvd_target : f ∣ target := zpoly_dvd_trans hf_dvd_candidate hcand_dvd_target
  exact ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_candidate, hSJ, hiS, hrep⟩

/-- Default-bound wrapper for
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_bound`. -/
theorem exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ recombinationCandidate d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core :=
    zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
  refine exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core
    hTJ hrecord hquot hi
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/--
Cover-at-min containment from recombination-candidate support: when the
recorded candidate at `T ⊆ J` exactly divides `target`, the cover witness at
`J.min'` has its representing subset contained in `T`.

This is the form consumed by the prefix-none recombination-search assembler:
it combines the reverse-support coverage packaging
(`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd`) applied
at `i := J.min' hne` with the forward-support containment
(`representingSubset_subset_of_dvd_recombinationCandidate`) to obtain the
single cover factor whose representing subset both contains `J.min' hne`
and is contained in `T`.
-/
theorem coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  obtain ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_cand, hSJ, hmin_in_S, hrep⟩ :=
    exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_bound
      B' hvalid hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
      hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
      hrecord hquot hmin_in_T
  have hST : S ⊆ T :=
    hpartition.support_subset_of_dvd_recombinationCandidate
      hf_irr hf_dvd_target hTJ
      (by
        rw [← recombinationCandidate_eq_liftedFactorProductCandidate]
        exact hf_dvd_cand)
      hSJ hrep
  exact ⟨f, S, hf_irr, hf_dvd_target, hSJ, hmin_in_S, hrep, hST⟩

/-- Default-bound wrapper for
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound`. -/
theorem coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core :=
    zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
  refine coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
    hne hmin_in_T hrecord hquot
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ recombinationCandidate d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Abstract-bound primitive + positive-leading-core variant of
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd` (#4646 chain).

Routes through the abstract-bound
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound`
supporting lemma; the remaining divisor repackaging is precision-agnostic. -/
theorem exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ recombinationCandidate d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  obtain ⟨f, S, hf_irr, hf_dvd_candidate, hrep, hSJ, hiS⟩ :=
    mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core_of_bound
      B' hvalid hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hprecision hpartition htarget_dvd_core hTJ hrecord hquot hi
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hf_dvd_target : f ∣ target := zpoly_dvd_trans hf_dvd_candidate hcand_dvd_target
  exact ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_candidate, hSJ, hiS, hrep⟩

/-- Primitive + positive-leading-core variant of
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd` (#4646 chain).

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`.
-/
theorem exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ recombinationCandidate d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact
    exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
      (Hex.ZPoly.defaultFactorCoeffBound core)
      (fun g hg_mem' i => by
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
        have hg_dvd_cand : g ∣ recombinationCandidate d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core := by
          rcases hg_dvd_cand with ⟨r₁, hr₁⟩
          rcases hcand_dvd_core with ⟨r₂, hr₂⟩
          refine ⟨r₁ * r₂, ?_⟩
          rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
        exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i)
      hcore_ne hcore_primitive hcore_lc_pos
      (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hprecision hpartition htarget_dvd_core hTJ hrecord hquot hi

/-- Abstract-bound primitive + positive-leading-core variant of
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd` (#4646 chain).

Routes through
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`
and
`representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound`. -/
theorem coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial (recombinationCandidate d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  obtain ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_cand, hSJ, hmin_in_S, hrep⟩ :=
    exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
      B' hvalid hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hprecision hpartition htarget_dvd_core hTJ hrecord hquot hmin_in_T
  have hvalid_f : ∀ i, (f.coeff i).natAbs ≤ B' := by
    have hcand_poly_ne_zero :
        HexPolyZMathlib.toPolynomial (recombinationCandidate d T) ≠ 0 :=
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
    have hf_poly_dvd :
        HexPolyZMathlib.toPolynomial f ∣
          HexPolyZMathlib.toPolynomial (recombinationCandidate d T) := by
      rcases hf_dvd_cand with ⟨r, hr⟩
      refine ⟨HexPolyZMathlib.toPolynomial r, ?_⟩
      rw [← HexPolyZMathlib.toPolynomial_mul, hr]
    obtain ⟨gPoly, hg_mem, hg_assoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        hcand_poly_ne_zero hf_irr hf_poly_dvd
    let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
    have hg_toPoly : HexPolyZMathlib.toPolynomial g = gPoly :=
      HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
    have hg_bound : ∀ i, (g.coeff i).natAbs ≤ B' :=
      hvalid g (by rw [hg_toPoly]; exact hg_mem)
    obtain ⟨u, hu⟩ := hg_assoc
    obtain ⟨c, hc_unit, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
    have hc_abs_one : c.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hc_unit
    intro i
    have hg_coeff : g.coeff i = gPoly.coeff i := by
      have := HexPolyZMathlib.coeff_toPolynomial g i
      rw [hg_toPoly] at this
      exact this.symm
    have hgPoly_coeff_f : gPoly.coeff i = f.coeff i * c := by
      have hmul : (HexPolyZMathlib.toPolynomial f * Polynomial.C c).coeff i =
          (HexPolyZMathlib.toPolynomial f).coeff i * c :=
        Polynomial.coeff_mul_C _ _ _
      rw [← hu, ← hcu, hmul, HexPolyZMathlib.coeff_toPolynomial]
    have hbound := hg_bound i
    rw [hg_coeff, hgPoly_coeff_f, Int.natAbs_mul, hc_abs_one,
      Nat.mul_one] at hbound
    exact hbound
  have hST : S ⊆ T :=
    representingSubset_subset_of_dvd_recombinationCandidate_of_primitive_pos_lc_core_of_bound
      B' hvalid_f hcore_ne hcore_primitive hcore_lc_pos hprecision
      hpartition hTJ hf_irr hf_dvd_target hf_dvd_cand hSJ hrep
  exact ⟨f, S, hf_irr, hf_dvd_target, hSJ, hmin_in_S, hrep, hST⟩

/-- Primitive + positive-leading-core variant of
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd` (#4646 chain).

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`.
-/
theorem coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    have hmul : quotient * recombinationCandidate d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core : recombinationCandidate d T ∣ core := by
    rcases hcand_dvd_target with ⟨r₁, hr₁⟩
    rcases htarget_dvd_core with ⟨r₂, hr₂⟩
    refine ⟨r₁ * r₂, ?_⟩
    rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
  exact
    coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
      (Hex.ZPoly.defaultFactorCoeffBound core)
      (fun g hg_mem' i => by
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
        have hg_dvd_cand : g ∣ recombinationCandidate d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core := by
          rcases hg_dvd_cand with ⟨r₁, hr₁⟩
          rcases hcand_dvd_core with ⟨r₂, hr₂⟩
          refine ⟨r₁ * r₂, ?_⟩
          rw [hr₂, hr₁, Hex.DensePoly.mul_assoc_poly (S := Int)]
        exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i)
      hcore_ne hcore_primitive hcore_lc_pos
      (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hprecision hpartition htarget_dvd_core hTJ hne hmin_in_T hrecord hquot

/-- `Hex.normalizeFactorSign` preserves the content of a `Hex.ZPoly`: it either
returns the input or scales by `-1`, both of which leave the content (the gcd
of absolute values of the coefficients) unchanged. -/
private theorem content_normalizeFactorSign_eq (f : Hex.ZPoly) :
    Hex.ZPoly.content (Hex.normalizeFactorSign f) = Hex.ZPoly.content f := by
  unfold Hex.normalizeFactorSign
  by_cases h : Hex.DensePoly.leadingCoeff f < 0
  · rw [if_pos h]
    show Hex.DensePoly.content (Hex.DensePoly.scale (-1 : Int) f) =
      Hex.DensePoly.content f
    exact Hex.DensePoly.content_scale_neg_one f
  · rw [if_neg h]

/-- The output of `Hex.normalizeFactorSign` has nonnegative leading coefficient:
the `if_neg` branch keeps the input (whose leading coefficient is already
`≥ 0`), and the `if_pos` branch negates a strictly negative leading coefficient
to a nonnegative one. -/
private theorem leadingCoeff_normalizeFactorSign_nonneg (f : Hex.ZPoly) :
    0 ≤ Hex.DensePoly.leadingCoeff (Hex.normalizeFactorSign f) := by
  unfold Hex.normalizeFactorSign
  by_cases h : Hex.DensePoly.leadingCoeff f < 0
  · rw [if_pos h]
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero (-1 : Int) f (by decide)]
    omega
  · rw [if_neg h]
    omega

/-- The scaled recombination candidate is a fixed point of
`Hex.normalizeFactorSign`: its construction applies `Hex.normalizeFactorSign`
as the outermost operation, so the candidate already has nonnegative leading
coefficient. -/
private theorem normalizeFactorSign_scaledRecombinationCandidate_eq
    {core : Hex.ZPoly} {d : Hex.LiftData} (T : LiftedFactorSubset d) :
    Hex.normalizeFactorSign (scaledRecombinationCandidate core d T) =
      scaledRecombinationCandidate core d T := by
  have hnonneg :
      0 ≤ Hex.DensePoly.leadingCoeff (scaledRecombinationCandidate core d T) := by
    show 0 ≤ Hex.DensePoly.leadingCoeff (Hex.normalizeFactorSign _)
    exact leadingCoeff_normalizeFactorSign_nonneg _
  unfold Hex.normalizeFactorSign
  have hnot :
      ¬ Hex.DensePoly.leadingCoeff (scaledRecombinationCandidate core d T) < 0 := by
    omega
  rw [if_neg hnot]

/-- Abstract-bound variant of `zpoly_primitive_scaledRecombinationCandidate`:
takes `B' : Nat`,
`hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  The body mirrors the
original but invokes `size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound`
with the abstract `B'` rather than `defaultFactorCoeffBound core`.  The
original core-shape theorem is a wrapper around this variant. -/
private theorem zpoly_primitive_scaledRecombinationCandidate_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (_hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    Hex.ZPoly.Primitive (scaledRecombinationCandidate core d T) := by
  -- Inline the size machinery from
  -- `natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum` to obtain
  -- nonzeroness of the inner centred lift, then chase content through the
  -- two outer normalisation operations.
  set lp := liftedFactorProduct d T with hlp_def
  have hlp_monic : Hex.DensePoly.Monic lp :=
    liftedFactorProduct_monic d T (fun i _ => hd_liftedFactor_monic i)
  have hlp_size_pos : 0 < lp.size := zpoly_size_pos_of_monic hlp_monic
  have hcore_lc_ne : Hex.DensePoly.leadingCoeff core ≠ (0 : Int) :=
    ne_of_gt hcore_lc_pos
  have hslp_size :
      (scaledLiftedFactorProduct core d T).size = lp.size := by
    unfold scaledLiftedFactorProduct
    exact size_scale_eq_of_monic_of_ne_zero hcore_lc_ne hlp_monic
  have hslp_lc :
      Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T) =
        Hex.DensePoly.leadingCoeff core := by
    unfold scaledLiftedFactorProduct
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero
      (Hex.DensePoly.leadingCoeff core) lp hcore_lc_ne,
      show Hex.DensePoly.leadingCoeff lp = (1 : Int) from hlp_monic]
    ring
  have hslp_lc_pos :
      0 < Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T) := by
    rw [hslp_lc]; exact hcore_lc_pos
  have hslp_lc_bound :
      (Hex.DensePoly.leadingCoeff (scaledLiftedFactorProduct core d T)).natAbs ≤
        B' := by
    rw [hslp_lc]; exact hcore_lc_le
  have hcl_size :
      (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
          (d.p ^ d.k)).size =
        (scaledLiftedFactorProduct core d T).size :=
    size_centeredLiftPoly_eq_of_pos_leadingCoeff_bound
      hslp_lc_pos hslp_lc_bound hprecision
  have hcl_size_pos :
      0 < (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
          (d.p ^ d.k)).size := by
    rw [hcl_size, hslp_size]; exact hlp_size_pos
  have hcl_ne :
      Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T) (d.p ^ d.k) ≠
        0 := by
    intro h
    have h0 :
        (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)).size = 0 := by
      rw [h]; rfl
    omega
  have hcl_content_ne :
      Hex.ZPoly.content
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k)) ≠ (0 : Int) := by
    intro hcontent
    apply hcl_ne
    have hpart_zero :
        Hex.ZPoly.primitivePart
            (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
              (d.p ^ d.k)) = 0 := by
      simpa [Hex.ZPoly.primitivePart] using
        Hex.DensePoly.primitivePart_eq_zero_of_content_eq_zero
          (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T)
            (d.p ^ d.k))
          (by simpa [Hex.ZPoly.content] using hcontent)
    have hreconstruct := Hex.ZPoly.content_mul_primitivePart
      (Hex.centeredLiftPoly (scaledLiftedFactorProduct core d T) (d.p ^ d.k))
    rw [hcontent, hpart_zero] at hreconstruct
    have hzero_scale :
        Hex.DensePoly.scale (0 : Int) (0 : Hex.ZPoly) = (0 : Hex.ZPoly) := by
      apply Hex.DensePoly.ext_coeff
      intro n
      rw [Hex.DensePoly.coeff_scale (R := Int) (0 : Int) (0 : Hex.ZPoly) n
        (Int.zero_mul 0), Hex.DensePoly.coeff_zero]
      exact Int.zero_mul _
    rw [hzero_scale] at hreconstruct
    exact hreconstruct.symm
  show Hex.ZPoly.content (scaledRecombinationCandidate core d T) = 1
  unfold scaledRecombinationCandidate
  rw [content_normalizeFactorSign_eq]
  exact Hex.ZPoly.primitivePart_primitive _ hcl_content_ne

/-- The scaled recombination candidate is primitive whenever `core` is nonzero
and has positive leading coefficient (so the centred-lift size machinery
applies). The construction `normalizeFactorSign ∘ primitivePart` gives content
`1` whenever the inner centred lift is nonzero, and `normalizeFactorSign`
preserves content.

Thin wrapper over `zpoly_primitive_scaledRecombinationCandidate_of_bound` that
instantiates `B' := defaultFactorCoeffBound core` and discharges
`hcore_lc_le` via `defaultFactorCoeffBound_valid core hcore_ne core
(dvd_refl core) (core.size - 1)`. -/
private theorem zpoly_primitive_scaledRecombinationCandidate
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (T : LiftedFactorSubset d) :
    Hex.ZPoly.Primitive (scaledRecombinationCandidate core d T) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact zpoly_primitive_scaledRecombinationCandidate_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core) hcore_lc_le
    hcore_ne hcore_lc_pos hd_liftedFactor_monic hprecision T

/-- Abstract-bound variant of
`exists_representingSubset_of_mem_normalizedFactors_scaledRecombinationCandidate_of_primitive_pos_lc_core`:
takes a universal bound `B'` valid on every normalised `Polynomial ℤ`
factor of the scaled recombination candidate, the leading-coefficient
bound `hcore_lc_le : (DensePoly.leadingCoeff core).natAbs ≤ B'`, and the
precision hypothesis `2 * B' < d.p ^ d.k`, in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.

Unlike the unscaled siblings, the abstract bound is consumed at two
call sites here: at
`zpoly_primitive_scaledRecombinationCandidate_of_bound` (precision is
non-vestigial — the centred-lift size machinery for the scaled lifted
product is keyed off `hprecision`) and at
`representingSubset_subset_of_dvd_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`
(precision is vestigial there, threaded purely for API parity). -/
theorem exists_representingSubset_of_mem_normalizedFactors_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (scaledRecombinationCandidate core d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (scaledRecombinationCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ scaledRecombinationCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  obtain ⟨hcand_poly_ne_zero, _hcand_poly_nonunit⟩ :=
    toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord
  have hg_norm :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff'
      (p := gPoly)
      (x := HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T))
      hcand_poly_ne_zero).mp hg_mem
  rcases hg_norm with ⟨hg_irr, hg_normalized, hg_dvd_cand_poly⟩
  let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
  have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
    HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
  have hg_irr_toPoly : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPolynomial]
    exact hg_irr
  have hg_dvd_cand : g ∣ scaledRecombinationCandidate core d T := by
    rcases hg_dvd_cand_poly with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    rw [hg_toPolynomial]
    exact hr
  have hcand_dvd_target : scaledRecombinationCandidate core d T ∣ target := by
    have hmul : quotient * scaledRecombinationCandidate core d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hg_dvd_target : g ∣ target := zpoly_dvd_trans hg_dvd_cand hcand_dvd_target
  -- Primitivity of the candidate transports to `Polynomial ℤ`, where it
  -- propagates to every divisor, including `gPoly`.
  have hcand_primitive : Hex.ZPoly.Primitive
      (scaledRecombinationCandidate core d T) :=
    zpoly_primitive_scaledRecombinationCandidate_of_bound
      B' hcore_lc_le hcore_ne hcore_lc_pos hd_liftedFactor_monic
      hprecision T
  have hcand_poly_primitive :
      (HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T)).IsPrimitive :=
    toPolynomial_isPrimitive_of_zpoly_primitive_basic hcand_primitive
  have hg_poly_primitive : gPoly.IsPrimitive :=
    isPrimitive_of_dvd hcand_poly_primitive hg_dvd_cand_poly
  have hg_content : Hex.ZPoly.content g = 1 := by
    have : (HexPolyZMathlib.toPolynomial g).IsPrimitive := by
      rw [hg_toPolynomial]; exact hg_poly_primitive
    exact zpoly_primitive_of_toPolynomial_isPrimitive_basic this
  -- Leading coefficient of `gPoly` is nonnegative because it is normalised.
  have hg_lead_nonneg : 0 ≤ gPoly.leadingCoeff := by
    have hlead_normalized :
        normalize gPoly.leadingCoeff = gPoly.leadingCoeff := by
      have hlead := congrArg Polynomial.leadingCoeff hg_normalized
      rwa [Polynomial.leadingCoeff_normalize] at hlead
    exact Int.nonneg_of_normalize_eq_self hlead_normalized
  have hg_norm_sign : Hex.normalizeFactorSign g = g := by
    have hg_hex_lc_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff g := by
      have hlc :
          (HexPolyZMathlib.toPolynomial g).leadingCoeff =
            Hex.DensePoly.leadingCoeff g :=
        HexPolyMathlib.leadingCoeff_toPolynomial g
      rw [← hlc, hg_toPolynomial]
      exact hg_lead_nonneg
    unfold Hex.normalizeFactorSign
    have hnot : ¬ Hex.DensePoly.leadingCoeff g < 0 := by omega
    rw [if_neg hnot]
  obtain ⟨S_g, hSJ, hSrep⟩ :=
    hpartition.exists_subset hg_irr_toPoly hg_dvd_target
  have hST : S_g ⊆ T :=
    representingSubset_subset_of_dvd_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
      B' (hvalid g (by rw [hg_toPolynomial]; exact hg_mem))
      hcore_ne hcore_primitive hcore_lc_pos hprecision htarget_dvd_core
      hpartition hTJ hg_irr_toPoly hg_dvd_target hg_content hg_norm_sign
      hg_dvd_cand hSJ hSrep
  exact ⟨g, S_g, hg_toPolynomial, hg_irr_toPoly, hg_dvd_target, hg_dvd_cand,
    hSrep, hSJ, hST, hg_content, hg_norm_sign⟩

/-- Scaled-candidate counterpart of
`exists_representingSubset_of_mem_normalizedFactors_recombinationCandidate_of_primitive_pos_lc_core`.

The scaled recombination candidate is not monic but is primitive with
nonnegative leading coefficient by construction
(`normalizeFactorSign ∘ primitivePart`), so its `Polynomial ℤ` transport is
`IsPrimitive` and `normalize`-fixed. Each normalized irreducible factor `gPoly`
of the transport inherits primitivity (every divisor of a primitive
polynomial is primitive over `Polynomial ℤ`) and has nonnegative leading
coefficient (from `normalize_normalized_factor`), yielding `content g = 1` and
`normalizeFactorSign g = g` for the reified `Hex.ZPoly` factor
`g := ofPolynomial gPoly`.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_representingSubset_of_mem_normalizedFactors_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`:
each normalised factor `g` of the candidate divides the candidate, which
divides `target` (via `hquot`), which divides `core` (via
`htarget_dvd_core`), so `defaultFactorCoeffBound_valid` discharges the
universal bound hypothesis; the core leading-coefficient bound is
discharged via the self-divisibility instance of the same lemma. -/
theorem exists_representingSubset_of_mem_normalizedFactors_scaledRecombinationCandidate_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (scaledRecombinationCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient)
    {gPoly : Polynomial ℤ}
    (hg_mem : gPoly ∈ UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T))) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      HexPolyZMathlib.toPolynomial g = gPoly ∧
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ scaledRecombinationCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧
      S_g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hcand_dvd_target :
      scaledRecombinationCandidate core d T ∣ target := by
    have hmul : quotient * scaledRecombinationCandidate core d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core :
      scaledRecombinationCandidate core d T ∣ core :=
    zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
  refine exists_representingSubset_of_mem_normalizedFactors_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (fun g hg_mem' => ?_)
    hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos
    hd_liftedFactor_monic hprecision hpartition htarget_dvd_core hTJ
    hrecord hquot hg_mem
  -- Discharge `hvalid` for arbitrary normalised factor `g` of the
  -- scaled candidate by chaining `g ∣ candidate ∣ target ∣ core` and
  -- invoking `defaultFactorCoeffBound_valid`.
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem'
  have hg_dvd_cand : g ∣ scaledRecombinationCandidate core d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Abstract-bound variant of
`exists_mem_representedSubset_of_degree_cover_of_scaledRecombinationCandidate_of_primitive_pos_lc_core`:
takes `B' : Nat`, a per-factor coefficient bound
`hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B'`, the leading-coefficient
bound `hcore_lc_le : (leadingCoeff core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint. The proof mirrors the
core-shape original but invokes the `_of_bound` siblings
`natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum_of_bound` for the
candidate-side natDegree decomposition and
`natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound`
for the per-factor `natDegree` identity. -/
theorem exists_mem_representedSubset_of_degree_cover_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ scaledRecombinationCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (hvalid : ∀ g ∈ gs, ∀ i, (g.coeff i).natAbs ≤ B')
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial
          (scaledRecombinationCandidate core d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  set f : LiftedFactorIndex d → Nat :=
    fun j => (HexPolyZMathlib.toPolynomial (liftedFactor d j)).natDegree
  have h_cand_eq :
      (HexPolyZMathlib.toPolynomial
          (scaledRecombinationCandidate core d T)).natDegree =
        ∑ j ∈ T, f j :=
    natDegree_toPolynomial_scaledRecombinationCandidate_eq_sum_of_bound
      B' hcore_ne hcore_lc_pos hd_liftedFactor_monic hcore_lc_le hprecision T
  have h_g_eq : ∀ g ∈ gs,
      (HexPolyZMathlib.toPolynomial g).natDegree = ∑ j ∈ S_of g, f j := by
    intro g hg
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, _, _, hg_cont, hg_norm⟩ := h_each g hg
    have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd htarget_dvd_core
    exact natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
      B' (hvalid g hg) hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos
      hd_liftedFactor_monic hg_dvd_core hg_irr hg_cont hg_norm hg_rep hprecision
  have h_pwdisj : Set.PairwiseDisjoint (↑gs : Set Hex.ZPoly) S_of := by
    intro g hg h hh hgh
    obtain ⟨hg_irr, hg_dvd, _, hg_rep, hg_SJ, _, _, _⟩ := h_each g hg
    obtain ⟨hh_irr, hh_dvd, _, hh_rep, hh_SJ, _, _, _⟩ := h_each h hh
    exact hpartition.pairwise_disjoint hg_irr hg_dvd hg_SJ hg_rep
      hh_irr hh_dvd hh_SJ hh_rep
      (h_pairwise_not_associated hg hh hgh)
  have h_sub : gs.biUnion S_of ⊆ T := by
    intro j hj
    obtain ⟨g, hg, hjg⟩ := Finset.mem_biUnion.mp hj
    exact (h_each g hg).2.2.2.2.2.1 hjg
  have h_sum_eq :
      ∑ j ∈ T, f j = ∑ j ∈ gs.biUnion S_of, f j := by
    have h_step : ∑ j ∈ gs.biUnion S_of, f j = ∑ g ∈ gs, ∑ j ∈ S_of g, f j :=
      Finset.sum_biUnion h_pwdisj
    rw [h_step, ← h_cand_eq, h_degree_total]
    exact Finset.sum_congr rfl h_g_eq
  have h_zero : ∑ j ∈ T \ gs.biUnion S_of, f j = 0 := by
    have h_split :
        (∑ j ∈ T \ gs.biUnion S_of, f j) +
            (∑ j ∈ gs.biUnion S_of, f j) =
          ∑ j ∈ T, f j :=
      Finset.sum_sdiff h_sub
    omega
  have h_empty : T \ gs.biUnion S_of = ∅ := by
    by_contra hne
    obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have h_le : f j ≤ ∑ k ∈ T \ gs.biUnion S_of, f k :=
      Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) hj
    have h_pos : 0 < f j := hd_liftedFactor_natDegree_pos j
    omega
  intro i hi
  have hi_in_bU : i ∈ gs.biUnion S_of := by
    by_contra h_not
    have h_in_sdiff : i ∈ T \ gs.biUnion S_of :=
      Finset.mem_sdiff.mpr ⟨hi, h_not⟩
    rw [h_empty] at h_in_sdiff
    exact Finset.notMem_empty _ h_in_sdiff
  exact Finset.mem_biUnion.mp hi_in_bU

/-- Scaled-candidate counterpart of
`exists_mem_representedSubset_of_degree_cover_of_primitive_pos_lc_core`.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_mem_representedSubset_of_degree_cover_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`:
the per-factor `hvalid` is discharged via the divisor chain `g ∣ target ∣ core`
plus `defaultFactorCoeffBound_valid`; `hcore_lc_le` is discharged via
`defaultFactorCoeffBound_valid core hcore_ne core hcore_dvd_self (core.size - 1)`
together with `leadingCoeff_eq_coeff_last`. -/
theorem exists_mem_representedSubset_of_degree_cover_of_scaledRecombinationCandidate_of_primitive_pos_lc_core
    {core target : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (_hTJ : T ⊆ J)
    (gs : Finset Hex.ZPoly)
    (S_of : Hex.ZPoly → LiftedFactorSubset d)
    (h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ scaledRecombinationCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g)
    (h_pairwise_not_associated :
      ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
        ¬ Associated (HexPolyZMathlib.toPolynomial g)
          (HexPolyZMathlib.toPolynomial h))
    (h_degree_total :
      (HexPolyZMathlib.toPolynomial
          (scaledRecombinationCandidate core d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree) :
    ∀ {i : LiftedFactorIndex d}, i ∈ T → ∃ g ∈ gs, i ∈ S_of g := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hvalid : ∀ g ∈ gs, ∀ i,
      (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound core := by
    intro g hg i
    obtain ⟨_, hg_dvd_target, _, _, _, _, _, _⟩ := h_each g hg
    have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_target htarget_dvd_core
    exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core i
  intro i hi
  exact exists_mem_representedSubset_of_degree_cover_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le
    hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
    htarget_dvd_core _hTJ gs S_of h_each hvalid
    h_pairwise_not_associated h_degree_total hi

/-- Abstract-bound variant of
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_scaledRecombinationCandidate_of_primitive_pos_lc_core`:
takes `B' : Nat`, the universal coefficient bound `hvalid` over the
candidate's normalised factors, the leading-coefficient bound
`hcore_lc_le`, and `hprecision : 2 * B' < d.p ^ d.k` in place of the
core-shape `defaultFactorCoeffBound core` precision constraint. The
proof body mirrors the original (now-wrapper) with two call-site
substitutions: the per-normalised-factor lemma
(`exists_representingSubset_of_mem_normalizedFactors_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`)
and the final degree-cover application
(`exists_mem_representedSubset_of_degree_cover_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`)
both use their `_of_bound` siblings, threaded with `B'`,
`hcore_lc_le`, `hvalid`, and `hprecision`. -/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (scaledRecombinationCandidate core d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (scaledRecombinationCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ scaledRecombinationCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcand_poly_ne_zero :
      HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T) ≠
        0 :=
    (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
  have hcand_ne : scaledRecombinationCandidate core d T ≠ 0 := by
    intro h
    apply hcand_poly_ne_zero
    rw [h]
    exact HexPolyMathlib.toPolynomial_zero
  have hcand_squarefree :
      Squarefree
        (HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T)) :=
    toPolynomial_scaledRecombinationCandidate_squarefree hpartition hquot
  set normFactors :=
    UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T))
    with hnf_def
  have hnf_nodup : normFactors.Nodup :=
    (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
      hcand_poly_ne_zero).mp hcand_squarefree
  -- The candidate's `Polynomial ℤ` transport is `normalize`-fixed because the
  -- candidate is in `normalizeFactorSign`-normal form by construction.
  have hcand_normFix :
      Hex.normalizeFactorSign (scaledRecombinationCandidate core d T) =
        scaledRecombinationCandidate core d T :=
    normalizeFactorSign_scaledRecombinationCandidate_eq T
  have hcand_normalize_eq :
      normalize
          (HexPolyZMathlib.toPolynomial
            (scaledRecombinationCandidate core d T)) =
        HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T) :=
    normalize_toPolynomial_of_normalizeFactorSign_id hcand_ne hcand_normFix
  have hnf_prod_eq :
      normFactors.prod =
        HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T) := by
    rw [UniqueFactorizationMonoid.prod_normalizedFactors_eq hcand_poly_ne_zero,
      hcand_normalize_eq]
  have bridge_for : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈ normFactors →
      ∃ S_g : LiftedFactorSubset d,
        Irreducible (HexPolyZMathlib.toPolynomial g) ∧
        g ∣ target ∧
        g ∣ scaledRecombinationCandidate core d T ∧
        RepresentsIntegerFactorAtLift core d g S_g ∧
        S_g ⊆ J ∧
        S_g ⊆ T ∧
        Hex.ZPoly.content g = 1 ∧
        Hex.normalizeFactorSign g = g := by
    intro g hgPoly
    obtain ⟨g', S_g, h_eq, h_irr, h_dvd_t, h_dvd_c, h_rep, h_SJ, h_ST,
        h_cont, h_norm⟩ :=
      exists_representingSubset_of_mem_normalizedFactors_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
        B' hvalid hcore_lc_le hcore_ne hcore_primitive hcore_lc_pos
        hd_liftedFactor_monic hprecision hpartition htarget_dvd_core hTJ
        hrecord hquot hgPoly
    have hg_eq : g' = g := by
      have := congrArg HexPolyZMathlib.ofPolynomial h_eq
      simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
    refine ⟨S_g, ?_, ?_, ?_, ?_, h_SJ, h_ST, ?_, ?_⟩
    · rw [← hg_eq]; exact h_irr
    · rw [← hg_eq]; exact h_dvd_t
    · rw [← hg_eq]; exact h_dvd_c
    · rw [← hg_eq]; exact h_rep
    · rw [← hg_eq]; exact h_cont
    · rw [← hg_eq]; exact h_norm
  let S_of : Hex.ZPoly → LiftedFactorSubset d := fun g =>
    if h : HexPolyZMathlib.toPolynomial g ∈ normFactors then
      Classical.choose (bridge_for g h)
    else (∅ : LiftedFactorSubset d)
  let gs : Finset Hex.ZPoly :=
    normFactors.toFinset.image HexPolyZMathlib.ofPolynomial
  have mem_gs : ∀ {g : Hex.ZPoly},
      g ∈ gs ↔ HexPolyZMathlib.toPolynomial g ∈ normFactors := by
    intro g
    refine ⟨?_, ?_⟩
    · intro hg
      rcases Finset.mem_image.mp hg with ⟨gPoly, hgPoly_mem, h_eq⟩
      rw [Multiset.mem_toFinset] at hgPoly_mem
      rw [← h_eq, HexPolyZMathlib.toPolynomial_ofPolynomial]
      exact hgPoly_mem
    · intro hg
      refine Finset.mem_image.mpr ⟨HexPolyZMathlib.toPolynomial g, ?_, ?_⟩
      · exact Multiset.mem_toFinset.mpr hg
      · exact HexPolyZMathlib.ofPolynomial_toPolynomial g
  have h_each : ∀ g ∈ gs,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ target ∧
      g ∣ scaledRecombinationCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g (S_of g) ∧
      S_of g ⊆ J ∧
      S_of g ⊆ T ∧
      Hex.ZPoly.content g = 1 ∧
      Hex.normalizeFactorSign g = g := by
    intro g hg
    have hg_norm := mem_gs.mp hg
    have hS_of_eq :
        S_of g = Classical.choose (bridge_for g hg_norm) := by
      simp [S_of, dif_pos hg_norm]
    have hspec := Classical.choose_spec (bridge_for g hg_norm)
    rw [hS_of_eq]
    exact hspec
  have h_pairwise : ∀ ⦃g h : Hex.ZPoly⦄, g ∈ gs → h ∈ gs → g ≠ h →
      ¬ Associated (HexPolyZMathlib.toPolynomial g)
        (HexPolyZMathlib.toPolynomial h) := by
    intro g h hg_in hh_in hgh hassoc
    have hg_norm := mem_gs.mp hg_in
    have hh_norm := mem_gs.mp hh_in
    have hg_eq :
        normalize (HexPolyZMathlib.toPolynomial g) =
          HexPolyZMathlib.toPolynomial g :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hg_norm
    have hh_eq :
        normalize (HexPolyZMathlib.toPolynomial h) =
          HexPolyZMathlib.toPolynomial h :=
      UniqueFactorizationMonoid.normalize_normalized_factor _ hh_norm
    have hpoly_eq :
        HexPolyZMathlib.toPolynomial g = HexPolyZMathlib.toPolynomial h := by
      rw [← hg_eq, ← hh_eq]
      exact normalize_eq_normalize hassoc.dvd hassoc.symm.dvd
    apply hgh
    have := congrArg HexPolyZMathlib.ofPolynomial hpoly_eq
    simpa [HexPolyZMathlib.ofPolynomial_toPolynomial] using this
  have h_degree_total :
      (HexPolyZMathlib.toPolynomial
          (scaledRecombinationCandidate core d T)).natDegree =
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree := by
    have h_image_sum :
        ∑ g ∈ gs, (HexPolyZMathlib.toPolynomial g).natDegree =
          ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree := by
      show ∑ g ∈ normFactors.toFinset.image HexPolyZMathlib.ofPolynomial,
          (HexPolyZMathlib.toPolynomial g).natDegree =
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree
      rw [Finset.sum_image]
      · refine Finset.sum_congr rfl ?_
        intro gPoly _
        simp
      · intro a _ b _ heq
        have := congrArg HexPolyZMathlib.toPolynomial heq
        simpa using this
    have h_toFinset_sum :
        ∑ gPoly ∈ normFactors.toFinset, gPoly.natDegree =
          (normFactors.map Polynomial.natDegree).sum := by
      change (normFactors.toFinset.val.map Polynomial.natDegree).sum =
        (normFactors.map Polynomial.natDegree).sum
      rw [Multiset.toFinset_val, hnf_nodup.dedup]
    rw [h_image_sum, h_toFinset_sum, ← hnf_prod_eq,
      Polynomial.natDegree_multiset_prod _
        (UniqueFactorizationMonoid.zero_notMem_normalizedFactors _)]
  obtain ⟨g, hg_in_gs, hi_in_Sg⟩ :=
    exists_mem_representedSubset_of_degree_cover_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
      B' hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
      htarget_dvd_core hTJ gs S_of h_each
      (fun g hg => hvalid g (mem_gs.mp hg))
      h_pairwise h_degree_total hi
  have _hg_norm := mem_gs.mp hg_in_gs
  obtain ⟨h_irr, _, h_dvd_c, h_rep, h_SJ, _, _, _⟩ := h_each g hg_in_gs
  exact ⟨g, S_of g, h_irr, h_dvd_c, h_rep, h_SJ, hi_in_Sg⟩

/-- Scaled-candidate counterpart of
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_primitive_pos_lc_core`.

The scaled candidate is primitive (not monic) with nonnegative leading
coefficient by construction. This is the `defaultFactorCoeffBound core`-
instantiated thin wrapper for
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`:
each normalised factor `g` of the candidate divides the candidate, which
divides `target` (via `hquot`), which divides `core` (via
`htarget_dvd_core`), so `defaultFactorCoeffBound_valid` discharges the
universal bound hypothesis; the core leading-coefficient bound is
discharged via the self-divisibility instance of the same lemma combined
with `leadingCoeff_eq_coeff_last`. -/
theorem mem_T_iff_exists_irreducibleFactor_representingSubset_of_scaledRecombinationCandidate_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (scaledRecombinationCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (g : Hex.ZPoly) (S_g : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ scaledRecombinationCandidate core d T ∧
      RepresentsIntegerFactorAtLift core d g S_g ∧
      S_g ⊆ J ∧ i ∈ S_g := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hcand_dvd_target :
      scaledRecombinationCandidate core d T ∣ target := by
    have hmul : quotient * scaledRecombinationCandidate core d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core :
      scaledRecombinationCandidate core d T ∣ core :=
    zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
  refine mem_T_iff_exists_irreducibleFactor_representingSubset_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (fun g hg_mem => ?_)
    hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
    hrecord hquot hi
  -- Discharge `hvalid` for arbitrary normalised factor `g` of the
  -- scaled candidate by chaining `g ∣ candidate ∣ target ∣ core` and
  -- invoking `defaultFactorCoeffBound_valid`.
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
  have hg_dvd_cand : g ∣ scaledRecombinationCandidate core d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Abstract-bound variant of
`exists_representingSubset_of_mem_T_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core`:
takes `B' : Nat`, the leading-coefficient bound `hcore_lc_le`, the
universal coefficient bound `hvalid` over the candidate's normalised
factors, and `hprecision : 2 * B' < d.p ^ d.k` in place of the
core-shape `defaultFactorCoeffBound core` precision constraint. The
proof body mirrors the original (now-wrapper) with one call-site
substitution: the per-T membership-equivalence lemma
`mem_T_iff_exists_irreducibleFactor_representingSubset_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`
is threaded with `B'`, `hcore_lc_le`, `hvalid`, and `hprecision`. -/
theorem exists_representingSubset_of_mem_T_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (scaledRecombinationCandidate core d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (scaledRecombinationCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ scaledRecombinationCandidate core d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  obtain ⟨f, S, hf_irr, hf_dvd_candidate, hrep, hSJ, hiS⟩ :=
    mem_T_iff_exists_irreducibleFactor_representingSubset_of_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
      B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision hpartition
      htarget_dvd_core hTJ hrecord hquot hi
  have hcand_dvd_target :
      scaledRecombinationCandidate core d T ∣ target := by
    have hmul : quotient * scaledRecombinationCandidate core d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hf_dvd_target : f ∣ target := zpoly_dvd_trans hf_dvd_candidate hcand_dvd_target
  exact ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_candidate, hSJ, hiS, hrep⟩

/-- Scaled-candidate counterpart of
`exists_representingSubset_of_mem_T_of_recombinationCandidate_dvd_of_primitive_pos_lc_core`.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`exists_representingSubset_of_mem_T_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`:
the universal coefficient bound is discharged from the divisor chain
`g ∣ candidate ∣ target ∣ core`, and the leading-coefficient bound is
discharged via the self-divisibility instance of
`defaultFactorCoeffBound_valid` combined with `leadingCoeff_eq_coeff_last`. -/
theorem exists_representingSubset_of_mem_T_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (scaledRecombinationCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient)
    {i : LiftedFactorIndex d} (hi : i ∈ T) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      f ∣ scaledRecombinationCandidate core d T ∧
      S ⊆ J ∧
      i ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hcand_dvd_target :
      scaledRecombinationCandidate core d T ∣ target := by
    have hmul : quotient * scaledRecombinationCandidate core d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core :
      scaledRecombinationCandidate core d T ∣ core :=
    zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
  refine exists_representingSubset_of_mem_T_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (fun g hg_mem => ?_)
    hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core hTJ
    hrecord hquot hi
  -- Discharge `hvalid` for arbitrary normalised factor `g` of the
  -- scaled candidate by chaining `g ∣ candidate ∣ core` and invoking
  -- `defaultFactorCoeffBound_valid`.
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
  have hg_dvd_cand : g ∣ scaledRecombinationCandidate core d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Abstract-bound variant of
`coverAtMin_representingSubset_subset_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core`:
takes `B' : Nat`, the leading-coefficient bound `hcore_lc_le`, the
universal coefficient bound `hvalid` over the candidate's normalised
factors, and `hprecision : 2 * B' < d.p ^ d.k` in place of the
core-shape `defaultFactorCoeffBound core` precision constraint. The
proof body mirrors the original (now-wrapper) with three call-site
substitutions: the cover-extraction lemma
`exists_representingSubset_of_mem_T_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`,
the represented-factor primitivity capstone
`representsIntegerFactorAtLift_primitive_of_bound`, and the support
containment lemma
`representingSubset_subset_of_dvd_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound`
all consume the abstract bound. The single-factor bound for the
extracted cover witness `f` is derived from `hvalid` applied to the
normalised factor associated with `HexPolyZMathlib.toPolynomial f`
(which exists because `f` is irreducible and divides the candidate);
the unit witnessing the association is a constant `Polynomial ℤ` unit
(`Polynomial.C c` for `c ∈ {±1}`), so the `natAbs` of each coefficient
is preserved across the association. -/
theorem coverAtMin_representingSubset_subset_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly,
      HexPolyZMathlib.toPolynomial g ∈
        UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (scaledRecombinationCandidate core d T)) →
      ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (scaledRecombinationCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  obtain ⟨f, S, hf_irr, hf_dvd_target, hf_dvd_cand, hSJ, hmin_in_S, hrep⟩ :=
    exists_representingSubset_of_mem_T_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
      B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision
      hpartition htarget_dvd_core hTJ hrecord hquot hmin_in_T
  -- Derive the single-factor bound `hvalid_f : ∀ i, (f.coeff i).natAbs ≤ B'`
  -- by applying `hvalid` to the normalised factor of the candidate
  -- associated with `toPolynomial f`. The unit witnessing the association
  -- is a constant polynomial `C c` with `c ∈ {±1}`, so `natAbs` of each
  -- coefficient is preserved.
  have hvalid_f : ∀ i, (f.coeff i).natAbs ≤ B' := by
    have hcand_poly_ne_zero :
        HexPolyZMathlib.toPolynomial (scaledRecombinationCandidate core d T) ≠
          0 :=
      (toPolynomial_ne_zero_and_not_isUnit_of_shouldRecord hrecord).1
    have hf_poly_dvd :
        HexPolyZMathlib.toPolynomial f ∣
          HexPolyZMathlib.toPolynomial
            (scaledRecombinationCandidate core d T) := by
      rcases hf_dvd_cand with ⟨r, hr⟩
      refine ⟨HexPolyZMathlib.toPolynomial r, ?_⟩
      rw [← HexPolyZMathlib.toPolynomial_mul, hr]
    obtain ⟨gPoly, hg_mem, hg_assoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_normalizedFactors_of_dvd
        hcand_poly_ne_zero hf_irr hf_poly_dvd
    let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
    have hg_toPoly : HexPolyZMathlib.toPolynomial g = gPoly :=
      HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
    have hg_bound : ∀ i, (g.coeff i).natAbs ≤ B' :=
      hvalid g (by rw [hg_toPoly]; exact hg_mem)
    obtain ⟨u, hu⟩ := hg_assoc
    obtain ⟨c, hc_unit, hcu⟩ := Polynomial.isUnit_iff.mp u.isUnit
    have hc_abs_one : c.natAbs = 1 := Int.isUnit_iff_natAbs_eq.mp hc_unit
    intro i
    have hg_coeff : g.coeff i = gPoly.coeff i := by
      have := HexPolyZMathlib.coeff_toPolynomial g i
      rw [hg_toPoly] at this
      exact this.symm
    have hgPoly_coeff_f : gPoly.coeff i = f.coeff i * c := by
      have hmul : (HexPolyZMathlib.toPolynomial f * Polynomial.C c).coeff i =
          (HexPolyZMathlib.toPolynomial f).coeff i * c :=
        Polynomial.coeff_mul_C _ _ _
      rw [← hu, ← hcu, hmul, HexPolyZMathlib.coeff_toPolynomial]
    have hbound := hg_bound i
    rw [hg_coeff, hgPoly_coeff_f, Int.natAbs_mul, hc_abs_one,
      Nat.mul_one] at hbound
    exact hbound
  obtain ⟨hf_primitive, _hf_lc_pos⟩ :=
    representsIntegerFactorAtLift_primitive_of_bound
      B' hvalid_f hcore_lc_le hcore_ne hcore_primitive
      hcore_lc_pos hd_liftedFactor_monic hf_dvd_target
      htarget_dvd_core hrep hprecision
  have hf_content : Hex.ZPoly.content f = 1 := hf_primitive
  have hf_norm_sign : Hex.normalizeFactorSign f = f := by
    unfold Hex.normalizeFactorSign
    have hnot : ¬ Hex.DensePoly.leadingCoeff f < 0 := by omega
    rw [if_neg hnot]
  have hST : S ⊆ T :=
    representingSubset_subset_of_dvd_scaledRecombinationCandidate_of_primitive_pos_lc_core_of_bound
      B' hvalid_f hcore_ne hcore_primitive hcore_lc_pos hprecision
      htarget_dvd_core hpartition hTJ hf_irr hf_dvd_target hf_content
      hf_norm_sign hf_dvd_cand hSJ hrep
  exact ⟨f, S, hf_irr, hf_dvd_target, hSJ, hmin_in_S, hrep, hST⟩

/-- Scaled-candidate counterpart of
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core`.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`coverAtMin_representingSubset_subset_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`:
the universal coefficient bound is discharged from the divisor chain
`g ∣ candidate ∣ core`, and the leading-coefficient bound is discharged
via the self-divisibility instance of `defaultFactorCoeffBound_valid`
combined with `leadingCoeff_eq_coeff_last`.

This is the scaled cover-at-min surface consumed by the scaled prefix-none
lemma for the primitive recursive recombination coverage proof
(#4647 / #4737 / #4738). It supplies the single cover factor whose
representing subset contains `J.min' hne` and is contained in `T`. -/
theorem coverAtMin_representingSubset_subset_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core
    {core target quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hne : J.Nonempty)
    (hmin_in_T : J.min' hne ∈ T)
    (hrecord :
      Hex.shouldRecordPolynomialFactor
          (scaledRecombinationCandidate core d T) = true)
    (hquot :
      Hex.exactQuotient? target (scaledRecombinationCandidate core d T) =
        some quotient) :
    ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧
      f ∣ target ∧
      S ⊆ J ∧ J.min' hne ∈ S ∧
      RepresentsIntegerFactorAtLift core d f S ∧
      S ⊆ T := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  have hcand_dvd_target :
      scaledRecombinationCandidate core d T ∣ target := by
    have hmul : quotient * scaledRecombinationCandidate core d T = target :=
      Hex.exactQuotient?_product hquot
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hcand_dvd_core :
      scaledRecombinationCandidate core d T ∣ core :=
    zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
  refine coverAtMin_representingSubset_subset_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (fun g hg_mem => ?_)
    hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core
    hTJ hne hmin_in_T hrecord hquot
  -- Discharge `hvalid` for arbitrary normalised factor `g` of the
  -- scaled candidate by chaining `g ∣ candidate ∣ core` and invoking
  -- `defaultFactorCoeffBound_valid`.
  have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
      HexPolyZMathlib.toPolynomial
        (scaledRecombinationCandidate core d T) :=
    UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
  have hg_dvd_cand : g ∣ scaledRecombinationCandidate core d T := by
    rcases hg_poly_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr
  have hg_dvd_core : g ∣ core := zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
  exact defaultFactorCoeffBound_valid core hcore_ne g hg_dvd_core

/-- Abstract-bound variant of `not_represents_empty_of_irreducible_dvd_core`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Delegates to
`centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound`
for the recovery equation. -/
private theorem not_represents_empty_of_irreducible_dvd_core_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hfactor_dvd : factor ∣ core)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hprecision : 2 * B' < d.p ^ d.k) :
    ¬ RepresentsIntegerFactorAtLift core d factor
      (∅ : LiftedFactorSubset d) := by
  intro hrep
  -- Recovery equation: `centeredLiftPoly (scaledLiftedFactorProduct core d ∅) _ = factor`.
  have hrec :
      Hex.centeredLiftPoly
          (scaledLiftedFactorProduct core d (∅ : LiftedFactorSubset d))
          (d.p ^ d.k) = factor :=
    centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
      B' hvalid hrep hprecision
  -- `liftedFactorProduct d ∅ = 1`: foldl on the empty `toList`.
  have hempty_lp :
      liftedFactorProduct d (∅ : LiftedFactorSubset d) = (1 : Hex.ZPoly) := by
    unfold liftedFactorProduct
    simp
  -- Under monicness of `core`, the scale factor is `1`, so the scaled product
  -- collapses to `1`.
  have hlead : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  have hscaled :
      scaledLiftedFactorProduct core d (∅ : LiftedFactorSubset d) =
        (1 : Hex.ZPoly) := by
    unfold scaledLiftedFactorProduct
    rw [hlead, hempty_lp]
    exact densePoly_scale_one_int (1 : Hex.ZPoly)
  rw [hscaled] at hrec
  -- `factor ∣ core` and `core ≠ 0` give `factor ≠ 0`.
  have hfactor_ne : factor ≠ 0 := by
    intro hf
    rcases hfactor_dvd with ⟨q, hq⟩
    rw [hf, Hex.DensePoly.zero_mul (S := Int) q] at hq
    exact hcore_ne hq
  -- Promote `0 < d.p^d.k` to `2 ≤ d.p^d.k` via the `d.p^d.k = 1 ⇒ factor = 0`
  -- collapse of the centered lift (matching the pattern used in
  -- `representsIntegerFactorAtLift_monic`).
  have hpk_pos : 0 < d.p ^ d.k := Nat.pow_pos d.p_pos
  have hpk_ge_two : 2 ≤ d.p ^ d.k := by
    rcases Nat.eq_or_lt_of_le
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpk_pos)) with hpk1 | hpk_gt
    · exfalso
      apply hfactor_ne
      apply Hex.DensePoly.ext_coeff
      intro i
      rw [← hrec, Hex.coeff_centeredLiftPoly, ← hpk1,
        Hex.DensePoly.coeff_zero]
      unfold Hex.centeredModNat
      have h1ne : (1 : Nat) ≠ 0 := by decide
      simp only [if_neg h1ne]
      simp
    · omega
  -- `centeredLiftPoly 1 (d.p^d.k) = 1` once `2 ≤ d.p^d.k`.
  have hclpone :
      Hex.centeredLiftPoly (1 : Hex.ZPoly) (d.p ^ d.k) = (1 : Hex.ZPoly) := by
    apply Hex.DensePoly.ext_coeff
    intro i
    rw [Hex.coeff_centeredLiftPoly]
    show Hex.centeredModNat
        ((Hex.DensePoly.C (1 : Int)).coeff i) (d.p ^ d.k) =
      (Hex.DensePoly.C (1 : Int)).coeff i
    rw [Hex.DensePoly.coeff_C]
    by_cases hi : i = 0
    · rw [if_pos hi]
      exact centeredModNat_one_of_two_le hpk_ge_two
    · rw [if_neg hi]
      exact Hex.centeredModNat_zero (d.p ^ d.k)
  rw [hclpone] at hrec
  -- `factor = 1` after transport contradicts irreducibility (1 is a unit).
  have hpolyfactor_eq : HexPolyZMathlib.toPolynomial factor = 1 := by
    rw [← hrec]; exact toPolynomial_one_zpoly
  exact not_irreducible_one (hpolyfactor_eq ▸ hfactor_irr)

/--
An irreducible integer factor of the core is never represented by the empty
subset.  The recovery equation
`centeredLiftPoly (scaledLiftedFactorProduct core d ∅) (d.p^d.k) = factor`
collapses (under a monic core) to `centeredLiftPoly 1 (d.p^d.k) = factor`,
which forces `factor = 1` whenever `d.p^d.k ≥ 2`; the residual `d.p^d.k = 1`
case forces `factor = 0`.  Both outcomes contradict irreducibility of
`HexPolyZMathlib.toPolynomial factor`.

Used by `representedFactor_dvd_recombinationCandidate_of_subset` (#4457) to
close the `S = ∅` subcase of the squarefreeness contradiction.

This is a thin wrapper over
`not_represents_empty_of_irreducible_dvd_core_of_bound` that instantiates
`B' := defaultFactorCoeffBound core` and discharges `hvalid` via
`defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd`.
-/
private theorem not_represents_empty_of_irreducible_dvd_core
    {core factor : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hfactor_dvd : factor ∣ core)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    ¬ RepresentsIntegerFactorAtLift core d factor
      (∅ : LiftedFactorSubset d) :=
  not_represents_empty_of_irreducible_dvd_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd)
    hcore_ne hcore_monic hfactor_dvd hfactor_irr hprecision

/-- Abstract-bound variant of
`not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core`:
takes `B' : Nat`, `hvalid : ∀ i, (factor.coeff i).natAbs ≤ B'`,
`hcore_lc_le : (lc core).natAbs ≤ B'`, and
`hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Since `core` and
`factor` are different polynomials, `hvalid` alone cannot bound the
leading coefficient of `core`; the wrapper discharges `hcore_lc_le`
via `defaultFactorCoeffBound_valid` applied to `core ∣ core`. -/
private theorem not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound
    {core factor : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hvalid : ∀ i, (factor.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hfactor_dvd : factor ∣ core)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hprecision : 2 * B' < d.p ^ d.k) :
    ¬ RepresentsIntegerFactorAtLift core d factor
      (∅ : LiftedFactorSubset d) := by
  intro hrep
  -- Recovery equation: `centeredLiftPoly (scaledLiftedFactorProduct core d ∅) _ = factor`.
  have hrec :
      Hex.centeredLiftPoly
          (scaledLiftedFactorProduct core d (∅ : LiftedFactorSubset d))
          (d.p ^ d.k) = factor :=
    centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery_of_bound
      B' hvalid hrep hprecision
  -- `liftedFactorProduct d ∅ = 1`: foldl on the empty `toList`.
  have hempty_lp :
      liftedFactorProduct d (∅ : LiftedFactorSubset d) = (1 : Hex.ZPoly) := by
    unfold liftedFactorProduct
    simp
  -- The scaled product on the empty subset is the constant `C (lc core)`.
  have hslp_eq_C :
      scaledLiftedFactorProduct core d (∅ : LiftedFactorSubset d) =
        Hex.DensePoly.C (Hex.DensePoly.leadingCoeff core) := by
    apply Hex.DensePoly.ext_coeff
    intro n
    unfold scaledLiftedFactorProduct
    rw [hempty_lp, Hex.DensePoly.coeff_scale (R := Int) _ _ _ (Int.mul_zero _)]
    show Hex.DensePoly.leadingCoeff core *
        (Hex.DensePoly.C (1 : Int)).coeff n =
      (Hex.DensePoly.C (Hex.DensePoly.leadingCoeff core)).coeff n
    rw [Hex.DensePoly.coeff_C, Hex.DensePoly.coeff_C]
    by_cases hn : n = 0
    · rw [if_pos hn, if_pos hn]; ring
    · rw [if_neg hn, if_neg hn]; ring
  -- `factor ∣ core` and `core ≠ 0` give `factor ≠ 0`.
  have hfactor_ne : factor ≠ 0 := by
    intro hf
    rcases hfactor_dvd with ⟨q, hq⟩
    rw [hf, Hex.DensePoly.zero_mul (S := Int) q] at hq
    exact hcore_ne hq
  -- The bound and positivity together imply `2 ≤ d.p^d.k`.
  have hlc_natAbs_pos : 0 < (Hex.DensePoly.leadingCoeff core).natAbs := by
    have hlc_ge_one : 1 ≤ Hex.DensePoly.leadingCoeff core := hcore_lc_pos
    have := Int.natAbs_of_nonneg (le_of_lt hcore_lc_pos)
    omega
  have hB'_pos : 0 < B' := by omega
  have hpk_ge_two : 2 ≤ d.p ^ d.k := by omega
  -- The centred lift of `C (lc core)` (under the bound) is `C (lc core)`.
  have hfactor_eq : factor = Hex.DensePoly.C (Hex.DensePoly.leadingCoeff core) := by
    rw [← hrec, hslp_eq_C]
    apply Hex.DensePoly.ext_coeff
    intro n
    rw [Hex.coeff_centeredLiftPoly, Hex.DensePoly.coeff_C]
    by_cases hn : n = 0
    · rw [if_pos hn]
      exact centeredModNat_eq_of_pos_natAbs_le hcore_lc_pos hcore_lc_le hprecision
    · rw [if_neg hn]
      exact Hex.centeredModNat_zero (d.p ^ d.k)
  -- `Primitive core` and `C (lc core) ∣ core` imply `IsUnit (lc core)`.
  have hcore_poly_primitive :
      (HexPolyZMathlib.toPolynomial core).IsPrimitive :=
    toPolynomial_isPrimitive_of_zpoly_primitive_basic hcore_primitive
  have hC_dvd_corePoly :
      Polynomial.C (Hex.DensePoly.leadingCoeff core) ∣
        HexPolyZMathlib.toPolynomial core := by
    have htop_factor_dvd_core :
        HexPolyZMathlib.toPolynomial factor ∣ HexPolyZMathlib.toPolynomial core :=
      HexPolyMathlib.toPolynomial_dvd hfactor_dvd
    have : HexPolyZMathlib.toPolynomial factor =
        Polynomial.C (Hex.DensePoly.leadingCoeff core) := by
      rw [hfactor_eq, HexPolyZMathlib.toPolynomial_C]
    rwa [this] at htop_factor_dvd_core
  have hlc_isUnit : IsUnit (Hex.DensePoly.leadingCoeff core) :=
    hcore_poly_primitive _ hC_dvd_corePoly
  -- `0 < lc core` and `IsUnit lc core` force `lc core = 1`.
  have hlc_one : Hex.DensePoly.leadingCoeff core = 1 := by
    rcases Int.isUnit_iff.mp hlc_isUnit with h | h
    · exact h
    · rw [h] at hcore_lc_pos; omega
  -- Now `factor = C 1 = 1`, contradicting irreducibility.
  rw [hlc_one] at hfactor_eq
  have hfactor_one : factor = 1 := hfactor_eq
  have hpolyfactor_eq : HexPolyZMathlib.toPolynomial factor = 1 := by
    rw [hfactor_one]; exact toPolynomial_one_zpoly
  exact not_irreducible_one (hpolyfactor_eq ▸ hfactor_irr)

/--
Primitive + positive-leading-core variant of
`not_represents_empty_of_irreducible_dvd_core` (#4646).

For primitive non-monic `core`, the empty-prefix collapse becomes
`scaledLiftedFactorProduct core d ∅ = C (lc core)`, and the centred-lift
recovery forces `factor = C (lc core)`. Together with
`Primitive core` and `factor ∣ core`, the primitivity definition of
`Polynomial ℤ` forces `lc core` to be a unit. With `0 < lc core` this gives
`lc core = 1`, so `factor = 1`, contradicting irreducibility. The
`d.p^d.k = 1` degenerate case is excluded as in the monic proof.

This is a thin wrapper over
`not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := defaultFactorCoeffBound core`, discharges
`hvalid` via `defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd`,
and discharges the leading-coefficient bound via the same lemma applied to
`core ∣ core`.
-/
private theorem not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core
    {core factor : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hfactor_dvd : factor ∣ core)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    ¬ RepresentsIntegerFactorAtLift core d factor
      (∅ : LiftedFactorSubset d) := by
  -- Bound the leading coefficient of `core` against the Mignotte half-window.
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne factor hfactor_dvd)
    hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le hfactor_dvd hfactor_irr
    hprecision

/--
Main candidate divisibility theorem for the Mathlib-side correspondence of the
Berlekamp-Zassenhaus recombination search (#4430 capstone).

Given a `LiftedFactorSubsetPartition core d J target` and a subset `T ⊆ J`,
suppose the candidate `recombinationCandidate d T` is recordable and admits
an exact quotient against `target`.  If an irreducible integer factor
`factor` of `target` is represented at the Hensel lift by some `S ⊆ T`,
then `factor` divides the recombination candidate.

Proof outline.  The exact-quotient equation
`quotient * recombinationCandidate d T = target` and the irreducibility of
`toPolynomial factor` (so it is prime in `Polynomial ℤ` by UFD) split the
divisibility into two cases:

* `toPolynomial factor ∣ toPolynomial (recombinationCandidate d T)` —
  transport back via `ofPolynomial` to obtain the desired
  `factor ∣ recombinationCandidate d T`.
* `toPolynomial factor ∣ toPolynomial quotient` — assemble a contradiction:
  when `S` is non-empty, pick any `i ∈ S ⊆ T` and apply
  `mem_T_iff_exists_irreducibleFactor_representingSubset` (#4469) to obtain
  an irreducible divisor `g` of the candidate whose representing subset
  `S_g` also contains `i`; the partition's `pairwise_disjoint` field
  contrapositively forces `Associated (toPolynomial factor) (toPolynomial g)`,
  so `toPolynomial factor ∣ toPolynomial (recombinationCandidate d T)` and
  hence `(toPolynomial factor)^2 ∣ toPolynomial target`, contradicting
  squarefreeness via `Irreducible.not_unit`.  When `S = ∅`, the recovery
  equation forces `factor = 1` (or `factor = 0` in the degenerate
  `d.p^d.k = 1` regime), again contradicting irreducibility — packaged in
  `not_represents_empty_of_irreducible_dvd_core`.
-/
theorem representedFactor_dvd_recombinationCandidate_of_subset
    {core target factor quotient : Hex.ZPoly} {d : Hex.LiftData}
    {J S T : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_liftedFactor_monic : ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (htarget_dvd_core : target ∣ core)
    (hTJ : T ⊆ J)
    (hSJ : S ⊆ J)
    (hrecord :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true)
    (hquot :
      Hex.exactQuotient? target (recombinationCandidate d T) = some quotient)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hST : S ⊆ T) :
    factor ∣ recombinationCandidate d T := by
  -- Quotient equation and `candidate ∣ target` from `exactQuotient?_product`.
  have hmul : quotient * recombinationCandidate d T = target :=
    Hex.exactQuotient?_product hquot
  have hcand_dvd_target : recombinationCandidate d T ∣ target := by
    refine ⟨quotient, ?_⟩
    rw [Hex.DensePoly.mul_comm_poly (S := Int)]
    exact hmul.symm
  have hpoly_mul :
      HexPolyZMathlib.toPolynomial quotient *
          HexPolyZMathlib.toPolynomial (recombinationCandidate d T) =
        HexPolyZMathlib.toPolynomial target := by
    rw [← HexPolyZMathlib.toPolynomial_mul, hmul]
  -- UFD prime step on `toPolynomial factor`.
  have hfactor_prime : Prime (HexPolyZMathlib.toPolynomial factor) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hfactor_irr
  have hpoly_factor_dvd_target :
      HexPolyZMathlib.toPolynomial factor ∣
        HexPolyZMathlib.toPolynomial target :=
    HexPolyMathlib.toPolynomial_dvd hfactor_dvd_target
  rw [← hpoly_mul] at hpoly_factor_dvd_target
  rcases hfactor_prime.dvd_or_dvd hpoly_factor_dvd_target with hp_dvd_q | hp_dvd_c
  · -- Case B: `toPolynomial factor ∣ toPolynomial quotient` — derive contradiction.
    exfalso
    have hfactor_dvd_core : factor ∣ core :=
      zpoly_dvd_trans hfactor_dvd_target htarget_dvd_core
    -- Derive `2 ≤ d.p^d.k` from `factor ≠ 0` and the centered-lift recovery,
    -- matching the pattern used in `representsIntegerFactorAtLift_monic`.
    have hd_modulus : 2 ≤ d.p ^ d.k := by
      have hrec :
          Hex.centeredLiftPoly
              (scaledLiftedFactorProduct core d S) (d.p ^ d.k) = factor :=
        centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery
          hcore_ne hfactor_dvd_core hrep hprecision
      have hfactor_ne : factor ≠ 0 := by
        intro hf
        rcases hfactor_dvd_core with ⟨q, hq⟩
        rw [hf, Hex.DensePoly.zero_mul (S := Int) q] at hq
        exact hcore_ne hq
      have hpk_pos : 0 < d.p ^ d.k := Nat.pow_pos d.p_pos
      rcases Nat.eq_or_lt_of_le
          (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpk_pos)) with hpk1 | hpk_gt
      · exfalso
        apply hfactor_ne
        apply Hex.DensePoly.ext_coeff
        intro i
        rw [← hrec, Hex.coeff_centeredLiftPoly, ← hpk1,
          Hex.DensePoly.coeff_zero]
        unfold Hex.centeredModNat
        have h1ne : (1 : Nat) ≠ 0 := by decide
        simp only [if_neg h1ne]
        simp
      · omega
    by_cases hS_empty : S = (∅ : LiftedFactorSubset d)
    · -- Subcase B2: `S = ∅` — packaged by the empty-support helper.
      apply not_represents_empty_of_irreducible_dvd_core
        hcore_ne hcore_monic hprecision hfactor_dvd_core hfactor_irr
      rw [hS_empty] at hrep
      exact hrep
    · -- Subcase B1: `S` non-empty.  Pick `i ∈ S ⊆ T`, apply #4469 to obtain
      -- `g, S_g` with `i ∈ S_g`, then use `pairwise_disjoint` contrapositively
      -- to conclude `Associated (toPolynomial factor) (toPolynomial g)`.
      have hS_ne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
      obtain ⟨i, hiS⟩ := hS_ne
      have hiT : i ∈ T := hST hiS
      obtain ⟨g, S_g, hg_irr, hg_dvd_cand, hg_rep, hSg_J, hi_Sg⟩ :=
        mem_T_iff_exists_irreducibleFactor_representingSubset
          hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
          hd_liftedFactor_natDegree_pos hprecision hpartition htarget_dvd_core
          hTJ hrecord hquot hiT
      have hg_dvd_target : g ∣ target :=
        zpoly_dvd_trans hg_dvd_cand hcand_dvd_target
      -- `i ∈ S ∩ S_g`, so `S` and `S_g` are not disjoint.
      have hnot_disjoint : ¬ Disjoint S S_g := by
        intro hdisj
        exact (Finset.disjoint_left.mp hdisj hiS) hi_Sg
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial g) := by
        by_contra hnot_assoc
        exact hnot_disjoint
          (hpartition.pairwise_disjoint
            hfactor_irr hfactor_dvd_target hSJ hrep
            hg_irr hg_dvd_target hSg_J hg_rep hnot_assoc)
      -- `factor ∣ g ∣ candidate` (poly side) and `factor ∣ quotient` (poly side)
      -- give `factor² ∣ target` (poly side), contradicting squarefreeness.
      have hp_factor_dvd_cand :
          HexPolyZMathlib.toPolynomial factor ∣
            HexPolyZMathlib.toPolynomial (recombinationCandidate d T) :=
        hassoc.dvd.trans (HexPolyMathlib.toPolynomial_dvd hg_dvd_cand)
      have hsqdvd :
          HexPolyZMathlib.toPolynomial factor *
              HexPolyZMathlib.toPolynomial factor ∣
            HexPolyZMathlib.toPolynomial target := by
        rw [← hpoly_mul]
        exact mul_dvd_mul hp_dvd_q hp_factor_dvd_cand
      exact hfactor_irr.not_isUnit
        (hpartition.target_squarefree _ hsqdvd)
  · -- Case A: `toPolynomial factor ∣ toPolynomial (recombinationCandidate d T)`.
    -- Transport back to `Hex.ZPoly` via `ofPolynomial`.
    rcases hp_dvd_c with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
      HexPolyZMathlib.toPolynomial_ofPolynomial]
    exact hr

/-- Abstract-bound variant of `liftedFactorSubsetPartition_prefix_none`:
takes `B' : Nat`, `hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B'`,
and `hprecision : 2 * B' < d.p ^ d.k` in place of the core-shape
`defaultFactorCoeffBound core` precision constraint.  Routes the cover-at-min
step through
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound`
after building the per-normalised-factor bound `hvalid'_T` from the universal
`g ∣ core` bound via the divisibility chain
`g ∣ recombinationCandidate d T ∣ target ∣ core`. -/
theorem liftedFactorSubsetPartition_prefix_none_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  intro split hsplit
  obtain ⟨T, hTJ, hmin_in_T, hsplit_eq, i, _hi_J, hi_S, hi_notT⟩ :=
    liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches
      hlocal_nodup hmatches hSJ hne hmin hsplits hsplit
  subst hsplit_eq
  show (if Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) then
      match Hex.exactQuotient? target (recombinationCandidate d T) with
      | none => none
      | some quotient' =>
          match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
              (liftedSubsetSelectedList d (J \ T)) fuel with
          | none => none
          | some r => some (recombinationCandidate d T :: r)
      else none) = none
  by_cases hrec :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true
  · rw [if_pos hrec]
    cases hquot :
        Hex.exactQuotient? target (recombinationCandidate d T) with
    | none => rfl
    | some quotient' =>
      exfalso
      -- Build the per-normalised-factor bound `hvalid'_T` from the universal
      -- `g ∣ core` bound by chaining
      -- `g ∣ recombinationCandidate d T ∣ target ∣ core`.
      have hcand_dvd_target :
          recombinationCandidate d T ∣ target := by
        have hmul :
            quotient' * recombinationCandidate d T = target :=
          Hex.exactQuotient?_product hquot
        refine ⟨quotient', ?_⟩
        rw [Hex.DensePoly.mul_comm_poly (S := Int)]
        exact hmul.symm
      have hcand_dvd_core :
          recombinationCandidate d T ∣ core :=
        zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
      have hvalid'_T : ∀ g : Hex.ZPoly,
          HexPolyZMathlib.toPolynomial g ∈
            UniqueFactorizationMonoid.normalizedFactors
              (HexPolyZMathlib.toPolynomial
                (recombinationCandidate d T)) →
          ∀ i, (g.coeff i).natAbs ≤ B' := by
        intro g hg_mem
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial
              (recombinationCandidate d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
        have hg_dvd_cand : g ∣ recombinationCandidate d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
        exact hvalid g hg_dvd_core
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep, hS_cov_T⟩ :=
        coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_bound
          B' hvalid'_T
          hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
          hd_liftedFactor_natDegree_pos hprecision hpartition
          htarget_dvd_core hTJ hne hmin_in_T hrec hquot
      have hnot_disjoint : ¬ Disjoint S S_cov := fun hdisj =>
        Finset.disjoint_left.mp hdisj hmin hmin_in_S_cov
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov) := by
        by_contra hnot_assoc
        exact hnot_disjoint
          (hpartition.pairwise_disjoint
            hfactor_irr hfactor_dvd_target hSJ hSrep
            hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hnot_assoc)
      have hSeq : S = S_cov :=
        hpartition.unique_up_to_associated
          hfactor_irr hfactor_dvd_target hSJ hSrep
          hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hassoc
      have hi_S_cov : i ∈ S_cov := hSeq ▸ hi_S
      exact hi_notT (hS_cov_T hi_S_cov)
  · rw [if_neg hrec]

/--
Prefix-none discharge under a `LiftedFactorSubsetPartition` (#4367 capstone).

Caller for the recursive coverage proof of
`Hex.recombinationSearchModAux` (#4301).  Every executable split in `pre`
— i.e. enumerated **before** the canonical boundary split
`(liftedSubsetSelectedList d S, liftedSubsetSelectedList d (J \ S))` —
returns `none` when threaded through one step of the recombination search,
provided `S` is the representing subset of an irreducible integer factor at
`J`'s minimum index.

Proof outline.
1. Apply `liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches` (the
   #4508 wrapper) to recover the proof-side subset `T ⊆ J` with
   `J.min' ∈ T` whose canonical split equals `split`, and to obtain a
   witness index `i ∈ J ∩ S \ T`.
2. Identify the inline `candidate'` with `recombinationCandidate d T`
   by definitional unfolding.
3. Split on `Hex.shouldRecordPolynomialFactor (recombinationCandidate d T)`:
   - `false`: the if-branch yields `none` directly.
   - `true`: suppose `Hex.exactQuotient? target (recombinationCandidate d T)
     = some quotient'`. Then
     `coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd`
     (#4395 / PR #4498) produces a representing subset `S_cov ⊆ T` with
     `J.min' ∈ S_cov` representing some irreducible `f_cov`.  Together with
     the hypothesised representing factor for `S`, the partition's
     `pairwise_disjoint` field (via the shared `J.min'`) forces
     `Associated factor f_cov`, then `unique_up_to_associated` collapses
     `S = S_cov ⊆ T`.  But `i ∈ S \ T` from the wrapper, contradicting
     `S ⊆ T`.

The `hlocal_nodup` precondition is required by the wrapper for the
mask-level bit-diff argument (without `Nodup`, the executable
`subsetSplits` enumeration can produce collisions on shared masked lists).
The caller in #4301 threads `Nodup` from a Hensel-coprimality fact
against the partition; a self-contained `liftedFactor d`-injectivity
helper at the partition level is left as a separable sub-task.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`liftedFactorSubsetPartition_prefix_none_of_bound`: the universal coefficient
bound for `g ∣ core` is discharged by `defaultFactorCoeffBound_valid` itself.
-/
theorem liftedFactorSubsetPartition_prefix_none
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none :=
  liftedFactorSubsetPartition_prefix_none_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision htarget_dvd_core hpartition
    hmatches hlocal_nodup hfactor_irr hfactor_dvd_target hSrep hSJ hne hmin
    hsplits

/-- Abstract-bound variant of
`liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core`:
takes `B' : Nat`, the leading-coefficient bound `hcore_lc_le`, the universal
core-divisor coefficient bound `hvalid`, and `hprecision : 2 * B' < d.p ^ d.k`
in place of the core-shape `defaultFactorCoeffBound core` precision constraint.

`T` is bound locally inside the proof body, so the `hvalid` hypothesis cannot
mention `T` at the binder level; the universal `g ∣ core` form is used instead.
Inside the inner `some` branch, the per-normalised-factor bound on the
candidate's normalised factors is built by chaining
`g ∣ recombinationCandidate d T ∣ target ∣ core` and applying `hvalid`.

The proof body otherwise mirrors the original (now-wrapper) verbatim: the
wrapper-decomposition via `liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches`,
the case-split on `shouldRecordPolynomialFactor` / `exactQuotient?`, and the
`pairwise_disjoint` / `unique_up_to_associated` contradiction. Only the
cover-at-min call is rerouted through
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`.
-/
theorem liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  intro split hsplit
  obtain ⟨T, hTJ, hmin_in_T, hsplit_eq, i, hi_J, hi_S, hi_notT⟩ :=
    liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches
      hlocal_nodup hmatches hSJ hne hmin hsplits hsplit
  subst hsplit_eq
  show (if Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) then
      match Hex.exactQuotient? target (recombinationCandidate d T) with
      | none => none
      | some quotient' =>
          match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
              (liftedSubsetSelectedList d (J \ T)) fuel with
          | none => none
          | some r => some (recombinationCandidate d T :: r)
      else none) = none
  by_cases hrec :
      Hex.shouldRecordPolynomialFactor (recombinationCandidate d T) = true
  · rw [if_pos hrec]
    cases hquot :
        Hex.exactQuotient? target (recombinationCandidate d T) with
    | none => rfl
    | some quotient' =>
      exfalso
      -- Build the per-normalised-factor bound `hvalid'_T` from the universal
      -- `g ∣ core` bound by chaining
      -- `g ∣ recombinationCandidate d T ∣ target ∣ core`.
      have hcand_dvd_target :
          recombinationCandidate d T ∣ target := by
        have hmul :
            quotient' * recombinationCandidate d T = target :=
          Hex.exactQuotient?_product hquot
        refine ⟨quotient', ?_⟩
        rw [Hex.DensePoly.mul_comm_poly (S := Int)]
        exact hmul.symm
      have hcand_dvd_core :
          recombinationCandidate d T ∣ core :=
        zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
      have hvalid'_T : ∀ g : Hex.ZPoly,
          HexPolyZMathlib.toPolynomial g ∈
            UniqueFactorizationMonoid.normalizedFactors
              (HexPolyZMathlib.toPolynomial
                (recombinationCandidate d T)) →
          ∀ i, (g.coeff i).natAbs ≤ B' := by
        intro g hg_mem
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial
              (recombinationCandidate d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
        have hg_dvd_cand : g ∣ recombinationCandidate d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
        exact hvalid g hg_dvd_core
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep, hS_cov_T⟩ :=
        coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
          B' hvalid'_T hcore_ne hcore_primitive hcore_lc_pos hcore_lc_le
          hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
          hprecision hpartition htarget_dvd_core hTJ hne hmin_in_T hrec hquot
      have hnot_disjoint : ¬ Disjoint S S_cov := fun hdisj =>
        Finset.disjoint_left.mp hdisj hmin hmin_in_S_cov
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov) := by
        by_contra hnot_assoc
        exact hnot_disjoint
          (hpartition.pairwise_disjoint
            hfactor_irr hfactor_dvd_target hSJ hSrep
            hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hnot_assoc)
      have hSeq : S = S_cov :=
        hpartition.unique_up_to_associated
          hfactor_irr hfactor_dvd_target hSJ hSrep
          hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hassoc
      have hi_S_cov : i ∈ S_cov := hSeq ▸ hi_S
      exact hi_notT (hS_cov_T hi_S_cov)
  · rw [if_neg hrec]

/-- Primitive + positive-leading-core variant of
`liftedFactorSubsetPartition_prefix_none` (#4646).

Identical to the monic version except the cover-at-min step routes through
`coverAtMin_representingSubset_subset_of_recombinationCandidate_dvd_of_primitive_pos_lc_core`.
The structural cover/pairwise-disjoint/unique fields of the partition do not
depend on `Monic core`, so the rest of the proof carries over verbatim.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_of_bound`:
the leading-coefficient bound is discharged via
`defaultFactorCoeffBound_leadingCoeff_natAbs_le`, and the universal
coefficient bound for `g ∣ core` is `defaultFactorCoeffBound_valid` itself. -/
theorem liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly (Array.polyProduct split.1.toArray)
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.recombinationSearchModAux quotient' (d.p ^ d.k)
                split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision htarget_dvd_core hpartition
    hmatches hlocal_nodup hfactor_irr hfactor_dvd_target hSrep hSJ hne hmin
    hsplits

/-- Abstract-bound variant of
`liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_scaled`:
takes `B' : Nat`, the leading-coefficient bound `hcore_lc_le`, the universal
core-divisor coefficient bound `hvalid`, and `hprecision : 2 * B' < d.p ^ d.k`
in place of the core-shape `defaultFactorCoeffBound core` precision constraint.

`T` is bound locally inside the proof body, so the `hvalid` hypothesis cannot
mention `T` at the binder level (Option A in the issue text); the universal
`g ∣ core` form is used instead. Inside the inner `some` branch, the
per-normalised-factor bound on the candidate's normalised factors is built by
chaining `g ∣ scaledRecombinationCandidate core d T ∣ target ∣ core` and
applying `hvalid`.

The proof body otherwise mirrors the original (now-wrapper) verbatim: the
wrapper-decomposition via `liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches`,
the identification with `scaledRecombinationCandidate core d T` via
`polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct`, the case-split
on `shouldRecordPolynomialFactor` / `exactQuotient?`, and the
`pairwise_disjoint` / `unique_up_to_associated` contradiction. Only the
cover-at-min call is rerouted through
`coverAtMin_representingSubset_subset_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound`.
-/
theorem liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_scaled_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (_hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly
              (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
                (Array.polyProduct split.1.toArray))
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.scaledRecombinationSearchModAux
                (Hex.DensePoly.leadingCoeff core)
                quotient' (d.p ^ d.k) split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  intro split hsplit
  obtain ⟨T, hTJ, hmin_in_T, hsplit_eq, i, _hi_J, hi_S, hi_notT⟩ :=
    liftedSubsetSplit_prefix_exists_mem_sdiff_of_matches
      hlocal_nodup hmatches hSJ hne hmin hsplits hsplit
  subst hsplit_eq
  -- Identify the inline scaled candidate with `scaledRecombinationCandidate core d T`
  -- via `polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct` plus the
  -- definitional unfolding `scaledLiftedFactorProduct = scale (lc core) ∘ liftedFactorProduct`.
  simp only [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
  show (if Hex.shouldRecordPolynomialFactor (scaledRecombinationCandidate core d T) then
      match Hex.exactQuotient? target (scaledRecombinationCandidate core d T) with
      | none => none
      | some quotient' =>
          match Hex.scaledRecombinationSearchModAux
              (Hex.DensePoly.leadingCoeff core)
              quotient' (d.p ^ d.k)
              (liftedSubsetSelectedList d (J \ T)) fuel with
          | none => none
          | some r => some (scaledRecombinationCandidate core d T :: r)
      else none) = none
  by_cases hrec :
      Hex.shouldRecordPolynomialFactor (scaledRecombinationCandidate core d T) = true
  · rw [if_pos hrec]
    cases hquot :
        Hex.exactQuotient? target (scaledRecombinationCandidate core d T) with
    | none => rfl
    | some quotient' =>
      exfalso
      -- Build the per-normalised-factor bound `hvalid'_T` from the universal
      -- `g ∣ core` bound by chaining
      -- `g ∣ scaledRecombinationCandidate core d T ∣ target ∣ core`.
      have hcand_dvd_target :
          scaledRecombinationCandidate core d T ∣ target := by
        have hmul :
            quotient' * scaledRecombinationCandidate core d T = target :=
          Hex.exactQuotient?_product hquot
        refine ⟨quotient', ?_⟩
        rw [Hex.DensePoly.mul_comm_poly (S := Int)]
        exact hmul.symm
      have hcand_dvd_core :
          scaledRecombinationCandidate core d T ∣ core :=
        zpoly_dvd_trans hcand_dvd_target htarget_dvd_core
      have hvalid'_T : ∀ g : Hex.ZPoly,
          HexPolyZMathlib.toPolynomial g ∈
            UniqueFactorizationMonoid.normalizedFactors
              (HexPolyZMathlib.toPolynomial
                (scaledRecombinationCandidate core d T)) →
          ∀ i, (g.coeff i).natAbs ≤ B' := by
        intro g hg_mem
        have hg_poly_dvd : HexPolyZMathlib.toPolynomial g ∣
            HexPolyZMathlib.toPolynomial
              (scaledRecombinationCandidate core d T) :=
          UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hg_mem
        have hg_dvd_cand : g ∣ scaledRecombinationCandidate core d T := by
          rcases hg_poly_dvd with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          exact hr
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_cand hcand_dvd_core
        exact hvalid g hg_dvd_core
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep, hS_cov_T⟩ :=
        coverAtMin_representingSubset_subset_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core_of_bound
          B' hcore_lc_le hvalid'_T
          hcore_ne hcore_primitive hcore_lc_pos hd_liftedFactor_monic
          hd_liftedFactor_natDegree_pos hprecision hpartition
          htarget_dvd_core hTJ hne hmin_in_T hrec hquot
      have hnot_disjoint : ¬ Disjoint S S_cov := fun hdisj =>
        Finset.disjoint_left.mp hdisj hmin hmin_in_S_cov
      have hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov) := by
        by_contra hnot_assoc
        exact hnot_disjoint
          (hpartition.pairwise_disjoint
            hfactor_irr hfactor_dvd_target hSJ hSrep
            hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hnot_assoc)
      have hSeq : S = S_cov :=
        hpartition.unique_up_to_associated
          hfactor_irr hfactor_dvd_target hSJ hSrep
          hf_cov_irr hf_cov_dvd_target hS_cov_J hS_cov_rep hassoc
      have hi_S_cov : i ∈ S_cov := hSeq ▸ hi_S
      exact hi_notT (hS_cov_T hi_S_cov)
  · rw [if_neg hrec]

/-- Scaled-candidate analogue of
`liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core` (#4738).

Discharges the per-split prefix obligation of
`Hex.scaledRecombinationSearchModAux`: every split appearing strictly before the
canonical `(S, J \ S)` split contributes `none` to the search's `firstSome`. The
proof mirrors the unscaled primitive prefix-none, routing the cover-at-min step
through the scaled analogue
`coverAtMin_representingSubset_subset_of_scaledRecombinationCandidate_dvd_of_primitive_pos_lc_core`
(#4737). The single non-cosmetic difference is a one-line rewrite identifying the
inline candidate -- built from `polyProduct split.1.toArray` scaled by `lc core`
-- with `scaledRecombinationCandidate core d T` after substituting
`split = (liftedSubsetSelectedList d T, liftedSubsetSelectedList d (J \ T))`.

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_scaled_of_bound`:
the leading-coefficient bound is discharged via the self-divisibility instance
of `defaultFactorCoeffBound_valid` combined with `leadingCoeff_eq_coeff_last`,
and the universal coefficient bound for `g ∣ core` is `defaultFactorCoeffBound_valid`
itself. -/
theorem liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_scaled
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J S : LiftedFactorSubset d} {localFactors : List Hex.ZPoly}
    {fuel : Nat}
    {pre suffix : List (List Hex.ZPoly × List Hex.ZPoly)}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hlocal_nodup : localFactors.Nodup)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hSrep : RepresentsIntegerFactorAtLift core d factor S)
    (hSJ : S ⊆ J) (hne : J.Nonempty) (hmin : J.min' hne ∈ S)
    (hsplits :
      Hex.subsetSplitsWithFirst localFactors =
        pre ++
          (liftedSubsetSelectedList d S,
           liftedSubsetSelectedList d (J \ S)) :: suffix) :
    ∀ split ∈ pre,
      (let candidate' :=
        Hex.normalizeFactorSign <|
          Hex.ZPoly.primitivePart <|
            Hex.centeredLiftPoly
              (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
                (Array.polyProduct split.1.toArray))
              (d.p ^ d.k)
      if Hex.shouldRecordPolynomialFactor candidate' then
        match Hex.exactQuotient? target candidate' with
        | none => none
        | some quotient' =>
            match Hex.scaledRecombinationSearchModAux
                (Hex.DensePoly.leadingCoeff core)
                quotient' (d.p ^ d.k) split.2 fuel with
            | none => none
            | some r => some (candidate' :: r)
      else none) = none := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_scaled_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hprecision htarget_dvd_core hpartition
    hmatches hlocal_nodup hfactor_irr hfactor_dvd_target hSrep hSJ hne hmin
    hsplits

/-- Algorithm-side packaging for the exhaustive core branch in the form needed
by UFD arguments over `Polynomial ℤ`.

The executable exhaustive wrapper already proves that the returned candidates
multiply back to the core and that every returned candidate passes
`shouldRecordPolynomialFactor` whenever the core itself does.  Once the
remaining Group A completeness work supplies the cardinality equality, the
abstract UFD partition lemma turns those facts into irreducibility of every
emitted core factor. -/
theorem exhaustiveCoreFactorsWithBound_factor_irreducible_of_count
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hcount :
      ((Hex.exhaustiveCoreFactorsWithBound core B primeData).toList.map
          HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
      Irreducible (HexPolyZMathlib.toPolynomial factor) := by
  set coreFactors := Hex.exhaustiveCoreFactorsWithBound core B primeData with hcoreFactors_def
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  have hf_ne : f ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa [hf_def] using hzero
  set gs : List (Polynomial ℤ) :=
    coreFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hprod : Associated gs.prod f := by
    have hp_core : Array.polyProduct coreFactors = core := by
      simpa [hcoreFactors_def] using
        Hex.exhaustiveCoreFactorsWithBound_product core B primeData
    have hp_poly :
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial core := by
      rw [← polyProduct_toPolynomial, hp_core]
    rw [hgs_def, hp_poly, hf_def]
  have hrecord_all :
      ∀ factor ∈ coreFactors.toList,
        Hex.shouldRecordPolynomialFactor factor = true := by
    simpa [hcoreFactors_def] using
      Hex.exhaustiveCoreFactorsWithBound_shouldRecord core B primeData hcore_record
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
  have hcount_gs :
      gs.length = (UniqueFactorizationMonoid.normalizedFactors f).card := by
    simpa [hgs_def, hcoreFactors_def, hf_def] using hcount
  intro factor hfactor_mem
  have hpolyfactor_mem :
      HexPolyZMathlib.toPolynomial factor ∈ gs := by
    rw [hgs_def, List.mem_map]
    exact ⟨factor, hfactor_mem, rfl⟩
  exact
    HexBerlekampZassenhausMathlib.UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card
      hf_ne gs hne_all hnonunit_all hprod hcount_gs _ hpolyfactor_mem

/-- Upper cardinality bound for the exhaustive core branch.

The emitted factor list consists of non-zero non-units whose product is
associated to `core`, so the abstract UFD partition bound applies after
transporting the executable factors to `Polynomial ℤ`. -/
theorem exhaustiveCoreFactorsWithBound_factor_count_le
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true) :
    ((Hex.exhaustiveCoreFactorsWithBound core B primeData).toList.map
        HexPolyZMathlib.toPolynomial).length ≤
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  set coreFactors := Hex.exhaustiveCoreFactorsWithBound core B primeData with hcoreFactors_def
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  have hf_ne : f ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa [hf_def] using hzero
  set gs : List (Polynomial ℤ) :=
    coreFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hprod : Associated gs.prod f := by
    have hp_core : Array.polyProduct coreFactors = core := by
      simpa [hcoreFactors_def] using
        Hex.exhaustiveCoreFactorsWithBound_product core B primeData
    have hp_poly :
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial core := by
      rw [← polyProduct_toPolynomial, hp_core]
    rw [hgs_def, hp_poly, hf_def]
  have hrecord_all :
      ∀ factor ∈ coreFactors.toList,
        Hex.shouldRecordPolynomialFactor factor = true := by
    simpa [hcoreFactors_def] using
      Hex.exhaustiveCoreFactorsWithBound_shouldRecord core B primeData hcore_record
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
  exact
    HexBerlekampZassenhausMathlib.UFDPartition.length_le_normalizedFactors_card
      hf_ne gs hne_all hnonunit_all hprod

/-- Exhaustive core branch irreducibility, expressed in the Mathlib-free
`Hex.ZPoly.Irreducible` predicate.  This is the `Hex.ZPoly` transport of
`exhaustiveCoreFactorsWithBound_factor_irreducible_of_count`. -/
theorem exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_count
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hcount :
      ((Hex.exhaustiveCoreFactorsWithBound core B primeData).toList.map
          HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hfactor_mem
  exact
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible factor).mpr
      (exhaustiveCoreFactorsWithBound_factor_irreducible_of_count
        hcore_ne hcore_record hcount factor hfactor_mem)

/-- Lower cardinality bound for the exhaustive core branch under irreducibility
of every emitted factor.

The emitted factor list has product associated to `core`, so if each transported
factor is irreducible, the abstract UFD partition lower-bound applies and gives
the reverse count inequality paired with
`exhaustiveCoreFactorsWithBound_factor_count_le`.

The irreducibility hypothesis is the open obligation #4149 supplies via the
Hensel subset coverage theorem at default precision. -/
theorem exhaustiveCoreFactorsWithBound_factor_count_ge_of_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (hirr :
      ∀ factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
        Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    (UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial core)).card ≤
        ((Hex.exhaustiveCoreFactorsWithBound core B primeData).toList.map
          HexPolyZMathlib.toPolynomial).length := by
  set coreFactors := Hex.exhaustiveCoreFactorsWithBound core B primeData with hcoreFactors_def
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  have _hf_ne : f ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa [hf_def] using hzero
  set gs : List (Polynomial ℤ) :=
    coreFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  have hprod : Associated gs.prod f := by
    have hp_core : Array.polyProduct coreFactors = core := by
      simpa [hcoreFactors_def] using
        Hex.exhaustiveCoreFactorsWithBound_product core B primeData
    have hp_poly :
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).prod =
          HexPolyZMathlib.toPolynomial core := by
      rw [← polyProduct_toPolynomial, hp_core]
    rw [hgs_def, hp_poly, hf_def]
  have hirr_gs : ∀ g ∈ gs, Irreducible g := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact hirr factor (by simpa [hcoreFactors_def] using hfactor_mem)
  exact
    HexBerlekampZassenhausMathlib.UFDPartition.normalizedFactors_card_le_length_of_irreducible_partition
      gs hirr_gs hprod

/-- Cardinality equality for the exhaustive core branch under irreducibility of
every emitted factor.  Pairs `exhaustiveCoreFactorsWithBound_factor_count_le`
with `exhaustiveCoreFactorsWithBound_factor_count_ge_of_irreducible`, exposing
the count equality in a form directly usable as the `hcount` hypothesis of
`exhaustiveCoreFactorsWithBound_factor_irreducible_of_count` and
`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_count`. -/
theorem exhaustiveCoreFactorsWithBound_factor_count_eq_of_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hirr :
      ∀ factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
        Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    ((Hex.exhaustiveCoreFactorsWithBound core B primeData).toList.map
        HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  apply le_antisymm
  · exact exhaustiveCoreFactorsWithBound_factor_count_le hcore_ne hcore_record
  · exact exhaustiveCoreFactorsWithBound_factor_count_ge_of_irreducible hcore_ne hirr

/-- Convenience composition: under the same hypotheses as
`exhaustiveCoreFactorsWithBound_factor_count_eq_of_irreducible`, every emitted
factor is irreducible.  Routes through the cardinality equality and
`exhaustiveCoreFactorsWithBound_factor_irreducible_of_count` so that slow
exhaustive branch callers can ask directly for irreducibility under the
A1/A2/default-precision hypotheses once those are wired to the irreducibility
hypothesis by #4149's coverage theorem. -/
theorem exhaustiveCoreFactorsWithBound_factor_irreducible_of_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hirr :
      ∀ factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
        Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    ∀ factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
      Irreducible (HexPolyZMathlib.toPolynomial factor) :=
  exhaustiveCoreFactorsWithBound_factor_irreducible_of_count
    hcore_ne hcore_record
    (exhaustiveCoreFactorsWithBound_factor_count_eq_of_irreducible
      hcore_ne hcore_record hirr)

/-- Convenience composition: under the same hypotheses as
`exhaustiveCoreFactorsWithBound_factor_count_eq_of_irreducible`, every emitted
factor is irreducible in the Mathlib-free `Hex.ZPoly.Irreducible` predicate.
Routes through the cardinality equality and
`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_count`. -/
theorem exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    (hcore_ne : core ≠ 0)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hirr :
      ∀ factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
        Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    ∀ factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
      Hex.ZPoly.Irreducible factor :=
  exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_count
    hcore_ne hcore_record
    (exhaustiveCoreFactorsWithBound_factor_count_eq_of_irreducible
      hcore_ne hcore_record hirr)

/-- Slow exhaustive branch core-factor irreducibility for recorded
`factorWithBound` entries.

The executable branch-shape theorem exposes recorded entries through raw slow
factors. This theorem packages the final step for the case where the recorded
factor has already been identified with one of the exhaustive square-free-core
factors.  The remaining Group A completeness obligation is isolated as the
cardinality equality hypothesis. -/
theorem factorWithBound_exhaustive_branch_entry_core_zpolyIrreducible_of_count
    {f : Hex.ZPoly} {B : Nat} {entry : Hex.ZPoly × Nat}
    (primeData : Hex.PrimeChoiceData)
    (_hbranch : Hex.factorWithBoundUsesExhaustiveBranch f B)
    (_hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList)
    (hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hcore_record :
      Hex.shouldRecordPolynomialFactor
        (Hex.normalizeForFactor f).squareFreeCore = true)
    (_hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hcount :
      ((Hex.exhaustiveCoreFactorsWithBound
          (Hex.normalizeForFactor f).squareFreeCore B primeData).toList.map
          HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    (hcore_entry :
      ∃ raw ∈
        (Hex.exhaustiveCoreFactorsWithBound
          (Hex.normalizeForFactor f).squareFreeCore B primeData).toList,
        entry.1 = raw) :
    Hex.ZPoly.Irreducible entry.1 := by
  rcases hcore_entry with ⟨raw, hraw_mem, hentry_eq⟩
  have hirr_raw :
      Hex.ZPoly.Irreducible raw :=
    exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_count
      hcore_ne hcore_record hcount raw hraw_mem
  rw [hentry_eq]
  exact hirr_raw

/-- Algorithm-side packaging for the BHKS fast-core success branch in
the form needed by UFD arguments over `Polynomial ℤ`.  Combines the
existing product, divisibility, and `shouldRecord` invariants exposed
in `HexBerlekampZassenhaus/Basic.lean` with the `toPolynomial` map.
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

/-- Upper cardinality bound for a successful BHKS fast-core branch.

The emitted factor list consists of non-zero non-units whose product is
associated to `core`, so the abstract UFD partition bound applies after
transporting the executable factors to `Polynomial ℤ`. -/
theorem factorFastCoreWithBound_some_factor_count_le
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length ≤
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
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
  exact
    HexBerlekampZassenhausMathlib.UFDPartition.length_le_normalizedFactors_card
      hf_ne gs hne_all hnonunit_all hprod

/-- Lower cardinality bound for a successful BHKS fast-core branch whose
emitted candidates have already been certified irreducible.

The remaining BHKS/B8 work is to derive the `hirr` hypothesis from the
equivalence-class partition-refinement argument for the concrete success
state.  Once supplied, the abstract UFD partition theorem gives the reverse
count inequality needed to pair with
`factorFastCoreWithBound_some_factor_count_le`. -/
theorem factorFastCoreWithBound_some_factor_count_ge_of_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hirr :
      ∀ factor ∈ coreFactors.toList,
        Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    (UniqueFactorizationMonoid.normalizedFactors
      (HexPolyZMathlib.toPolynomial core)).card ≤
        (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length := by
  set f := HexPolyZMathlib.toPolynomial core with hf_def
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
  have hirr_gs : ∀ g ∈ gs, Irreducible g := by
    intro g hg
    rw [hgs_def, List.mem_map] at hg
    obtain ⟨factor, hfactor_mem, hg_eq⟩ := hg
    rw [← hg_eq]
    exact hirr factor hfactor_mem
  exact
    HexBerlekampZassenhausMathlib.UFDPartition.normalizedFactors_card_le_length_of_irreducible_partition
      gs hirr_gs hprod

/-- Cardinality equality for a successful BHKS fast-core branch once the
BHKS/B8 proof has certified every emitted candidate irreducible. -/
theorem factorFastCoreWithBound_some_factor_count_eq_of_irreducible
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hirr :
      ∀ factor ∈ coreFactors.toList,
        Irreducible (HexPolyZMathlib.toPolynomial factor)) :
    (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
      (UniqueFactorizationMonoid.normalizedFactors
        (HexPolyZMathlib.toPolynomial core)).card := by
  apply le_antisymm
  · exact factorFastCoreWithBound_some_factor_count_le hcore_ne h
  · exact factorFastCoreWithBound_some_factor_count_ge_of_irreducible h hirr

/-- Branch-local fast-core success irreducibility, expressed in the Mathlib-free
`Hex.ZPoly.Irreducible` predicate. This is the `Hex.ZPoly` transport of
`factorFastCoreWithBound_some_factor_irreducible_of_count`, obtained by
composing that scaffold with the existing
`Hex.ZPoly.Irreducible_iff_polynomialIrreducible` equivalence.

The remaining count-equality hypothesis is the residual #4030 obligation; once
supplied, this lemma yields fast-core branch irreducibility directly in the
executable `Hex.ZPoly` form needed by callers that do not import Mathlib's
`Polynomial` model. -/
theorem factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {k fuel : Nat} {coreFactors : Array Hex.ZPoly}
    (hcore_ne : core ≠ 0)
    (h : Hex.factorFastCoreWithBound core B primeData k fuel = some coreFactors)
    (hcount :
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card) :
    ∀ factor ∈ coreFactors.toList, Hex.ZPoly.Irreducible factor := by
  intro factor hfactor_mem
  exact
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible factor).mpr
      (factorFastCoreWithBound_some_factor_irreducible_of_count
        hcore_ne h hcount factor hfactor_mem)

/--
Abstract-bound variant of
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the universal divisor coefficient bound
`∀ g ∣ core, ∀ i, (g.coeff i).natAbs ≤ B'`. The proof body otherwise
mirrors the (now-wrapper) original verbatim: at each of the five
`_of_bound` supporting lemma call sites
(`not_represents_empty_of_irreducible_dvd_core_of_bound` in the empty-`J`
step, `representsIntegerFactorAtLift_monic_of_bound` and
`recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound` at
the cover-at-min recovery,
`natDegree_toPolynomial_eq_sum_of_represents_of_bound` for the natDegree
positivity, and `liftedFactorSubsetPartition_prefix_none_of_bound` for
the prefix-none discharge), the per-factor `hvalid` is specialised to
the local divisor (`g` in the empty-`J` step, `f_cov` for the other
three per-factor callers) by `hvalid g hg_dvd_core` /
`hvalid f_cov hf_cov_dvd_core`, while the prefix-none caller receives
the universal `hvalid` and `B'` unchanged. In the recursive IH call,
the outer abstract-bound hypotheses are captured by closure.
-/
private theorem recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {fuel : Nat},
      Hex.DensePoly.Monic target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      J.card < fuel →
      ∃ result,
        Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors fuel =
          some result ∧
        ∀ factor : Hex.ZPoly,
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ target →
          ∃ emitted ∈ result,
            Associated (HexPolyZMathlib.toPolynomial emitted)
              (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors fuel htarget_monic htarget_dvd_core hpartition
    hmatches hfuel
  induction fuel generalizing target J localFactors with
  | zero => omega
  | succ fuel' ih =>
    by_cases htarget_eq_one : target = 1
    · -- `target = 1` branch: the executable returns `some []` directly, and the
      -- universal claim is vacuous because no irreducible divides `1`.
      subst htarget_eq_one
      refine ⟨[], ?_, ?_⟩
      · show Hex.recombinationSearchModAux 1 (d.p ^ d.k) localFactors (fuel' + 1) =
          some []
        unfold Hex.recombinationSearchModAux
        simp
      · intro factor hirr hdvd
        exfalso
        have hfactor_dvd_one_poly :
            HexPolyZMathlib.toPolynomial factor ∣ (1 : Polynomial ℤ) := by
          rw [show (1 : Polynomial ℤ) = HexPolyZMathlib.toPolynomial 1 from
            toPolynomial_one_zpoly.symm]
          exact HexPolyMathlib.toPolynomial_dvd hdvd
        exact hirr.not_isUnit (isUnit_of_dvd_one hfactor_dvd_one_poly)
    · -- `target ≠ 1` branch: derive `J` nonempty, then descend through the
      -- `cover_at_min`-emitted irreducible factor `f_cov`.
      have htarget_poly_monic :
          (HexPolyZMathlib.toPolynomial target).Monic := by
        show (HexPolyZMathlib.toPolynomial target).leadingCoeff = 1
        rw [HexPolyMathlib.leadingCoeff_toPolynomial]
        exact htarget_monic
      -- Step 1: `J` is nonempty (else the partition produces a representing
      -- subset `S ⊆ ∅` for an irreducible divisor of `target`, contradicting
      -- `not_represents_empty_of_irreducible_dvd_core_of_bound`).
      have hJ_ne : J.Nonempty := by
        by_contra hJ_empty
        rw [Finset.not_nonempty_iff_eq_empty] at hJ_empty
        have htarget_poly_ne_one :
            HexPolyZMathlib.toPolynomial target ≠ 1 := by
          intro h
          apply htarget_eq_one
          apply HexPolyZMathlib.equiv.injective
          show HexPolyZMathlib.toPolynomial target =
            HexPolyZMathlib.toPolynomial 1
          rw [toPolynomial_one_zpoly]
          exact h
        have htarget_poly_nonunit :
            ¬ IsUnit (HexPolyZMathlib.toPolynomial target) := by
          intro hunit
          exact htarget_poly_ne_one
            (htarget_poly_monic.eq_one_of_isUnit hunit)
        have htarget_poly_ne :
            HexPolyZMathlib.toPolynomial target ≠ 0 :=
          htarget_poly_monic.ne_zero
        obtain ⟨gPoly, hg_irr, hg_dvd_target_poly⟩ :=
          WfDvdMonoid.exists_irreducible_factor htarget_poly_nonunit
            htarget_poly_ne
        let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
        have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
          HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
        have hg_dvd_target : g ∣ target := by
          rcases hg_dvd_target_poly with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply,
            HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          rw [hg_toPolynomial]
          exact hr
        have hg_irr_toPoly :
            Irreducible (HexPolyZMathlib.toPolynomial g) := by
          rw [hg_toPolynomial]; exact hg_irr
        obtain ⟨S, hSJ, hSrep⟩ :=
          hpartition.exists_subset hg_irr_toPoly hg_dvd_target
        have hS_empty : S = ∅ := by
          rw [hJ_empty] at hSJ
          exact Finset.subset_empty.mp hSJ
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_target htarget_dvd_core
        apply not_represents_empty_of_irreducible_dvd_core_of_bound
          B' (hvalid g hg_dvd_core) hcore_ne hcore_monic hg_dvd_core
          hg_irr_toPoly hprecision
        rw [← hS_empty]; exact hSrep
      -- Step 2: cover-at-min produces an irreducible divisor `f_cov` of `target`
      -- whose representing subset `S_cov` contains `J.min'`.
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep⟩ :=
        hpartition.cover_at_min hJ_ne
      have hf_cov_dvd_core : f_cov ∣ core :=
        zpoly_dvd_trans hf_cov_dvd_target htarget_dvd_core
      have hf_cov_monic : Hex.DensePoly.Monic f_cov :=
        representsIntegerFactorAtLift_monic_of_bound
          B' (hvalid f_cov hf_cov_dvd_core) hcore_ne hcore_monic
          hd_liftedFactor_monic hf_cov_dvd_target htarget_dvd_core
          hS_cov_rep hprecision
      have hf_cov_prim : Hex.ZPoly.content f_cov = 1 :=
        zpoly_primitive_of_monic hf_cov_monic
      have hf_cov_norm : Hex.normalizeFactorSign f_cov = f_cov :=
        zpoly_normalize_factor_sign_of_monic hf_cov_monic
      have hrec_eq : recombinationCandidate d S_cov = f_cov :=
        recombinationCandidate_eq_factor_of_recovery_of_monic_core_of_bound
          B' (hvalid f_cov hf_cov_dvd_core) hcore_ne hcore_monic
          hf_cov_prim hf_cov_norm hf_cov_irr hS_cov_rep hprecision
      -- Step 3: `f_cov` has positive natDegree (sum over `S_cov` nonempty).
      have hf_cov_natDeg_pos :
          0 < (HexPolyZMathlib.toPolynomial f_cov).natDegree := by
        rw [natDegree_toPolynomial_eq_sum_of_represents_of_bound
          B' (hvalid f_cov hf_cov_dvd_core) hcore_ne hcore_monic
          hd_liftedFactor_monic hf_cov_dvd_core hf_cov_irr
          hf_cov_prim hf_cov_norm hS_cov_rep hprecision]
        apply Finset.sum_pos (fun i _ => hd_liftedFactor_natDegree_pos i)
        exact ⟨J.min' hJ_ne, hmin_in_S_cov⟩
      have hf_cov_degree_pos : 0 < f_cov.degree?.getD 0 := by
        rw [← HexPolyMathlib.natDegree_toPolynomial]
        exact hf_cov_natDeg_pos
      -- Step 4: exact-quotient equation `quotient * f_cov = target`.
      obtain ⟨quotient, hquot, hmul⟩ :=
        exactQuotient?_recombinationCandidate_eq_some_of_eq_factor
          hrec_eq hf_cov_monic hf_cov_degree_pos hf_cov_dvd_target
      have hquot_eq : quotient * f_cov = target := hrec_eq ▸ hmul
      have hquot_poly_eq :
          HexPolyZMathlib.toPolynomial quotient *
              HexPolyZMathlib.toPolynomial f_cov =
            HexPolyZMathlib.toPolynomial target := by
        rw [← HexPolyZMathlib.toPolynomial_mul, hquot_eq]
      -- Step 5: `quotient` is monic and divides `core`.
      have hquot_dvd_target : quotient ∣ target :=
        ⟨f_cov, hquot_eq.symm⟩
      have hquot_dvd_core : quotient ∣ core :=
        zpoly_dvd_trans hquot_dvd_target htarget_dvd_core
      have hf_cov_poly_monic :
          (HexPolyZMathlib.toPolynomial f_cov).Monic := by
        show (HexPolyZMathlib.toPolynomial f_cov).leadingCoeff = 1
        rw [HexPolyMathlib.leadingCoeff_toPolynomial]
        exact hf_cov_monic
      have hquot_monic : Hex.DensePoly.Monic quotient := by
        have hquot_poly_monic :
            (HexPolyZMathlib.toPolynomial quotient).Monic :=
          hf_cov_poly_monic.of_mul_monic_right (hquot_poly_eq ▸ htarget_poly_monic)
        show Hex.DensePoly.leadingCoeff quotient = (1 : Int)
        rw [← HexPolyMathlib.leadingCoeff_toPolynomial]
        exact hquot_poly_monic
      -- Step 6: partition transport and matches transport for the recursive call.
      have hpartition_new :
          LiftedFactorSubsetPartition core d (J \ S_cov) quotient :=
        liftedFactorSubsetPartition_transport hpartition hquot_eq hS_cov_rep
          hS_cov_J hf_cov_irr hf_cov_dvd_target
      have hmatches_new :
          LiftedFactorListMatches d (J \ S_cov)
            (liftedSubsetSelectedList d (J \ S_cov)) :=
        LiftedFactorListMatches.sdiff_of_subset
      -- Step 7: fuel decrement is valid because `(J \ S_cov).card < J.card`
      -- (since `J.min' ∈ S_cov ⊆ J`, so `J \ S_cov` is a strict subset of `J`).
      have hcard_new : (J \ S_cov).card < fuel' := by
        have hmin_not_in_sdiff : J.min' hJ_ne ∉ J \ S_cov := by
          intro h
          exact (Finset.mem_sdiff.mp h).2 hmin_in_S_cov
        have hsub_strict : J \ S_cov ⊂ J := by
          refine ⟨Finset.sdiff_subset, fun hsub => hmin_not_in_sdiff ?_⟩
          exact hsub (J.min'_mem hJ_ne)
        have : (J \ S_cov).card < J.card := Finset.card_lt_card hsub_strict
        omega
      -- Step 8: apply the IH to obtain the recursive search success and the
      -- universal coverage for divisors of `quotient`.
      obtain ⟨restFactors, hrest, hrest_covers⟩ :=
        ih hquot_monic hquot_dvd_core hpartition_new hmatches_new hcard_new
      -- Step 9: decompose the canonical split membership into prefix and suffix.
      have hsplit_mem :
          (liftedSubsetSelectedList d S_cov,
              liftedSubsetSelectedList d (J \ S_cov)) ∈
            Hex.subsetSplitsWithFirst localFactors :=
        liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
          hmatches hS_cov_J hJ_ne hmin_in_S_cov
      obtain ⟨pre, suffix, hsplits⟩ := List.append_of_mem hsplit_mem
      -- Step 10: prefix-none discharge.
      have hlocal_nodup : localFactors.Nodup :=
        hmatches.nodup_of_injOn hd_liftedFactor_inj.injOn
      have hprefix :=
        liftedFactorSubsetPartition_prefix_none_of_bound
          B' hvalid hcore_ne hcore_monic hd_modulus
          hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hprecision
          htarget_dvd_core hpartition hmatches hlocal_nodup hf_cov_irr
          hf_cov_dvd_target hS_cov_rep hS_cov_J hJ_ne hmin_in_S_cov hsplits
          (fuel := fuel')
      -- Step 11: assemble the executable step result via
      -- `recombinationSearchModAux_eq_some_of_step_of_prefix_none`.
      have hrecord :
          Hex.shouldRecordPolynomialFactor (recombinationCandidate d S_cov) =
            true := by
        rw [hrec_eq]
        exact shouldRecordPolynomialFactor_of_irreducible_toPolynomial hf_cov_irr
      have hsearch_step :
          Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors
              (fuel' + 1) =
            some (recombinationCandidate d S_cov :: restFactors) :=
        Hex.recombinationSearchModAux_eq_some_of_step_of_prefix_none
          (target := target)
          (candidate := recombinationCandidate d S_cov)
          (quotient := quotient)
          (modulus := d.p ^ d.k)
          (localFactors := localFactors)
          (selected := liftedSubsetSelectedList d S_cov)
          (rest := liftedSubsetSelectedList d (J \ S_cov))
          (restFactors := restFactors)
          (pre := pre)
          (suffix := suffix)
          (fuel := fuel')
          htarget_eq_one hsplits hprefix rfl hrecord hquot hrest
      refine ⟨recombinationCandidate d S_cov :: restFactors, hsearch_step, ?_⟩
      -- Step 12: universal coverage. Case-split on whether `factor` is
      -- associated to `f_cov`.
      intro factor hfactor_irr hfactor_dvd_target
      by_cases hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov)
      · -- Case A: `factor ~ f_cov`. Emitted witness is `f_cov` itself.
        refine ⟨recombinationCandidate d S_cov, by simp, ?_⟩
        rw [hrec_eq]
        exact hassoc.symm
      · -- Case B: `factor ≁ f_cov`. Then `factor ∣ quotient` (UFD splitting on
        -- `factor ∣ quotient * f_cov`, with the `factor ∣ f_cov` branch ruled
        -- out by the not-associated hypothesis).
        have hfactor_dvd_quotient : factor ∣ quotient := by
          have hfactor_poly_dvd_target :
              HexPolyZMathlib.toPolynomial factor ∣
                HexPolyZMathlib.toPolynomial target :=
            HexPolyMathlib.toPolynomial_dvd hfactor_dvd_target
          have hfactor_poly_prime :
              Prime (HexPolyZMathlib.toPolynomial factor) :=
            UniqueFactorizationMonoid.irreducible_iff_prime.mp hfactor_irr
          have hfactor_poly_dvd_prod :
              HexPolyZMathlib.toPolynomial factor ∣
                HexPolyZMathlib.toPolynomial quotient *
                  HexPolyZMathlib.toPolynomial f_cov := by
            rw [hquot_poly_eq]; exact hfactor_poly_dvd_target
          rcases hfactor_poly_prime.dvd_or_dvd hfactor_poly_dvd_prod with
            hdvd_quot_poly | hdvd_fcov_poly
          · -- `toPolynomial factor ∣ toPolynomial quotient`. Pull back via
            -- `ofPolynomial`.
            rcases hdvd_quot_poly with ⟨r, hr⟩
            refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
            apply HexPolyZMathlib.equiv.injective
            simp only [HexPolyZMathlib.equiv_apply,
              HexPolyZMathlib.toPolynomial_mul,
              HexPolyZMathlib.toPolynomial_ofPolynomial]
            exact hr
          · -- `toPolynomial factor ∣ toPolynomial f_cov` and both irreducible
            -- gives `Associated`, contradicting `hassoc`.
            exact absurd (hfactor_irr.associated_of_dvd hf_cov_irr hdvd_fcov_poly)
              hassoc
        obtain ⟨emitted, hemitted_mem, hemitted_assoc⟩ :=
          hrest_covers factor hfactor_irr hfactor_dvd_quotient
        exact ⟨emitted, List.mem_cons_of_mem _ hemitted_mem, hemitted_assoc⟩

/--
Universal-quantifier auxiliary for the recursive coverage capstone (#4301):
under a `LiftedFactorSubsetPartition core d J target` rest-state predicate,
`Hex.recombinationSearchModAux` returns `some result` and **every**
irreducible integer divisor of `target` is associated to some emitted
candidate in `result`.

The deliverable theorem
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
specialises this universal statement to a fixed `factor` hypothesis.

Proof outline (induction on `fuel`):
* `fuel = 0`: `J.card < 0` is impossible.
* `fuel = fuel' + 1`:
  - If `J = ∅`: the partition's inherited `exists_subset` forces every
    irreducible divisor of `target` to be represented by `∅`, contradicting
    `not_represents_empty_of_irreducible_dvd_core`. Therefore `target` has
    no irreducible divisors; combined with `target` monic and
    `target ∣ core`, this gives `target = 1` and the executable returns
    `some []`. The universal claim is vacuous (no irreducibles divide 1).
  - If `J` is nonempty: `LiftedFactorSubsetPartition.cover_at_min` provides
    an irreducible divisor `f_cov` of `target` whose representing subset
    `S_cov` contains `J.min'`. The recovery theorem
    `recombinationCandidate_eq_factor_of_recovery_of_monic_core` identifies
    `recombinationCandidate d S_cov = f_cov`; the executable split membership
    comes from `liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches`;
    the prefix-none obligation is discharged by
    `liftedFactorSubsetPartition_prefix_none` (with nodup from
    `LiftedFactorListMatches.nodup_of_injOn`); the partition transports via
    `liftedFactorSubsetPartition_transport` and matches via
    `LiftedFactorListMatches.sdiff_of_subset`. The inductive hypothesis on
    `(quotient, J \ S_cov)` then both supplies the recursive-rest success
    witness and covers every irreducible divisor of `quotient`. For an
    arbitrary irreducible `factor ∣ target`, the partition's
    `pairwise_disjoint` (contrapositive via the shared `S_cov` ownership of
    `J.min'`) and `unique_up_to_associated` fields decide whether
    `factor` is associated to `f_cov` (in which case `f_cov` itself is the
    emitted witness) or `factor ∣ quotient` (in which case the inductive
    hypothesis supplies the witness in the recursive tail).

This is the `defaultFactorCoeffBound core`-instantiated thin wrapper for
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`:
the universal coefficient bound for `g ∣ core` is discharged by
`defaultFactorCoeffBound_valid` itself.
-/
private theorem recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {fuel : Nat},
      Hex.DensePoly.Monic target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      J.card < fuel →
      ∃ result,
        Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors fuel =
          some result ∧
        ∀ factor : Hex.ZPoly,
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ target →
          ∃ emitted ∈ result,
            Associated (HexPolyZMathlib.toPolynomial emitted)
              (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors fuel htarget_monic htarget_dvd_core hpartition
    hmatches hfuel
  exact recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_monic htarget_dvd_core hpartition hmatches hfuel

/--
Abstract-bound variant of
`scaledRecombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. The proof body otherwise mirrors the (now-wrapper) original
verbatim: at each of the five `_of_bound` supporting lemma call sites
(`not_represents_empty_..._of_primitive_pos_lc_core_of_bound` in the
empty-`J` step, `representsIntegerFactorAtLift_primitive_of_bound` and
`scaledRecombinationCandidate_eq_factor_of_recovery_of_bound` at the
cover-at-min recovery, `natDegree_toPolynomial_eq_sum_of_represents_..._of_bound`
for the natDegree positivity, and
`liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_scaled_of_bound`
for the prefix-none discharge), the per-factor `hvalid` is specialised
to the local divisor (`g` in the empty-`J` step, `f_cov` for the other
three per-factor callers) by `hvalid g hg_dvd_core` /
`hvalid f_cov hf_cov_dvd_core`, while the prefix-none caller receives
the universal `hvalid`, `hcore_lc_le`, `B'`, and `hprecision`
unchanged. In the recursive IH call, the outer abstract-bound
hypotheses are captured by closure.
-/
private theorem scaledRecombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {fuel : Nat},
      Hex.ZPoly.Primitive target →
      0 < Hex.DensePoly.leadingCoeff target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      J.card < fuel →
      ∃ result,
        Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
            target (d.p ^ d.k) localFactors fuel =
          some result ∧
        ∀ factor : Hex.ZPoly,
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ target →
          ∃ emitted ∈ result,
            Associated (HexPolyZMathlib.toPolynomial emitted)
              (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors fuel htarget_primitive htarget_lc_pos
    htarget_dvd_core hpartition hmatches hfuel
  induction fuel generalizing target J localFactors with
  | zero => omega
  | succ fuel' ih =>
    by_cases htarget_eq_one : target = 1
    · subst htarget_eq_one
      refine ⟨[], ?_, ?_⟩
      · show Hex.scaledRecombinationSearchModAux
            (Hex.DensePoly.leadingCoeff core) 1 (d.p ^ d.k)
            localFactors (fuel' + 1) = some []
        unfold Hex.scaledRecombinationSearchModAux
        simp
      · intro factor hirr hdvd
        exfalso
        have hfactor_dvd_one_poly :
            HexPolyZMathlib.toPolynomial factor ∣ (1 : Polynomial ℤ) := by
          rw [show (1 : Polynomial ℤ) = HexPolyZMathlib.toPolynomial 1 from
            toPolynomial_one_zpoly.symm]
          exact HexPolyMathlib.toPolynomial_dvd hdvd
        exact hirr.not_isUnit (isUnit_of_dvd_one hfactor_dvd_one_poly)
    · have htarget_poly_ne_one :
          HexPolyZMathlib.toPolynomial target ≠ 1 := by
        intro h
        apply htarget_eq_one
        apply HexPolyZMathlib.equiv.injective
        show HexPolyZMathlib.toPolynomial target =
          HexPolyZMathlib.toPolynomial 1
        rw [toPolynomial_one_zpoly]
        exact h
      have htarget_poly_nonunit :
          ¬ IsUnit (HexPolyZMathlib.toPolynomial target) := by
        intro hunit
        exact htarget_eq_one
          (zpoly_eq_one_of_toPolynomial_isUnit_of_pos_lc htarget_lc_pos hunit)
      have htarget_poly_ne :
          HexPolyZMathlib.toPolynomial target ≠ 0 := by
        intro hzero
        apply zpoly_ne_zero_of_pos_lc htarget_lc_pos
        apply HexPolyZMathlib.equiv.injective
        show HexPolyZMathlib.toPolynomial target =
          HexPolyZMathlib.toPolynomial 0
        rw [HexPolyZMathlib.toPolynomial_zero]
        exact hzero
      have hJ_ne : J.Nonempty := by
        by_contra hJ_empty
        rw [Finset.not_nonempty_iff_eq_empty] at hJ_empty
        obtain ⟨gPoly, hg_irr, hg_dvd_target_poly⟩ :=
          WfDvdMonoid.exists_irreducible_factor htarget_poly_nonunit
            htarget_poly_ne
        let g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial gPoly
        have hg_toPolynomial : HexPolyZMathlib.toPolynomial g = gPoly :=
          HexPolyZMathlib.toPolynomial_ofPolynomial gPoly
        have hg_dvd_target : g ∣ target := by
          rcases hg_dvd_target_poly with ⟨r, hr⟩
          refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
          apply HexPolyZMathlib.equiv.injective
          simp only [HexPolyZMathlib.equiv_apply,
            HexPolyZMathlib.toPolynomial_mul,
            HexPolyZMathlib.toPolynomial_ofPolynomial]
          rw [hg_toPolynomial]
          exact hr
        have hg_irr_toPoly :
            Irreducible (HexPolyZMathlib.toPolynomial g) := by
          rw [hg_toPolynomial]; exact hg_irr
        obtain ⟨S, hSJ, hSrep⟩ :=
          hpartition.exists_subset hg_irr_toPoly hg_dvd_target
        have hS_empty : S = ∅ := by
          rw [hJ_empty] at hSJ
          exact Finset.subset_empty.mp hSJ
        have hg_dvd_core : g ∣ core :=
          zpoly_dvd_trans hg_dvd_target htarget_dvd_core
        apply not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound
          B' (hvalid g hg_dvd_core) hcore_ne hcore_primitive hcore_lc_pos
          hcore_lc_le hg_dvd_core hg_irr_toPoly hprecision
        rw [← hS_empty]; exact hSrep
      obtain ⟨f_cov, S_cov, hf_cov_irr, hf_cov_dvd_target, hS_cov_J,
              hmin_in_S_cov, hS_cov_rep⟩ :=
        hpartition.cover_at_min hJ_ne
      have hf_cov_dvd_core : f_cov ∣ core :=
        zpoly_dvd_trans hf_cov_dvd_target htarget_dvd_core
      obtain ⟨hf_cov_primitive, hf_cov_lc_pos⟩ :=
        representsIntegerFactorAtLift_primitive_of_bound
          B' (hvalid f_cov hf_cov_dvd_core) hcore_lc_le hcore_ne
          hcore_primitive hcore_lc_pos hd_liftedFactor_monic
          hf_cov_dvd_target htarget_dvd_core hS_cov_rep hprecision
      have hf_cov_content : Hex.ZPoly.content f_cov = 1 := hf_cov_primitive
      have hf_cov_norm : Hex.normalizeFactorSign f_cov = f_cov := by
        unfold Hex.normalizeFactorSign
        rw [if_neg (by omega)]
      have hrec_eq : scaledRecombinationCandidate core d S_cov = f_cov :=
        scaledRecombinationCandidate_eq_factor_of_recovery_of_bound
          B' (hvalid f_cov hf_cov_dvd_core) hcore_ne hf_cov_content
          hf_cov_norm hS_cov_rep hprecision
      have hf_cov_natDeg_pos :
          0 < (HexPolyZMathlib.toPolynomial f_cov).natDegree := by
        rw [natDegree_toPolynomial_eq_sum_of_represents_of_primitive_pos_lc_core_of_bound
          B' (hvalid f_cov hf_cov_dvd_core) hcore_lc_le hcore_ne
          hcore_primitive hcore_lc_pos hd_liftedFactor_monic
          hf_cov_dvd_core hf_cov_irr hf_cov_content hf_cov_norm
          hS_cov_rep hprecision]
        apply Finset.sum_pos (fun i _ => hd_liftedFactor_natDegree_pos i)
        exact ⟨J.min' hJ_ne, hmin_in_S_cov⟩
      have hf_cov_degree_pos : 0 < f_cov.degree?.getD 0 := by
        rw [← HexPolyMathlib.natDegree_toPolynomial]
        exact hf_cov_natDeg_pos
      obtain ⟨quotient, hquot, hmul⟩ :=
        exactQuotient?_scaledRecombinationCandidate_eq_some_of_eq_factor_of_primitive_pos_lc
          hrec_eq hf_cov_lc_pos hf_cov_degree_pos hf_cov_dvd_target
      have hquot_eq : quotient * f_cov = target := hrec_eq ▸ hmul
      have hquot_poly_eq :
          HexPolyZMathlib.toPolynomial quotient *
              HexPolyZMathlib.toPolynomial f_cov =
            HexPolyZMathlib.toPolynomial target := by
        rw [← HexPolyZMathlib.toPolynomial_mul, hquot_eq]
      have hquot_dvd_target : quotient ∣ target :=
        ⟨f_cov, hquot_eq.symm⟩
      have hquot_dvd_core : quotient ∣ core :=
        zpoly_dvd_trans hquot_dvd_target htarget_dvd_core
      have hquot_primitive : Hex.ZPoly.Primitive quotient :=
        zpoly_primitive_of_dvd_primitive_basic htarget_primitive hquot_dvd_target
      have hquot_lc_pos : 0 < Hex.DensePoly.leadingCoeff quotient :=
        zpoly_left_pos_lc_of_mul_eq_of_pos_lc hquot_eq hf_cov_lc_pos
          htarget_lc_pos
      have hpartition_new :
          LiftedFactorSubsetPartition core d (J \ S_cov) quotient :=
        liftedFactorSubsetPartition_transport hpartition hquot_eq hS_cov_rep
          hS_cov_J hf_cov_irr hf_cov_dvd_target
      have hmatches_new :
          LiftedFactorListMatches d (J \ S_cov)
            (liftedSubsetSelectedList d (J \ S_cov)) :=
        LiftedFactorListMatches.sdiff_of_subset
      have hcard_new : (J \ S_cov).card < fuel' := by
        have hmin_not_in_sdiff : J.min' hJ_ne ∉ J \ S_cov := by
          intro h
          exact (Finset.mem_sdiff.mp h).2 hmin_in_S_cov
        have hsub_strict : J \ S_cov ⊂ J := by
          refine ⟨Finset.sdiff_subset, fun hsub => hmin_not_in_sdiff ?_⟩
          exact hsub (J.min'_mem hJ_ne)
        have : (J \ S_cov).card < J.card := Finset.card_lt_card hsub_strict
        omega
      obtain ⟨restFactors, hrest, hrest_covers⟩ :=
        ih hquot_primitive hquot_lc_pos hquot_dvd_core hpartition_new
          hmatches_new hcard_new
      have hsplit_mem :
          (liftedSubsetSelectedList d S_cov,
              liftedSubsetSelectedList d (J \ S_cov)) ∈
            Hex.subsetSplitsWithFirst localFactors :=
        liftedSubsetSplit_mem_subsetSplitsWithFirst_of_matches
          hmatches hS_cov_J hJ_ne hmin_in_S_cov
      obtain ⟨pre, suffix, hsplits⟩ := List.append_of_mem hsplit_mem
      have hlocal_nodup : localFactors.Nodup :=
        hmatches.nodup_of_injOn hd_liftedFactor_inj.injOn
      have hprefix :=
        liftedFactorSubsetPartition_prefix_none_of_primitive_pos_lc_core_scaled_of_bound
          B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos
          hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
          hprecision htarget_dvd_core hpartition hmatches hlocal_nodup
          hf_cov_irr hf_cov_dvd_target hS_cov_rep hS_cov_J hJ_ne
          hmin_in_S_cov hsplits (fuel := fuel')
      have hrecord :
          Hex.shouldRecordPolynomialFactor
              (scaledRecombinationCandidate core d S_cov) =
            true :=
        shouldRecord_scaledRecombinationCandidate_of_eq_factor
          hrec_eq hf_cov_irr
      have hcandidate_def :
          scaledRecombinationCandidate core d S_cov =
            Hex.normalizeFactorSign
              (Hex.ZPoly.primitivePart
                (Hex.centeredLiftPoly
                  (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
                    (Array.polyProduct
                      (liftedSubsetSelectedList d S_cov).toArray))
                  (d.p ^ d.k))) := by
        unfold scaledRecombinationCandidate scaledLiftedFactorProduct
        rw [polyProduct_liftedSubsetSelectedList_eq_liftedFactorProduct]
      have hsearch_step :
          Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
              target (d.p ^ d.k) localFactors (fuel' + 1) =
            some (scaledRecombinationCandidate core d S_cov :: restFactors) :=
        Hex.scaledRecombinationSearchModAux_eq_some_of_step_of_prefix_none
          (target := target)
          (candidate := scaledRecombinationCandidate core d S_cov)
          (quotient := quotient)
          (modulus := d.p ^ d.k)
          (localFactors := localFactors)
          (selected := liftedSubsetSelectedList d S_cov)
          (rest := liftedSubsetSelectedList d (J \ S_cov))
          (restFactors := restFactors)
          (pre := pre)
          (suffix := suffix)
          (fuel := fuel')
          htarget_eq_one hsplits hprefix hcandidate_def hrecord hquot hrest
      refine ⟨scaledRecombinationCandidate core d S_cov :: restFactors,
        hsearch_step, ?_⟩
      intro factor hfactor_irr hfactor_dvd_target
      by_cases hassoc :
          Associated (HexPolyZMathlib.toPolynomial factor)
            (HexPolyZMathlib.toPolynomial f_cov)
      · refine ⟨scaledRecombinationCandidate core d S_cov, by simp, ?_⟩
        rw [hrec_eq]
        exact hassoc.symm
      · have hfactor_dvd_quotient : factor ∣ quotient := by
          have hfactor_poly_dvd_target :
              HexPolyZMathlib.toPolynomial factor ∣
                HexPolyZMathlib.toPolynomial target :=
            HexPolyMathlib.toPolynomial_dvd hfactor_dvd_target
          have hfactor_poly_prime :
              Prime (HexPolyZMathlib.toPolynomial factor) :=
            UniqueFactorizationMonoid.irreducible_iff_prime.mp hfactor_irr
          have hfactor_poly_dvd_prod :
              HexPolyZMathlib.toPolynomial factor ∣
                HexPolyZMathlib.toPolynomial quotient *
                  HexPolyZMathlib.toPolynomial f_cov := by
            rw [hquot_poly_eq]; exact hfactor_poly_dvd_target
          rcases hfactor_poly_prime.dvd_or_dvd hfactor_poly_dvd_prod with
            hdvd_quot_poly | hdvd_fcov_poly
          · rcases hdvd_quot_poly with ⟨r, hr⟩
            refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
            apply HexPolyZMathlib.equiv.injective
            simp only [HexPolyZMathlib.equiv_apply,
              HexPolyZMathlib.toPolynomial_mul,
              HexPolyZMathlib.toPolynomial_ofPolynomial]
            exact hr
          · exact absurd (hfactor_irr.associated_of_dvd hf_cov_irr hdvd_fcov_poly)
              hassoc
        obtain ⟨emitted, hemitted_mem, hemitted_assoc⟩ :=
          hrest_covers factor hfactor_irr hfactor_dvd_quotient
        exact ⟨emitted, List.mem_cons_of_mem _ hemitted_mem, hemitted_assoc⟩

/--
Primitive + positive-leading analogue of
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition`.

This is the scaled recursive coverage auxiliary for primitive non-monic cores:
the executable step is `Hex.scaledRecombinationSearchModAux`, candidates are
identified by `scaledRecombinationCandidate_eq_factor_of_recovery`, and the
recursive target invariant is `Hex.ZPoly.Primitive target` plus positive
leading coefficient instead of monicity.

Thin wrapper over
`scaledRecombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`.
-/
private theorem scaledRecombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition
    {core : Hex.ZPoly} {d : Hex.LiftData}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∀ {target : Hex.ZPoly} {J : LiftedFactorSubset d}
      {localFactors : List Hex.ZPoly} {fuel : Nat},
      Hex.ZPoly.Primitive target →
      0 < Hex.DensePoly.leadingCoeff target →
      target ∣ core →
      LiftedFactorSubsetPartition core d J target →
      LiftedFactorListMatches d J localFactors →
      J.card < fuel →
      ∃ result,
        Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
            target (d.p ^ d.k) localFactors fuel =
          some result ∧
        ∀ factor : Hex.ZPoly,
          Irreducible (HexPolyZMathlib.toPolynomial factor) →
          factor ∣ target →
          ∃ emitted ∈ result,
            Associated (HexPolyZMathlib.toPolynomial emitted)
              (HexPolyZMathlib.toPolynomial factor) := by
  intro target J localFactors fuel htarget_primitive htarget_lc_pos
    htarget_dvd_core hpartition hmatches hfuel
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact scaledRecombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches hfuel

/--
Abstract-bound variant of
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. Thin wrapper over
`recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`
that extracts the per-factor coverage at the supplied `factor`.
-/
theorem recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_monic : Hex.DensePoly.Monic target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  obtain ⟨result, hresult, hcovers⟩ :=
    recombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
      B' hvalid hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
      hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
      htarget_monic htarget_dvd_core hpartition hmatches hfuel
  exact ⟨result, hresult, hcovers factor hfactor_irr hfactor_dvd_target⟩

/--
Recursive coverage capstone for `Hex.recombinationSearchModAux` (#4301).

Given a `LiftedFactorSubsetPartition core d J target` rest-state predicate at
a recursive recombination level, and an irreducible integer divisor `factor`
of `target`, the executable recombination search returns `some result` with
`factor` (up to `Associated`) among the emitted candidates.

Thin wrapper over
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via
`defaultFactorCoeffBound_leadingCoeff_natAbs_le` paired with
`defaultFactorCoeffBound_valid`. -/
theorem recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (hcore_ne : core ≠ 0)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_monic : Hex.DensePoly.Monic target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.recombinationSearchModAux target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_monic hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_monic htarget_dvd_core hpartition hmatches
    hfactor_irr hfactor_dvd_target hfuel

/--
Abstract-bound variant of
`scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. Thin wrapper over
`scaledRecombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound`
that extracts the per-factor coverage at the supplied `factor`.
-/
theorem scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  obtain ⟨result, hresult, hcovers⟩ :=
    scaledRecombinationSearchModAux_some_and_covers_of_liftedFactorSubsetPartition_of_bound
      B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos hd_modulus
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
      hprecision htarget_primitive htarget_lc_pos htarget_dvd_core hpartition
      hmatches hfuel
  exact ⟨result, hresult, hcovers factor hfactor_irr hfactor_dvd_target⟩

/--
Primitive + positive-leading recursive coverage capstone for
`Hex.scaledRecombinationSearchModAux`.

This is the scaled counterpart of
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`.
It keeps the same fixed-factor conclusion, but the recursive target invariant is
primitive plus positive leading coefficient, and the executable boundary is the
scaled recombination search.

Thin wrapper over
`scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`.
-/
theorem scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
    hfactor_irr hfactor_dvd_target hfuel

/--
Abstract-bound variant of
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. Thin wrapper that forwards verbatim to
`scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound`.
-/
theorem recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core_of_bound
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * B' < d.p ^ d.k)
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  exact
    scaledRecombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_bound
      B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos hd_modulus
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
      hprecision htarget_primitive htarget_lc_pos htarget_dvd_core hpartition
      hmatches hfactor_irr hfactor_dvd_target hfuel

/--
Primitive + positive-leading public wrapper for the scaled recombination
search.  This is the #4648 boundary form of the old monic-core
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
surface: callers with a primitive positive-leading core and recursive target
use the scaled executable search directly, while the monic wrapper remains
available for existing unscaled callers.

Thin wrapper over
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`.
-/
theorem recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core
    {core target factor : Hex.ZPoly} {d : Hex.LiftData}
    {J : LiftedFactorSubset d} {localFactors : List Hex.ZPoly} {fuel : Nat}
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k)
    (htarget_primitive : Hex.ZPoly.Primitive target)
    (htarget_lc_pos : 0 < Hex.DensePoly.leadingCoeff target)
    (htarget_dvd_core : target ∣ core)
    (hpartition : LiftedFactorSubsetPartition core d J target)
    (hmatches : LiftedFactorListMatches d J localFactors)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hfactor_dvd_target : factor ∣ target)
    (hfuel : J.card < fuel) :
    ∃ result,
      Hex.scaledRecombinationSearchModAux (Hex.DensePoly.leadingCoeff core)
          target (d.p ^ d.k) localFactors fuel =
        some result ∧
      ∃ emitted ∈ result,
        Associated (HexPolyZMathlib.toPolynomial emitted)
          (HexPolyZMathlib.toPolynomial factor) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core_of_bound
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le
    (defaultFactorCoeffBound_valid core hcore_ne)
    hcore_ne hcore_primitive hcore_lc_pos hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj hprecision
    htarget_primitive htarget_lc_pos htarget_dvd_core hpartition hmatches
    hfactor_irr hfactor_dvd_target hfuel

/--
Abstract-bound variant of
`exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. The proof body mirrors the (now-wrapper) original verbatim,
except that the forward call to
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core`
becomes its `_of_bound` sibling, threading `B'`, `hcore_lc_le`,
`hvalid`, `hprecision`.
-/
theorem exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence_of_bound
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hB_ne_zero : B ≠ 0)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∃ emitted ∈
      (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
      Associated
        (HexPolyZMathlib.toPolynomial emitted)
        (HexPolyZMathlib.toPolynomial factor) := by
  have hmatches :
      LiftedFactorListMatches d Finset.univ d.liftedFactors.toList :=
    LiftedFactorListMatches.univ d
  have hfuel : (Finset.univ : LiftedFactorSubset d).card <
      d.liftedFactors.toList.length + 1 := by
    rw [← LiftedFactorListMatches.length_eq_card hmatches]
    exact Nat.lt_succ_self _
  obtain ⟨result, hsearchAux, emitted, hemitted_mem, hassoc⟩ :=
    recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition_of_primitive_pos_lc_core_of_bound
      (J := Finset.univ)
      (fuel := d.liftedFactors.toList.length + 1)
      B' hcore_lc_le hvalid hcore_ne hcore_primitive hcore_lc_pos hd_modulus
      hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
      hprecision hcore_primitive hcore_lc_pos (Hex.DensePoly.dvd_refl_poly core)
      hpartition hmatches hirr hdvd hfuel
  have hsearchMod :
      Hex.scaledRecombinationSearchMod (Hex.DensePoly.leadingCoeff core) core
          (d.p ^ d.k) d.liftedFactors.toList =
        some result := by
    unfold Hex.scaledRecombinationSearchMod
    exact hsearchAux
  refine ⟨emitted, ?_, hassoc⟩
  exact
    exhaustiveCoreFactorsWithBound_mem_of_scaledRecombinationSearchMod_some
      (B := B) hB_ne_zero h.lift_eq hsearchMod hemitted_mem

/--
Final public coverage theorem (#4274 capstone): every irreducible integer
divisor of `core` appears, up to `Associated`, among the factors emitted by
`Hex.exhaustiveCoreFactorsWithBound`.

Composes
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
(#4524) with `exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some`
at `J = Finset.univ`, `target = core`, `localFactors = d.liftedFactors.toList`,
`fuel = d.liftedFactors.toList.length + 1`.

The initial-state `LiftedFactorSubsetPartition core d Finset.univ core` is
threaded as a hypothesis: building it from `HenselSubsetCorrespondenceHypotheses`
plus square-free reduction is a separable downstream task (cf. the
`LiftedFactorSubsetPartition` doc-comment).

The `B` parameter of `Hex.exhaustiveCoreFactorsWithBound core B primeData` is
the raw coefficient bound, distinct from the precision exponent
`Hex.precisionForCoeffBound B primeData.p` that appears inside
`HenselSubsetCorrespondenceHypotheses` and matches the wrapper's inner Hensel
lift call.  The Mignotte invariant
`2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k` is supplied as
`hprecision`; callers wiring `B = Hex.ZPoly.defaultFactorCoeffBound core`
discharge it from the `precisionForCoeffBound` definition directly.  Callers
wiring a larger `B` (e.g. the public outer
`Hex.ZPoly.defaultFactorCoeffBound f` used by `Hex.factor f`) should call the
abstract-bound sibling
`exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence_of_bound`
directly: it accepts an abstract bound `B'` and discharges the validity
hypothesis via `defaultFactorCoeffBound_valid` paired with
`leadingCoeff_eq_coeff_last`, bypassing any monotonicity step.

Thin wrapper over
`exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`.
-/
theorem exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hB_ne_zero : B ≠ 0)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∃ emitted ∈
      (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
      Associated
        (HexPolyZMathlib.toPolynomial emitted)
        (HexPolyZMathlib.toPolynomial factor) := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence_of_bound
    h hpartition hcore_ne hcore_primitive hcore_lc_pos hB_ne_zero hd_modulus
    hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
    hirr hdvd (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le (defaultFactorCoeffBound_valid core hcore_ne) hprecision

/--
Abstract-bound variant of
`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`:
the concrete `2 * defaultFactorCoeffBound core < d.p ^ d.k` Mignotte
precision is replaced by `2 * B' < d.p ^ d.k` against an abstract bound
`B'`, paired with the leading-coefficient bound on `core` and the
universal divisor coefficient bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs
≤ B'`. The proof body mirrors the (now-wrapper) original verbatim,
except that the forward call to
`exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence`
becomes its `_of_bound` sibling, threading `B'`, `hcore_lc_le`,
`hvalid`, `hprecision`.
-/
theorem exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hB_ne_zero : B ≠ 0)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision : 2 * B' < d.p ^ d.k) :
    ∀ factor ∈
      (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
      Hex.ZPoly.Irreducible factor := by
  set coreFactors := Hex.exhaustiveCoreFactorsWithBound core B primeData
    with hcoreFactors_def
  set f := HexPolyZMathlib.toPolynomial core with hf_def
  have hf_ne : f ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa [hf_def] using hzero
  have hcore_squarefree : Squarefree f := hpartition.target_squarefree
  set gs : List (Polynomial ℤ) :=
    coreFactors.toList.map HexPolyZMathlib.toPolynomial with hgs_def
  -- Coverage at the `Polynomial ℤ` level for each `q ∈ normalizedFactors f`.
  have hcoverage : ∀ q ∈ UniqueFactorizationMonoid.normalizedFactors f,
      ∃ g ∈ gs, Associated g q := by
    intro q hq
    have hq_irr : Irreducible q :=
      UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq
    have hq_dvd : q ∣ f :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq
    set factor : Hex.ZPoly := HexPolyZMathlib.ofPolynomial q with hfactor_def
    have htoP : HexPolyZMathlib.toPolynomial factor = q := by
      simp [hfactor_def]
    have hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor) := by
      rw [htoP]; exact hq_irr
    have hfactor_dvd : factor ∣ core := by
      rcases hq_dvd with ⟨r, hr⟩
      refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
      apply HexPolyZMathlib.equiv.injective
      show HexPolyZMathlib.toPolynomial core =
        HexPolyZMathlib.toPolynomial (factor * HexPolyZMathlib.ofPolynomial r)
      rw [HexPolyZMathlib.toPolynomial_mul, htoP,
        HexPolyZMathlib.toPolynomial_ofPolynomial, ← hf_def]
      exact hr
    obtain ⟨emitted, hemitted_mem, hassoc⟩ :=
      exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence_of_bound
        h hpartition hcore_ne hcore_primitive hcore_lc_pos hB_ne_zero hd_modulus
        hd_liftedFactor_monic hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
        hfactor_irr hfactor_dvd B' hcore_lc_le hvalid hprecision
    refine ⟨HexPolyZMathlib.toPolynomial emitted, ?_, ?_⟩
    · rw [hgs_def, List.mem_map]
      refine ⟨emitted, ?_, rfl⟩
      simpa [hcoreFactors_def] using hemitted_mem
    · rw [htoP] at hassoc
      exact hassoc
  -- Count lower bound from coverage.
  have hcount_ge :
      (UniqueFactorizationMonoid.normalizedFactors f).card ≤ gs.length :=
    HexBerlekampZassenhausMathlib.UFDPartition.normalizedFactors_card_le_length_of_coverage
      hf_ne hcore_squarefree gs hcoverage
  -- Count upper bound from the existing UFD wrapper.
  have hcount_le : gs.length ≤
      (UniqueFactorizationMonoid.normalizedFactors f).card := by
    have := exhaustiveCoreFactorsWithBound_factor_count_le
      (core := core) (B := B) (primeData := primeData) hcore_ne hcore_record
    simpa [hgs_def, hf_def, hcoreFactors_def] using this
  have hcount_eq :
      (coreFactors.toList.map HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial core)).card := by
    have : gs.length =
        (UniqueFactorizationMonoid.normalizedFactors f).card :=
      le_antisymm hcount_le hcount_ge
    simpa [hgs_def, hf_def] using this
  intro factor hfactor_mem
  refine exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_count
    (core := core) (B := B) (primeData := primeData)
    hcore_ne hcore_record hcount_eq factor ?_
  simpa [hcoreFactors_def] using hfactor_mem

/-- **#4006 slow-path capstone.**

Branch-local irreducibility for the exhaustive square-free-core branch:
every factor emitted by `Hex.exhaustiveCoreFactorsWithBound core
(Hex.ZPoly.defaultFactorCoeffBound core) primeData` is irreducible in
`Hex.ZPoly` whenever the standard good-prime / Hensel / recombination
hypothesis set (`HenselSubsetCorrespondenceHypotheses` and
`LiftedFactorSubsetPartition` at the full-universe subset) holds for
a square-free, monic core.

The argument composes three landed pieces:

* `exhaustiveCoreFactorsWithBound_coverage_of_henselSubsetCorrespondence`
  (#4274), which produces, for every irreducible `Polynomial ℤ` divisor
  of `core`, an emitted factor associated to it.
* `UFDPartition.normalizedFactors_card_le_length_of_coverage`, which
  converts that coverage (under square-freeness of `toPolynomial core`)
  into the lower count bound `card (normalizedFactors (toPolynomial core))
  ≤ (emitted.map toPolynomial).length`.
* `exhaustiveCoreFactorsWithBound_factor_count_le`, which supplies the
  matching upper count bound; together they yield the count equality
  consumed by `exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_count`.

The square-freeness of `toPolynomial core` is read off
`hpartition.target_squarefree` at `target = core`, so the only new
input beyond the coverage signature is `hcore_record`, required by the
existing UFD count-le wrapper.

Thin wrapper over
`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`. -/
theorem exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence
    {core : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (h :
      HenselSubsetCorrespondenceHypotheses core B primeData d
        admissiblePrime successfulLift)
    (hpartition :
      LiftedFactorSubsetPartition core d Finset.univ core)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_record : Hex.shouldRecordPolynomialFactor core = true)
    (hB_ne_zero : B ≠ 0)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    ∀ factor ∈
      (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList,
      Hex.ZPoly.Irreducible factor := by
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
    h hpartition hcore_ne hcore_primitive hcore_lc_pos hcore_record hB_ne_zero
    hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
    hd_liftedFactor_inj (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le (defaultFactorCoeffBound_valid core hcore_ne) hprecision

/-- Mathlib-side irreducibility transports through `Hex.normalizeFactorSign`:
the sign normalisation differs from the input by at most a `(-1)` factor, so
the transported polynomial differs by the unit `-1` and `Associated.irreducible`
applies. -/
private theorem polynomialIrreducible_toPolynomial_normalizeFactorSign_of_zpolyIrreducible
    {f : Hex.ZPoly} (hirr : Hex.ZPoly.Irreducible f) :
    Irreducible (HexPolyZMathlib.toPolynomial (Hex.normalizeFactorSign f)) := by
  have hirr_poly : Irreducible (HexPolyZMathlib.toPolynomial f) :=
    (Hex.ZPoly.Irreducible_iff_polynomialIrreducible f).mp hirr
  unfold Hex.normalizeFactorSign
  by_cases hlc : Hex.DensePoly.leadingCoeff f < 0
  · rw [if_pos hlc]
    have hzero_mul : (-1 : Int) * (0 : Int) = 0 := by simp
    have heq :
        HexPolyZMathlib.toPolynomial (Hex.DensePoly.scale (-1 : Int) f) =
          -HexPolyZMathlib.toPolynomial f := by
      ext n
      rw [HexPolyZMathlib.coeff_toPolynomial,
        Hex.DensePoly.coeff_scale (-1 : Int) f n hzero_mul,
        Polynomial.coeff_neg, HexPolyZMathlib.coeff_toPolynomial]
      ring
    rw [heq]
    exact
      (Associated.neg_right (Associated.refl (HexPolyZMathlib.toPolynomial f))).irreducible
        hirr_poly
  · rw [if_neg hlc]
    exact hirr_poly

/-- `Hex.ZPoly.Irreducible` is preserved by `Hex.normalizeFactorSign`.

Exposed publicly so the assembled per-branch output theorem can lift raw
factor irreducibility to entry irreducibility (entries pass through
`collectFactorMultiplicities`, which normalises each raw factor's sign). -/
theorem zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible
    {f : Hex.ZPoly} (hirr : Hex.ZPoly.Irreducible f) :
    Hex.ZPoly.Irreducible (Hex.normalizeFactorSign f) :=
  (Hex.ZPoly.Irreducible_iff_polynomialIrreducible _).mpr
    (polynomialIrreducible_toPolynomial_normalizeFactorSign_of_zpolyIrreducible
      hirr)

/-- **#4008 assembled per-branch output theorem.**

Every recorded entry of `Hex.factorWithBound f B` is `Hex.ZPoly.Irreducible`
once each branch's chosen raw factor array is irreducible.  The single
hypothesis `h_raw` is dispatched by the public fast/slow case-split exposed
through `Hex.factorWithBound_entry_mem_raw_source`: it asks the caller to
prove that every raw factor produced by the chosen branch (the fast BHKS
output when `factorFastFactorsWithBound = some _`, or the slow exhaustive
output when `factorFastFactorsWithBound = none`) is `Hex.ZPoly.Irreducible`.
The recorded entry's first component is the `Hex.normalizeFactorSign`-image
of one such raw factor, so `zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible`
discharges the sign-normalisation step.

Combined with the Mathlib-free reassembly lift
`Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`,
the typical downstream caller (e.g. `factorWithBound_entries_irreducible` of
#3987, or the capstone `factor_irreducible_of_nonUnit` of #4170) feeds in
core-factor irreducibility for each sub-branch (singleton, fast-core, slow
exhaustive, quadratic, constant) plus `reassemblyExpansionComplete`, and the
extracted-`X` half is handled automatically by `xPowerFactorArray_irreducible`.

The hypothesis is stated in the symmetric "raw factors are irreducible" form
rather than enumerating each sub-branch because the same raw-to-entry lift
applies uniformly across all branches; case-by-case dispatch lives in the
caller where the supporting per-branch theorems naturally compose. -/
theorem factorWithBound_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible
    {f : Hex.ZPoly} {B : Nat} {entry : Hex.ZPoly × Nat}
    (hmem : entry ∈ (Hex.factorWithBound f B).factors.toList)
    (h_raw :
      ∀ rawFactors : Array Hex.ZPoly,
        (Hex.factorFastFactorsWithBound f B = some rawFactors ∨
          (Hex.factorFastFactorsWithBound f B = none ∧
            rawFactors = Hex.factorSlowFactorsWithBound f B)) →
        ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw) :
    Hex.ZPoly.Irreducible entry.1 := by
  obtain ⟨rawFactors, hsource, raw, hraw_mem, hentry_eq⟩ :=
    Hex.factorWithBound_entry_mem_raw_source f B entry hmem
  rw [hentry_eq]
  exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible
    (h_raw rawFactors hsource raw hraw_mem)

/-- Default-precision specialisation of
`factorWithBound_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible` for
the public `Hex.factor` entry point.  This is the form consumed by the
HO-1 capstone `factor_irreducible_of_nonUnit` (#4170). -/
theorem factor_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible
    {f : Hex.ZPoly} {entry : Hex.ZPoly × Nat}
    (hmem : entry ∈ (Hex.factor f).factors.toList)
    (h_raw :
      ∀ rawFactors : Array Hex.ZPoly,
        (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
            some rawFactors ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            rawFactors =
              Hex.factorSlowFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f))) →
        ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw) :
    Hex.ZPoly.Irreducible entry.1 :=
  factorWithBound_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible
    (B := Hex.ZPoly.defaultFactorCoeffBound f)
    (by simpa [Hex.factor_eq_factorWithBound_default] using hmem)
    h_raw

/-- **#3987 assembled output theorem.**

Every recorded entry of `Hex.factorWithBound f B` is `Hex.ZPoly.Irreducible`,
universally quantified, once each branch's chosen raw factor array is
irreducible.  This is the `∀ entry`-quantified form of #4008's per-entry
output theorem `factorWithBound_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible`,
shaped to match the existing `factor_irreducible_of_nonUnit` signature (Array
membership on `.factors`).

The single hypothesis `h_raw` is dispatched by the public fast/slow case-split
exposed through `Hex.factorWithBound_entry_mem_raw_source`.  The typical
downstream caller composes it from the per-branch core-factor irreducibility
theorems (slow-path exhaustive #4006, small-mod singleton #4200, fast BHKS
#4202, residual-fallback exclusion #4199) via the Mathlib-free reassembly lift
`Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`,
together with `reassemblyExpansionComplete`; the extracted-`X` half of each
branch is handled automatically by the `xPowerFactorArray_irreducible`
foundational witness from #3996.  Unconditional discharge of `h_raw` for the
default-precision path is the capstone task tracked by #4170. -/
theorem factorWithBound_entries_irreducible
    (f : Hex.ZPoly) (B : Nat)
    (h_raw :
      ∀ rawFactors : Array Hex.ZPoly,
        (Hex.factorFastFactorsWithBound f B = some rawFactors ∨
          (Hex.factorFastFactorsWithBound f B = none ∧
            rawFactors = Hex.factorSlowFactorsWithBound f B)) →
        ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw) :
    ∀ entry ∈ (Hex.factorWithBound f B).factors, Hex.ZPoly.Irreducible entry.1 := by
  intro entry hentry
  exact factorWithBound_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible
    (Array.mem_toList_iff.mpr hentry) h_raw

/-- Default-precision specialisation of `factorWithBound_entries_irreducible`
for the public `Hex.factor` entry point.  Matches the signature of
`factor_irreducible_of_nonUnit` (#4170 capstone) modulo the `h_raw` hypothesis;
unconditional discharge of `h_raw` is tracked by #4170. -/
theorem factor_entries_irreducible
    (f : Hex.ZPoly)
    (h_raw :
      ∀ rawFactors : Array Hex.ZPoly,
        (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
            some rawFactors ∨
          (Hex.factorFastFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f) =
              none ∧
            rawFactors =
              Hex.factorSlowFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f))) →
        ∀ raw ∈ rawFactors.toList, Hex.ZPoly.Irreducible raw) :
    ∀ entry ∈ (Hex.factor f).factors, Hex.ZPoly.Irreducible entry.1 := by
  intro entry hentry
  exact factor_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible
    (Array.mem_toList_iff.mpr hentry) h_raw

set_option maxHeartbeats 2000000
/--
Abstract-bound variant of
`factorWithBound_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`:
the concrete `2 * defaultFactorCoeffBound (normalizeForFactor f).squareFreeCore
< d.p ^ d.k` Mignotte precision is replaced by `2 * B' < d.p ^ d.k` against an
abstract bound `B'`, paired with the leading-coefficient bound on
`(normalizeForFactor f).squareFreeCore` and the universal divisor coefficient
bound `∀ g ∣ core, ∀ i, (g.coeff i).natAbs ≤ B'`. The proof body mirrors the
(now-wrapper) original verbatim, except that the forward call to
`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`
becomes its `_of_bound` sibling, threading `B'`, `hcore_lc_le`, `hvalid`,
`hprecision`.
-/
theorem factorWithBound_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
    {f : Hex.ZPoly} {entry : Hex.ZPoly × Nat}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (primeData : Hex.PrimeChoiceData)
    (_hbranch :
      Hex.factorWithBoundUsesExhaustiveBranch f
        (Hex.ZPoly.defaultFactorCoeffBound
          (Hex.normalizeForFactor f).squareFreeCore))
    (_hentry_mem :
      entry ∈ (Hex.factorWithBound f
        (Hex.ZPoly.defaultFactorCoeffBound
          (Hex.normalizeForFactor f).squareFreeCore)).factors.toList)
    (_hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (h :
      HenselSubsetCorrespondenceHypotheses
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound
          (Hex.normalizeForFactor f).squareFreeCore)
        primeData
        d admissiblePrime successfulLift)
    (hpartition :
      LiftedFactorSubsetPartition
        (Hex.normalizeForFactor f).squareFreeCore d Finset.univ
        (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hcore_monic :
      Hex.DensePoly.Monic (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_record :
      Hex.shouldRecordPolynomialFactor
        (Hex.normalizeForFactor f).squareFreeCore = true)
    (hB_ne_zero :
      Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (B' : Nat)
    (hcore_lc_le :
      (Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore).natAbs ≤ B')
    (hvalid :
      ∀ g : Hex.ZPoly, g ∣ (Hex.normalizeForFactor f).squareFreeCore →
        ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision : 2 * B' < d.p ^ d.k)
    (hcore_entry :
      ∃ raw ∈ (Hex.exhaustiveCoreFactorsWithBound
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound
            (Hex.normalizeForFactor f).squareFreeCore)
          primeData).toList,
        entry.1 = Hex.normalizeFactorSign raw) :
    Hex.ZPoly.Irreducible entry.1 := by
  obtain ⟨raw, hraw_mem, hentry_eq⟩ := hcore_entry
  have hcore_primitive := zpoly_primitive_of_monic hcore_monic
  have hcore_lc_pos := zpoly_lc_pos_of_monic hcore_monic
  have hirr_raw : Hex.ZPoly.Irreducible raw :=
    exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
      h hpartition hcore_ne hcore_primitive hcore_lc_pos hcore_record hB_ne_zero
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hd_liftedFactor_inj B' hcore_lc_le hvalid hprecision raw hraw_mem
  rw [hentry_eq]
  exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible hirr_raw

set_option maxHeartbeats 2000000

/-- **#4006 slow-path lemma (deliverable 2).**

Connects the branch-local irreducibility theorem
`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`
to the slow-path exhaustive-branch shape `factorWithBound_entry_mem_exhaustive_branch_raw`
(#4041), so downstream slow-path callers can move directly from "this
recorded `factorWithBound` entry was emitted by the exhaustive branch and
identifies with a `Hex.normalizeFactorSign`-image of an exhaustive
square-free-core factor" to "the entry is irreducible as a `Hex.ZPoly`".

This lemma specialises the hypothesis set of deliverable 1 to
`primeData = Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore`
(the slow path's actual prime-data source) and the outer coefficient bound
`B = Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore`
(the bound at which deliverable 1's coverage hypothesis is well-formed).
The `hbranch` and `hentry_mem` arguments are not used by the proof, but
they document the caller-side entry point: a typical caller threads them
through `factorWithBound_entry_mem_exhaustive_branch_raw` and
`exhaustiveSlowRawFactorsWithBound_mem_normalization_or_core` to obtain the
`hcore_entry` witness.

Thin wrapper over
`factorWithBound_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound
(Hex.normalizeForFactor f).squareFreeCore` and discharges the abstract bound
hypotheses via `defaultFactorCoeffBound_valid` paired with
`leadingCoeff_eq_coeff_last`. -/
theorem factorWithBound_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence
    {f : Hex.ZPoly} {entry : Hex.ZPoly × Nat}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (primeData : Hex.PrimeChoiceData)
    (_hbranch :
      Hex.factorWithBoundUsesExhaustiveBranch f
        (Hex.ZPoly.defaultFactorCoeffBound
          (Hex.normalizeForFactor f).squareFreeCore))
    (_hentry_mem :
      entry ∈ (Hex.factorWithBound f
        (Hex.ZPoly.defaultFactorCoeffBound
          (Hex.normalizeForFactor f).squareFreeCore)).factors.toList)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (h :
      HenselSubsetCorrespondenceHypotheses
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound
          (Hex.normalizeForFactor f).squareFreeCore)
        primeData
        d admissiblePrime successfulLift)
    (hpartition :
      LiftedFactorSubsetPartition
        (Hex.normalizeForFactor f).squareFreeCore d Finset.univ
        (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hcore_monic :
      Hex.DensePoly.Monic (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_record :
      Hex.shouldRecordPolynomialFactor
        (Hex.normalizeForFactor f).squareFreeCore = true)
    (hB_ne_zero :
      Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore < d.p ^ d.k)
    (hcore_entry :
      ∃ raw ∈ (Hex.exhaustiveCoreFactorsWithBound
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound
            (Hex.normalizeForFactor f).squareFreeCore)
          primeData).toList,
        entry.1 = Hex.normalizeFactorSign raw) :
    Hex.ZPoly.Irreducible entry.1 := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos := zpoly_lc_pos_of_monic hcore_monic
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact factorWithBound_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
    primeData _hbranch _hentry_mem hchoose h hpartition hcore_ne hcore_monic
    hcore_record hB_ne_zero
    hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
    hd_liftedFactor_inj (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le (defaultFactorCoeffBound_valid core hcore_ne) hprecision hcore_entry

set_option maxHeartbeats 2000000
/--
Abstract-bound variant of
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`:
the concrete
`2 * defaultFactorCoeffBound (normalizeForFactor f).squareFreeCore < d.p ^ d.k`
Mignotte precision on the square-free core is replaced by `2 * B' < d.p ^ d.k`
against an abstract bound `B'`, paired with the leading-coefficient bound on
the core and the universal divisor coefficient bound
`∀ g ∣ core, ∀ i, (g.coeff i).natAbs ≤ B'`. The proof body mirrors the
(now-wrapper) original verbatim, except that the forward call to the
slow-path capstone
`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`
becomes its `_of_bound` sibling, threading `B'`, `hcore_lc_le`, `hvalid`,
`hprecision`.
-/
theorem factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
    {f : Hex.ZPoly} {entry : Hex.ZPoly × Nat}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (primeData : Hex.PrimeChoiceData)
    (_hbranch :
      Hex.factorWithBoundUsesExhaustiveBranch f
        (Hex.ZPoly.defaultFactorCoeffBound f))
    (_hentry_mem :
      entry ∈ (Hex.factorWithBound f
        (Hex.ZPoly.defaultFactorCoeffBound f)).factors.toList)
    (_hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (h :
      HenselSubsetCorrespondenceHypotheses
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData
        d admissiblePrime successfulLift)
    (hpartition :
      LiftedFactorSubsetPartition
        (Hex.normalizeForFactor f).squareFreeCore d Finset.univ
        (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hcore_primitive :
      Hex.ZPoly.Primitive (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_record :
      Hex.shouldRecordPolynomialFactor
        (Hex.normalizeForFactor f).squareFreeCore = true)
    (hB_ne_zero : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (B' : Nat)
    (hcore_lc_le :
      (Hex.DensePoly.leadingCoeff
        (Hex.normalizeForFactor f).squareFreeCore).natAbs ≤ B')
    (hvalid :
      ∀ g : Hex.ZPoly, g ∣ (Hex.normalizeForFactor f).squareFreeCore →
        ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision : 2 * B' < d.p ^ d.k)
    (hcore_entry :
      ∃ raw ∈ (Hex.exhaustiveCoreFactorsWithBound
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData).toList,
        entry.1 = Hex.normalizeFactorSign raw) :
    Hex.ZPoly.Irreducible entry.1 := by
  obtain ⟨raw, hraw_mem, hentry_eq⟩ := hcore_entry
  have hirr_raw : Hex.ZPoly.Irreducible raw :=
    exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
      h hpartition hcore_ne hcore_primitive hcore_lc_pos hcore_record hB_ne_zero
      hd_modulus hd_liftedFactor_monic hd_liftedFactor_natDegree_pos
      hd_liftedFactor_inj B' hcore_lc_le hvalid hprecision raw hraw_mem
  rw [hentry_eq]
  exact zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible hirr_raw

set_option maxHeartbeats 2000000

/-- **#4536 outer-bound slow-path lemma.**

The caller-facing variant of
`factorWithBound_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`
at the *outer* coefficient bound `B = Hex.ZPoly.defaultFactorCoeffBound f`
actually used by the public entry point `Hex.factor f`.  Recall that
`Hex.factor f` unfolds to
`Hex.factorWithBound f (Hex.ZPoly.defaultFactorCoeffBound f)`, which in the
slow exhaustive branch invokes
`exhaustiveCoreFactorsWithBound (normalizeForFactor f).squareFreeCore
  (defaultFactorCoeffBound f) primeData` — the same square-free core as the
#4006 sibling, but at a strictly larger outer coefficient bound than that
sibling's `defaultFactorCoeffBound (normalizeForFactor f).squareFreeCore`.

The proof composes the `B`-generalised upstream theorem
`exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_henselSubsetCorrespondence`
at `B := defaultFactorCoeffBound f` with
`zpolyIrreducible_normalizeFactorSign_of_zpolyIrreducible` to recover entry
irreducibility through the `Hex.normalizeFactorSign` post-processing applied
by `collectFactorMultiplicities`.

The Mignotte invariant `hprecision : 2 * defaultFactorCoeffBound core <
d.p^d.k` operates on `core = (normalizeForFactor f).squareFreeCore` (the
square-free core, not the public input `f`) and is supplied externally;
this matches the #4006 sibling's invariant shape exactly.

For HO-1 callers wiring `B' := Hex.ZPoly.defaultFactorCoeffBound f`, the
canonical surface is the abstract-bound sibling
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound`
above: it accepts the universal divisor-coefficient bound
`hvalid : ∀ g ∣ core, ∀ i, (g.coeff i).natAbs ≤ B'` plus the outer-shape
Mignotte precision `2 * B' < d.p ^ d.k` directly, with no monotonicity
step required.  (The `squareFreeCore`-bound monotonicity question was
tracked as #4539 and closed without resolution; the `_of_bound` cascade
superseded it.)

Thin wrapper over
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound`
that instantiates `B' := Hex.ZPoly.defaultFactorCoeffBound core` and
discharges the abstract bound hypotheses via `defaultFactorCoeffBound_valid`
paired with `leadingCoeff_eq_coeff_last`.

The `hbranch` and `hentry_mem` arguments are not used by the proof, but
they document the caller-side entry point: a typical caller threads them
through `factorWithBound_entry_mem_exhaustive_branch_raw` and
`exhaustiveSlowRawFactorsWithBound_mem_normalization_or_core` to obtain the
`hcore_entry` witness. -/
theorem factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence
    {f : Hex.ZPoly} {entry : Hex.ZPoly × Nat}
    {d : Hex.LiftData} {admissiblePrime successfulLift : Prop}
    (primeData : Hex.PrimeChoiceData)
    (_hbranch :
      Hex.factorWithBoundUsesExhaustiveBranch f
        (Hex.ZPoly.defaultFactorCoeffBound f))
    (_hentry_mem :
      entry ∈ (Hex.factorWithBound f
        (Hex.ZPoly.defaultFactorCoeffBound f)).factors.toList)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (h :
      HenselSubsetCorrespondenceHypotheses
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)
        primeData
        d admissiblePrime successfulLift)
    (hpartition :
      LiftedFactorSubsetPartition
        (Hex.normalizeForFactor f).squareFreeCore d Finset.univ
        (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hcore_primitive :
      Hex.ZPoly.Primitive (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_lc_pos :
      0 < Hex.DensePoly.leadingCoeff (Hex.normalizeForFactor f).squareFreeCore)
    (hcore_record :
      Hex.shouldRecordPolynomialFactor
        (Hex.normalizeForFactor f).squareFreeCore = true)
    (hB_ne_zero : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0)
    (hd_modulus : 2 ≤ d.p ^ d.k)
    (hd_liftedFactor_monic :
      ∀ i, Hex.DensePoly.Monic (liftedFactor d i))
    (hd_liftedFactor_natDegree_pos :
      ∀ i, 0 < (HexPolyZMathlib.toPolynomial (liftedFactor d i)).natDegree)
    (hd_liftedFactor_inj : Function.Injective (liftedFactor d))
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound
        (Hex.normalizeForFactor f).squareFreeCore < d.p ^ d.k)
    (hcore_entry :
      ∃ raw ∈ (Hex.exhaustiveCoreFactorsWithBound
          (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.defaultFactorCoeffBound f)
          primeData).toList,
        entry.1 = Hex.normalizeFactorSign raw) :
    Hex.ZPoly.Irreducible entry.1 := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_le := defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne
  exact factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence_of_bound
    primeData _hbranch _hentry_mem hchoose h hpartition hcore_ne hcore_primitive
    hcore_lc_pos hcore_record hB_ne_zero hd_modulus hd_liftedFactor_monic
    hd_liftedFactor_natDegree_pos hd_liftedFactor_inj
    (Hex.ZPoly.defaultFactorCoeffBound core)
    hcore_lc_le (defaultFactorCoeffBound_valid core hcore_ne) hprecision
    hcore_entry

/-- **#4543 supporting lemma (HO-1).**

Generic constructor for `HenselSubsetCorrespondenceHypotheses` over the
executable `Hex.choosePrimeData`/`Hex.henselLiftData` surface, parametric
in the core and the precision count `B` passed to `Hex.henselLiftData`.

The slow exhaustive branch of `Hex.factorWithBound f B₀` (in particular the
public entry point `Hex.factor f`, where `B₀ = Hex.ZPoly.defaultFactorCoeffBound f`)
calls
`Hex.henselLiftData core (Hex.precisionForCoeffBound B₀ primeData.p) primeData`
on `core = (Hex.normalizeForFactor f).squareFreeCore` and
`primeData = Hex.choosePrimeData core`.  Specialising this constructor at
that `B := Hex.precisionForCoeffBound (Hex.ZPoly.defaultFactorCoeffBound f)
primeData.p` therefore produces a value with the exact shape consumed by
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`
(the outer-bound slow-path wrapper landed in PR #4537), unblocking the
slow-path arm of the HO-1 capstone `factor_irreducible_of_nonUnit` (#4170).
See `henselSubsetCorrespondenceHypotheses_outerBound_of_choosePrimeData`
below for the specialisation.

The `admissiblePrime` and `successfulLift` proposition hooks are
instantiated with `True`; the downstream callers depend on the
`exists_subset`/`unique_subset` projections rather than on the hook
propositions themselves (the hooks are markers reserved for a future
analytic Hensel proof that needs to surface those predicates).

The `exists_subset` and `unique_subset` fields encode the analytic
square-free Hensel subset correspondence: every irreducible integer
factor of `core` admits a unique subset of the executable lifted local
factors whose `Hex.DensePoly.scale (leadingCoeff core)`-scaled product
agrees with the factor modulo the Hensel modulus `d.p ^ d.k`.  A
Mathlib-free proof would require either BHKS Theorem 5.2 machinery
(tracked by #2567) or the classical square-free Hensel lemma transported
to the executable `Hex.ZPoly` surface (not yet ported into
`HexBerlekampZassenhausMathlib`).  Per #4543's explicit fallback
allowance, the analytic obligation is left as a single localised `sorry`
inside the `henselSubsetCorrespondence_analytic_obligation` helper;
the constructor itself is `sorry`-free.  This is sorry-equivalent to the
current slow-path arm of #4170 (which sits behind a single opaque
`sorry` of the same analytic content), while exposing a strictly more
useful API for the HO-1 assembly. -/
private theorem henselSubsetCorrespondence_analytic_obligation
    (core : Hex.ZPoly) (B : Nat) :
    let primeData := Hex.choosePrimeData core
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    ∀ {factor : Hex.ZPoly},
      Irreducible (HexPolyZMathlib.toPolynomial factor) →
      factor ∣ core →
      ∃! S : LiftedFactorSubset d, RepresentsIntegerFactorAtLift core d factor S := by
  intro primeData d factor _ _
  sorry

/-- **#4543 supporting lemma (HO-1).**

`HenselSubsetCorrespondenceHypotheses` value in the successful
`Hex.choosePrimeData? core = some primeData` branch, parametric in the
precision count `B`.  The proof transports through
`Hex.choosePrimeData_eq_of_choosePrimeData?_some` to reuse
`henselSubsetCorrespondence_analytic_obligation`; see that helper for the
single localised analytic `sorry`. -/
theorem henselSubsetCorrespondenceHypotheses_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetCorrespondenceHypotheses core B primeData d True True := by
  have hprimeData : Hex.choosePrimeData core = primeData :=
    Hex.choosePrimeData_eq_of_choosePrimeData?_some hchoose
  subst primeData
  intro d
  refine
    { lift_eq := rfl
      admissible_prime := trivial
      successful_lift := trivial
      exists_subset := ?_
      unique_subset := ?_ }
  · intro factor hirr hdvd
    exact (henselSubsetCorrespondence_analytic_obligation core B hirr hdvd).exists
  · intro factor S T hirr hdvd hS hT
    rcases henselSubsetCorrespondence_analytic_obligation core B hirr hdvd with
      ⟨_, _, huniq⟩
    exact (huniq S hS).trans (huniq T hT).symm

/-- **#4543 supporting lemma (HO-1), outer-bound specialisation.**

Specialisation of `henselSubsetCorrespondenceHypotheses_of_choosePrimeData`
at the precision count actually consumed by the slow exhaustive branch
of `Hex.factor f` (i.e. `Hex.factorWithBound f
(Hex.ZPoly.defaultFactorCoeffBound f)`).  The resulting structure value
has the exact `core`/`B`/`primeData`/`d` shape expected by
`factor_exhaustive_branch_entry_core_zpolyIrreducible_of_henselSubsetCorrespondence`
(PR #4537), so the HO-1 slow-path assembly can apply that wrapper
directly. -/
theorem henselSubsetCorrespondenceHypotheses_outerBound_of_choosePrimeData
    (f : Hex.ZPoly)
    (primeData : Hex.PrimeChoiceData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore = some primeData) :
    let core := (Hex.normalizeForFactor f).squareFreeCore
    let B := Hex.ZPoly.defaultFactorCoeffBound f
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetCorrespondenceHypotheses core B primeData d True True :=
  henselSubsetCorrespondenceHypotheses_of_choosePrimeData _ _ primeData hchoose

/-- **#4549 supporting lemma (HO-1), analytic obligation.**

The genuinely analytic content of the
`LiftedFactorSubsetPartition core d Finset.univ core` constructor over
the executable `Hex.choosePrimeData`/`Hex.henselLiftData` surface.
Packages the four fields that cannot be derived purely from the
`HenselSubsetCorrespondenceHypotheses`/`unique_subset` infrastructure
of #4543 alone:

* `cover` — every lifted-factor index is contained in some representing
  subset of an irreducible integer divisor of `core`;
* `pairwise_disjoint` — non-associated irreducible divisors of `core`
  have disjoint representing subsets;
* `unique_up_to_associated` — associated irreducible divisors of `core`
  share their representing subset;
* `support_subset_of_dvd_recombinationCandidate` — if an irreducible
  divisor of `core` divides a recombination candidate, its representing
  subset is contained in the candidate's selection set.
* `support_subset_of_dvd_scaledRecombinationCandidate` — the analogous
  support containment for scaled recombination candidates.

A Mathlib-free proof of this obligation would require either BHKS
Theorem 5.2 machinery (tracked by #2567) or the classical square-free
Hensel correspondence + partition completeness lemma transported to the
executable `Hex.ZPoly` surface (not yet ported into
`HexBerlekampZassenhausMathlib`).  Per #4549's explicit fallback
allowance (mirroring the #4543 pattern), the four-field package is left
as a single localised `sorry` here; the parametric constructor that
routes through this helper is `sorry`-free.  This is sorry-equivalent
to the current slow-path arm of #4170, while exposing a strictly more
useful API for the HO-1 assembly.

Note: the issue text suggested deriving `pairwise_disjoint` /
`unique_up_to_associated` from `unique_subset` alone, but
`RepresentsIntegerFactorAtLift` is not invariant under unit factors
in `Polynomial ℤ` (the predicate uses signed `reduceModPow` equality
of the scaled lifted product against the factor), so both fields are
genuinely analytic in the same sense as `cover` and bundled here. -/
private theorem liftedFactorSubsetPartition_analytic_obligation
    (core : Hex.ZPoly) (B : Nat) :
    let primeData := Hex.choosePrimeData core
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    (∀ {i : LiftedFactorIndex d},
        i ∈ (Finset.univ : LiftedFactorSubset d) →
          ∃ (f : Hex.ZPoly) (S : LiftedFactorSubset d),
            Irreducible (HexPolyZMathlib.toPolynomial f) ∧
              f ∣ core ∧
                S ⊆ (Finset.univ : LiftedFactorSubset d) ∧
                  i ∈ S ∧ RepresentsIntegerFactorAtLift core d f S) ∧
      (∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
          Irreducible (HexPolyZMathlib.toPolynomial f) →
            f ∣ core →
              RepresentsIntegerFactorAtLift core d f S →
                Irreducible (HexPolyZMathlib.toPolynomial g) →
                  g ∣ core →
                    RepresentsIntegerFactorAtLift core d g T →
                      ¬ Associated (HexPolyZMathlib.toPolynomial f)
                          (HexPolyZMathlib.toPolynomial g) →
                        Disjoint S T) ∧
        (∀ {f g : Hex.ZPoly} {S T : LiftedFactorSubset d},
            Irreducible (HexPolyZMathlib.toPolynomial f) →
              f ∣ core →
                RepresentsIntegerFactorAtLift core d f S →
                  Irreducible (HexPolyZMathlib.toPolynomial g) →
                    g ∣ core →
                      RepresentsIntegerFactorAtLift core d g T →
                        Associated (HexPolyZMathlib.toPolynomial f)
                            (HexPolyZMathlib.toPolynomial g) →
                          S = T) ∧
          (∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
              Irreducible (HexPolyZMathlib.toPolynomial f) →
                f ∣ core →
                  f ∣ liftedFactorProductCandidate d T →
                    RepresentsIntegerFactorAtLift core d f S →
                      S ⊆ T) ∧
            (∀ {f : Hex.ZPoly} {S T : LiftedFactorSubset d},
                Irreducible (HexPolyZMathlib.toPolynomial f) →
                  f ∣ core →
                    f ∣ scaledRecombinationCandidate core d T →
                      RepresentsIntegerFactorAtLift core d f S →
                        S ⊆ T) := by
  intro primeData d
  sorry

/-- **#4549 supporting lemma (HO-1).**

Parametric constructor for `LiftedFactorSubsetPartition core d
Finset.univ core` over the successful
`Hex.choosePrimeData? core = some primeData` surface, parametric in the core
and the precision count `B` passed to `Hex.ZPoly.toMonicLiftData`.

Square-freeness of `HexPolyZMathlib.toPolynomial core` is taken as an
explicit hypothesis `hcore_sqfree`: the outer-bound specialisation
below threads it in at
`core = (Hex.normalizeForFactor f).squareFreeCore` (where it is
expected to hold by construction), and downstream HO-1 assemblies
supply it from the caller's own square-free-core invariants.  This
matches the issue's option (a) for handling
`target_squarefree`.

Composes:

* `henselSubsetCorrespondenceRest_initial` applied to the witness-form
  `henselSubsetCorrespondenceHypotheses_of_choosePrimeData` for
  `toHenselSubsetCorrespondenceRest`;
* `hcore_sqfree` for `target_squarefree`;
* the analytic obligation helper above for the five genuinely analytic
  fields (`cover`, `pairwise_disjoint`, `unique_up_to_associated`,
  `support_subset_of_dvd_recombinationCandidate`,
  `support_subset_of_dvd_scaledRecombinationCandidate`).

The constructor body is `sorry`-free; the only analytic `sorry`
introduced by #4549 is inside
`liftedFactorSubsetPartition_analytic_obligation` above. -/
theorem liftedFactorSubsetPartition_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    LiftedFactorSubsetPartition core d Finset.univ core := by
  have hprimeData : Hex.choosePrimeData core = primeData :=
    Hex.choosePrimeData_eq_of_choosePrimeData?_some hchoose
  subst primeData
  intro d
  obtain ⟨hcover, hdisj, huniq, hsup, hscaled_sup⟩ :=
    liftedFactorSubsetPartition_analytic_obligation core B
  refine
    { toHenselSubsetCorrespondenceRest :=
        henselSubsetCorrespondenceRest_initial
          (henselSubsetCorrespondenceHypotheses_of_choosePrimeData core B
            (Hex.choosePrimeData core) hchoose)
      target_squarefree := hcore_sqfree
      cover := ?_
      pairwise_disjoint := ?_
      unique_up_to_associated := ?_
      support_subset_of_dvd_recombinationCandidate := ?_
      support_subset_of_dvd_scaledRecombinationCandidate := ?_ }
  · intro i hi
    exact hcover hi
  · intro f g S T hirr_f hdvd_f _ hSrep hirr_g hdvd_g _ hTrep hnoassoc
    exact hdisj hirr_f hdvd_f hSrep hirr_g hdvd_g hTrep hnoassoc
  · intro f g S T hirr_f hdvd_f _ hSrep hirr_g hdvd_g _ hTrep hassoc
    exact huniq hirr_f hdvd_f hSrep hirr_g hdvd_g hTrep hassoc
  · intro f S T hirr hdvd_target _ hdvd_cand _ hSrep
    exact hsup hirr hdvd_target hdvd_cand hSrep
  · intro f S T hirr hdvd_target _ hdvd_cand _ hSrep
    exact hscaled_sup hirr hdvd_target hdvd_cand hSrep

/-! ### `ModPSubsetPartitionHypotheses` existence/uniqueness assembly

These theorems compose the `monicModPImage` divisibility lemma,
`factors_irreducible_of_choosePrimeData_of_some`, and the UFD subset
existence/uniqueness lemma from `UFDPartition.lean` to discharge the
`exists_subset` / `unique_subset` fields of `ModPSubsetPartitionHypotheses`
in the `choosePrimeData? core = some primeData` branch. The wrapper
exposes the caller-facing shape under the same `hsome` hypothesis. -/

/-- `factorsModP.toList` mapped to Mathlib polynomials has product equal to the
Mathlib transport of `monicModularImage (modP p core)`. -/
private lemma toMathlibPolynomial_factorsModP_product_eq_monicModularImage
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    (hsome : Hex.choosePrimeData? core = some primeData) :
    letI := primeData.bounds
    ((primeData.factorsModP.toList : Multiset _).map
        HexBerlekampMathlib.toMathlibPolynomial).prod =
      HexBerlekampMathlib.toMathlibPolynomial
        (Hex.monicModularImage
          (@Hex.ZPoly.modP primeData.p primeData.bounds core)) := by
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hsome
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  obtain ⟨hzero, hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hsome
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI := hfield
  set raw :=
      (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
        (Hex.monicModularImage_monic hprime _ hzero)
        hfield).factors with hraw_def
  have hraw_ne : ∀ g ∈ raw, g ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      (Hex.monicModularImage_monic hprime _ hzero)
  have hmonic_image_monic :
      Hex.DensePoly.Monic
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime _ hzero
  have hprod_raw :
      Hex.Berlekamp.factorProduct raw =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) :=
    Hex.Berlekamp.factorProduct_berlekampFactor _ _
  have hprod_mapped :
      Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    rw [Hex.factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct
        hprime raw hraw_ne, hprod_raw]
    exact Hex.monicModularImage_eq_self_of_monic hprime _ hmonic_image_monic
  have hlist : primeData.factorsModP.toList = raw.map Hex.monicModularImage := by
    rw [hfactors_eq]
  have hbridge :
      (primeData.factorsModP.toList.map HexBerlekampMathlib.toMathlibPolynomial).prod =
        HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) := by
    rw [hlist]
    rw [← toMathlibPolynomial_listFoldlMul_one (raw.map Hex.monicModularImage)]
    show HexBerlekampMathlib.toMathlibPolynomial
        (Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage)) = _
    rw [hprod_mapped]
  rw [← hbridge]
  exact Multiset.prod_coe _

/-- `Finset.univ.val.map` of the indexed Mathlib factor function recovers the
mapped-to-Mathlib multiset of `factorsModP.toList`. -/
private lemma univ_val_map_modPFactor_eq_factorsModP_map
    (primeData : Hex.PrimeChoiceData) :
    letI := primeData.bounds
    ((Finset.univ : Finset (ModPFactorIndex primeData)).val.map fun i =>
        HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)) =
      ((primeData.factorsModP.toList : Multiset _).map
        HexBerlekampMathlib.toMathlibPolynomial) := by
  letI := primeData.bounds
  unfold modPFactor
  rw [Finset.val_univ_fin]
  rw [show (primeData.factorsModP.toList : List _) =
        List.ofFn (fun i : Fin primeData.factorsModP.size => primeData.factorsModP[i]) from
        List.ofFn_getElem.symm]
  rw [Multiset.map_coe, Multiset.map_coe]
  congr 1
  rw [List.ofFn_eq_map, List.map_map]
  rfl

/-- A submultiset of an injective Finset image can be recovered by filtering. -/
private lemma map_filter_eq_of_le_map_val
    {α β : Type*} [DecidableEq β]
    {f : α → β} (hf_inj : Function.Injective f)
    (S : Finset α)
    {t : Multiset β}
    (h : t ≤ S.val.map f) :
    (S.filter (fun a => f a ∈ t)).val.map f = t := by
  classical
  have hSnodup : S.val.Nodup := S.nodup
  have hmap_nodup : (S.val.map f).Nodup := hSnodup.map hf_inj
  have ht_nodup : t.Nodup := Multiset.nodup_of_le h hmap_nodup
  have hSfilter_nodup : (S.filter (fun a => f a ∈ t)).val.Nodup :=
    (S.filter _).nodup
  have hLHS_nodup :
      ((S.filter (fun a => f a ∈ t)).val.map f).Nodup :=
    hSfilter_nodup.map hf_inj
  refine Multiset.Nodup.ext hLHS_nodup ht_nodup |>.mpr ?_
  intro x
  constructor
  · intro hx
    rw [Multiset.mem_map] at hx
    obtain ⟨a, ha_mem, ha_eq⟩ := hx
    rw [Finset.mem_val, Finset.mem_filter] at ha_mem
    rw [← ha_eq]; exact ha_mem.2
  · intro hxt
    have hxmap : x ∈ S.val.map f := Multiset.mem_of_le h hxt
    rw [Multiset.mem_map] at hxmap
    obtain ⟨a, ha_mem, ha_eq⟩ := hxmap
    rw [Multiset.mem_map]
    refine ⟨a, ?_, ha_eq⟩
    rw [Finset.mem_val, Finset.mem_filter]
    refine ⟨ha_mem, ?_⟩
    rw [ha_eq]; exact hxt

/-- Final assembly: the analyzable `choosePrimeData? core = some primeData`
branch of the integer-irreducible → mod-`p` representing-subset existence
and uniqueness statement. -/
theorem existsUnique_modPFactorSubset_of_choosePrimeData_of_some
    (core : Hex.ZPoly) {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hcore_ne : core ≠ 0)
    (primeData : Hex.PrimeChoiceData)
    (hsome : Hex.choosePrimeData? core = some primeData) :
    ∃! S : ModPFactorSubset primeData,
      RepresentsIntegerFactorModP primeData factor S := by
  classical
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hsome
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hprime_root : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime_root⟩
  obtain ⟨hzero, hfactors_eq⟩ :=
    Hex.choosePrimeData?_factorsModP_berlekamp_form core primeData hsome
  have hform : Hex.factorsModPBerlekampForm core primeData :=
    ⟨hprime, hzero, hfactors_eq⟩
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    Hex.choosePrimeData?_isGoodPrime core primeData hsome
  have hnodup : primeData.factorsModP.toList.Nodup :=
    factorsModP_nodup_of_factorsModPBerlekampForm core primeData hform hgood
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI := hfield
  -- Set up abbreviations.
  set f : ModPFactorIndex primeData → Polynomial (ZMod primeData.p) :=
      fun i => HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)
      with hf_def
  set factorsM : Multiset (Polynomial (ZMod primeData.p)) :=
      ((primeData.factorsModP.toList : Multiset _).map
        HexBerlekampMathlib.toMathlibPolynomial) with hfactorsM_def
  set mathD : Polynomial (ZMod primeData.p) :=
      HexBerlekampMathlib.toMathlibPolynomial
        (@monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor))
      with hmathD_def
  -- `factorsM` equals the univ-image of `f`.
  have hfactorsM_univ : factorsM = Finset.univ.val.map f :=
    (univ_val_map_modPFactor_eq_factorsModP_map primeData).symm
  -- `toMathlibPolynomial` is injective via `fpPolyEquiv`.
  have hinjPoly :
      Function.Injective
        (HexBerlekampMathlib.toMathlibPolynomial : Hex.FpPoly primeData.p → _) :=
    HexBerlekampMathlib.fpPolyEquiv.injective
  -- `modPFactor` is injective on `Fin n` (via factorsModP.toList.Nodup).
  have hmodPFactor_inj :
      Function.Injective (modPFactor primeData) := by
    intro i j hij
    have h_get_i :
        primeData.factorsModP.toList[i.val]'(by
          rw [Array.length_toList]; exact i.isLt) = primeData.factorsModP[i] := by
      simp
    have h_get_j :
        primeData.factorsModP.toList[j.val]'(by
          rw [Array.length_toList]; exact j.isLt) = primeData.factorsModP[j] := by
      simp
    have h_eq :
        primeData.factorsModP.toList[i.val]'(by
            rw [Array.length_toList]; exact i.isLt) =
          primeData.factorsModP.toList[j.val]'(by
            rw [Array.length_toList]; exact j.isLt) := by
      rw [h_get_i, h_get_j]; exact hij
    exact Fin.ext (List.Nodup.getElem_inj_iff hnodup |>.mp h_eq)
  -- `f` is injective.
  have hf_inj : Function.Injective f := fun i j hij =>
    hmodPFactor_inj (hinjPoly hij)
  -- factorsM is nodup.
  have hfactorsM_nodup : factorsM.Nodup := by
    rw [hfactorsM_def]
    exact (Multiset.coe_nodup.mpr hnodup).map hinjPoly
  -- Each q in factorsM is irreducible.
  have hirr_each : ∀ q ∈ factorsM, Irreducible q := by
    intro q hq
    rw [hfactorsM_def, Multiset.mem_map] at hq
    obtain ⟨g, hg_mem, hg_eq⟩ := hq
    rw [Multiset.mem_coe] at hg_mem
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hg_mem
    have hi_eq : modPFactor primeData ⟨i.val, by
        rw [← Array.length_toList]; exact i.isLt⟩ = g := by
      unfold modPFactor
      have hget : primeData.factorsModP.toList.get i = g := hi
      simpa [List.get_eq_getElem] using hget
    rw [← hg_eq, ← hi_eq]
    exact factors_irreducible_of_choosePrimeData_of_some core primeData hsome _
  -- Each q in factorsM is monic, hence normalize-fixed.
  have hmonic_each : ∀ q ∈ factorsM, q.Monic := by
    intro q hq
    rw [hfactorsM_def, Multiset.mem_map] at hq
    obtain ⟨g, hg_mem, hg_eq⟩ := hq
    rw [Multiset.mem_coe] at hg_mem
    have hg_monic : Hex.DensePoly.Monic g :=
      factorsModP_monic_of_factorsModPBerlekampForm core primeData hform g
        (Array.mem_toList_iff.mp hg_mem)
    rw [← hg_eq]
    exact HexBerlekampMathlib.toMathlibPolynomial_monic g hg_monic
  have hnorm_each : ∀ q ∈ factorsM, normalize q = q := fun q hq =>
    (hmonic_each q hq).normalize_eq_self
  -- mathD is monic, hence normalize-fixed.
  have hmonicModPImage_monic :
      Hex.DensePoly.Monic
        (@monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor)) := by
    apply monicModPImage_monic_of_ne_zero hprime
    -- factor must not vanish mod p; derived from the divisibility facts.
    have hfactor_dvd_core_modP :
        @Hex.ZPoly.modP primeData.p primeData.bounds factor ∣
          @Hex.ZPoly.modP primeData.p primeData.bounds core :=
      modP_dvd_modP_of_dvd primeData.p hdvd
    have hcore_modP_iszero :
        (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
      Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
    exact fpPoly_isZero_false_of_dvd_of_isZero_false
      hfactor_dvd_core_modP hcore_modP_iszero
  have hmathD_monic : mathD.Monic := by
    rw [hmathD_def]
    exact HexBerlekampMathlib.toMathlibPolynomial_monic _ hmonicModPImage_monic
  have hmathD_norm : normalize mathD = mathD := hmathD_monic.normalize_eq_self
  -- mathD ∣ factorsM.prod.
  have hbridge_dvd :
      @monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor) ∣
        Hex.monicModularImage
          (@Hex.ZPoly.modP primeData.p primeData.bounds core) :=
    monicModPImage_dvd_monicModularImage_of_dvd_of_choosePrimeData?_some
      hdvd hcore_ne hsome
  have hmathD_dvd : mathD ∣ factorsM.prod := by
    rw [hfactorsM_def]
    rw [toMathlibPolynomial_factorsModP_product_eq_monicModularImage hsome]
    rw [hmathD_def]
    rcases hbridge_dvd with ⟨c, hc⟩
    refine ⟨HexBerlekampMathlib.toMathlibPolynomial c, ?_⟩
    rw [hc, toMathlibPolynomial_mul]
  -- Apply the UFD lemma.
  obtain ⟨T, ⟨hT_le, hT_prod⟩, hT_uniq⟩ :=
    HexBerlekampZassenhausMathlib.UFDPartition.existsUnique_subset_product_eq_of_dvd_of_squarefree_prod
      hirr_each hnorm_each hfactorsM_nodup hmathD_norm hmathD_dvd
  -- Construct S from T.
  set Stwit : ModPFactorSubset primeData :=
      Finset.univ.filter (fun i : ModPFactorIndex primeData => f i ∈ T) with hStwit_def
  have hStwit_map : Stwit.val.map f = T := by
    rw [hStwit_def]
    have hle : T ≤ Finset.univ.val.map f := by
      rw [← hfactorsM_univ]; exact hT_le
    exact map_filter_eq_of_le_map_val hf_inj Finset.univ hle
  refine ⟨Stwit, ?_, ?_⟩
  · -- Existence.
    show modPFactorProduct primeData Stwit =
        @monicModPImage primeData.p primeData.bounds
          (@Hex.ZPoly.modP primeData.p primeData.bounds factor)
    apply hinjPoly
    rw [toMathlibPolynomial_modPFactorProduct]
    show (∏ i ∈ Stwit, f i) = mathD
    rw [Finset.prod_eq_multiset_prod, hStwit_map]; exact hT_prod
  · -- Uniqueness.
    intro S' hS'
    have hS'_prod :
        modPFactorProduct primeData S' =
          @monicModPImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds factor) := hS'
    apply Finset.val_inj.mp
    apply Multiset.map_injective hf_inj
    have hS'_map_le : S'.val.map f ≤ factorsM := by
      rw [hfactorsM_univ]
      apply Multiset.map_le_map
      exact Finset.val_le_iff.mpr (Finset.subset_univ _)
    have hS'_map_prod : (S'.val.map f).prod = mathD := by
      rw [← Finset.prod_eq_multiset_prod, ← toMathlibPolynomial_modPFactorProduct,
        hS'_prod]
    have hS'_T : S'.val.map f = T :=
      hT_uniq _ ⟨hS'_map_le, hS'_map_prod⟩
    rw [hS'_T, ← hStwit_map]

/-- Caller-facing wrapper for the witness-form
`Hex.choosePrimeData? core = some primeData` branch required by the
`ModPSubsetPartitionHypotheses` constructor. The explicit `hchoose` witness
excludes the `none` branch where the mod-`p` factorisation invariant is
unavailable. -/
theorem existsUnique_modPFactorSubset_of_choosePrimeData
    (core : Hex.ZPoly) {factor : Hex.ZPoly}
    (primeData : Hex.PrimeChoiceData)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hchoose : Hex.choosePrimeData? core = some primeData) :
    ∃! S : ModPFactorSubset primeData,
      RepresentsIntegerFactorModP primeData factor S := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  -- `core ≠ 0` from `isGoodPrime` (which forces `(modP p core).isZero = false`).
  have hcore_ne : core ≠ 0 := by
    intro hcore_zero
    have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
      Hex.choosePrimeData?_isGoodPrime core primeData hchoose
    have hcore_modP_iszero :
        (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
      Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
    have hzero_modP : @Hex.ZPoly.modP primeData.p primeData.bounds 0 = 0 := by
      apply Hex.DensePoly.ext_coeff
      intro k
      rw [Hex.ZPoly.coeff_modP, Hex.DensePoly.coeff_zero]
      rfl
    rw [hcore_zero, hzero_modP] at hcore_modP_iszero
    exact Bool.noConfusion hcore_modP_iszero
  exact existsUnique_modPFactorSubset_of_choosePrimeData_of_some core
    hirr hdvd hcore_ne primeData hchoose

/-- **HO-1 supporting lemma (#4688).**

`ModPSubsetPartitionHypotheses` constructor at the executable
`Hex.choosePrimeData` boundary.

Composes:

* `Hex.choosePrimeData?_fModP_eq` for `fModP_eq`;
* `trivial` for the `True` `admissible_prime` / `square_free_reduction` hooks;
* `factors_irreducible_of_choosePrimeData_of_some` (#4686) for the per-factor
  irreducibility component;
* `existsUnique_modPFactorSubset_of_choosePrimeData` (#4693) for both the
  existence and uniqueness components.

The `hchoose` hypothesis is an explicit `choosePrimeData? = some` witness,
so the `none` branch (where the mod-`p` factorisation invariant is
unavailable) is excluded; downstream callers discharge it from the same
`choosePrimeData?` chain that supplies the other partition fields. -/
theorem modPSubsetPartitionHypotheses_of_choosePrimeData
    (core : Hex.ZPoly)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData) :
    ModPSubsetPartitionHypotheses core primeData True True := by
  refine
    { fModP_eq := ?_
      admissible_prime := trivial
      square_free_reduction := trivial
      factors_irreducible := ?_
      exists_subset := ?_
      unique_subset := ?_ }
  · exact Hex.choosePrimeData?_fModP_eq core primeData hchoose
  · exact factors_irreducible_of_choosePrimeData_of_some core primeData hchoose
  · intro factor hirr hdvd
    exact (existsUnique_modPFactorSubset_of_choosePrimeData core primeData hirr hdvd hchoose).exists
  · intro factor S T hirr hdvd hS hT
    rcases existsUnique_modPFactorSubset_of_choosePrimeData core primeData hirr hdvd hchoose with
      ⟨_, _, huniq⟩
    exact (huniq S hS).trans (huniq T hT).symm

/--
Non-circular `choosePrimeData`/`Hex.ZPoly.toMonicLiftData` constructor for
`HenselSubsetLiftHypotheses`.

Unlike `henselSubsetLiftHypotheses_of_choosePrimeData_henselLiftData`, this
surface consumes the lifted-side descent package directly instead of
requiring a full `HenselSubsetCorrespondenceHypotheses` value.
-/
theorem henselSubsetLiftHypotheses_of_choosePrimeData_henselLiftData_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hdescent :
      HenselLiftDescentHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core
          (Hex.ZPoly.toMonicLiftData core B primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData core B primeData)
            hdescent.factor_count_eq S)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetLiftHypotheses core B primeData d True True True True := by
  intro d
  have _ := hchoose
  exact
    henselSubsetLiftHypotheses_of_forwardTransport_descent
      (hadmissible := trivial)
      (hsquareFree := trivial)
      hdescent
      hlifted_of_modP

/-- **#4697 supporting lemma (HO-1).**

Assembly constructor for `HenselSubsetLiftHypotheses` at the executable
`Hex.choosePrimeData` / `Hex.henselLiftData` surface.

The constructor composes:

* `henselLiftData_liftedFactors_size_eq` (PR #4698) for `factor_count_eq`;
* the supplied forward transport `hlifted_of_modP` for `represents_lifted_of_modP`
  (sourced in practice from `henselLiftData_represents_lifted_of_modP`, landed
  in #4733, once the caller has discharged its analytic prerequisites);
* the landed descent wrapper `henselLiftData_represents_modP_of_lifted`
  (PR #4739) for `represents_modP_of_lifted`, instantiated with the supplied
  `hmod` / `hcorr` partition-and-correspondence inputs together with
  `hlifted_of_modP`.

The four proposition hooks `admissible_prime`, `square_free_reduction`,
`successful_lift`, `coprime_lift` are instantiated with `True`.

Downstream caller: `henselSubsetCorrespondence_of_modPSubsetPartition`
(line above), which composes this value with `hmod` to recover the
`HenselSubsetCorrespondenceHypotheses` package on the lifted surface. -/
theorem henselSubsetLiftHypotheses_of_choosePrimeData_henselLiftData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hmod :
      ModPSubsetPartitionHypotheses core primeData True True)
    (hcorr :
      HenselSubsetCorrespondenceHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core
          (Hex.ZPoly.toMonicLiftData core B primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData core B primeData)
            (Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData)
            S)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetLiftHypotheses core B primeData d True True True True := by
  intro d
  have _ := hchoose
  refine
    { lift_eq := rfl
      factor_count_eq := Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData
      admissible_prime := trivial
      square_free_reduction := trivial
      successful_lift := trivial
      coprime_lift := trivial
      represents_lifted_of_modP := ?_
      represents_modP_of_lifted := ?_ }
  · intro factor S hirr hdvd hrep
    exact hlifted_of_modP hirr hdvd hrep
  · intro factor T hirr hdvd hT
    exact henselLiftData_represents_modP_of_lifted hmod hcorr
      (Hex.ZPoly.toMonicLiftData_liftedFactors_size_eq core B primeData)
      hlifted_of_modP hirr hdvd hT

/-- **#5689 supporting lemma (HO-1 successful branch).**

Successful-branch constructor for the lifted Hensel subset correspondence at
the witness-form `Hex.choosePrimeData?` boundary.

The explicit `hchoose` hypothesis selects the analyzable
`Hex.choosePrimeData? core = some primeData` branch, supplying the mod-`p`
subset partition.  The Hensel-lift obligations remain packaged as
an explicit `HenselSubsetLiftHypotheses` input, so callers do not have to use
the older analytic fallback constructor. -/
theorem henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hlift :
      HenselSubsetLiftHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData)
        True True True True) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetCorrespondenceHypotheses core B primeData d True True := by
  intro d
  exact
    henselSubsetCorrespondence_of_modPSubsetPartition
      (modPSubsetPartitionHypotheses_of_choosePrimeData core primeData hchoose)
      hlift

/-- **#5689 supporting lemma (HO-1 successful branch).**

Caller-facing wrapper for the common successful-branch shape: compose the
`choosePrimeData? = some ...` mod-`p` partition with a non-circular lifted-side
descent package and explicit forward Hensel transport to obtain the standard
`HenselSubsetCorrespondenceHypotheses` surface. -/
theorem henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hdescent :
      HenselLiftDescentHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ core →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift core
          (Hex.ZPoly.toMonicLiftData core B primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData core B primeData)
            hdescent.factor_count_eq S)) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    HenselSubsetCorrespondenceHypotheses core B primeData d True True := by
  intro d
  exact
    henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success core B primeData hchoose
      (henselSubsetLiftHypotheses_of_choosePrimeData_henselLiftData_descent
        core B primeData hchoose hdescent hlifted_of_modP)

end

end HexBerlekampZassenhausMathlib
