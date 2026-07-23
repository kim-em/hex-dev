/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Basic
public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexHenselMathlib.Correctness
public import HexPolyZMathlib.Basic
public import HexPolyZMathlib.Mignotte
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain


public section
set_option backward.proofsInPublic true

/-!
This module collects the transport bounds, `factorize_product`, `factorize_unique`, and `checkIrreducibleCert_sound`.
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
          (Hex.Nat.binom (HexPolyZMathlib.toPolynomial g).natDegree i : ℝ) := by
      rw [HexPolyZMathlib.binom_eq_choose]
    rw [hbinom] at hstep
    have huniform_nat :=
      Hex.ZPoly.mignotteCoeffBound_le_defaultFactorCoeffBound
        f (k := (HexPolyZMathlib.toPolynomial g).natDegree) (j := i) hdegree hi
    have hmig_eq :
        Hex.ZPoly.mignotteCoeffBound f
            (HexPolyZMathlib.toPolynomial g).natDegree i =
          Hex.Nat.binom (HexPolyZMathlib.toPolynomial g).natDegree i *
            Hex.ZPoly.coeffL2NormBound f :=
      Hex.ZPoly.mignotteCoeffBound_eq f _ _
    have huniform_real :
        (Hex.Nat.binom (HexPolyZMathlib.toPolynomial g).natDegree i : ℝ) *
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
@[expose]
def irreducibleByFactorization (f : Polynomial ℤ) : Bool :=
  Hex.ZPoly.isIrreducible (HexPolyZMathlib.ofPolynomial f)

/-- The default executable factorization multiplies back to the input. -/
@[simp, grind =]
theorem factorize_product (f : Hex.ZPoly) :
    Hex.Factorization.product (Hex.ZPoly.factorize f) = f :=
  Hex.factorize_product f

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

/--
Every polynomial factor emitted by the default executable factorization of a
nonzero input is primitive. The public path is the self-certifying hybrid
(#8383), so primitivity is discharged from `f ≠ 0` alone (the filtered product
reconstructs `f`); no raw-source hypothesis is needed.
-/
theorem factorize_entries_primitive_of_chosen_raw_primitive
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∀ entry ∈ (Hex.ZPoly.factorize f).factors, Hex.ZPoly.Primitive entry.1 :=
  Hex.factorize_entries_primitive_of_ne_zero f hf

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
      rw [List.foldl_cons, ih (init * Hex.Factorization.factorPower entry.1 entry.2),
        HexPolyZMathlib.toPolynomial_mul, factorPower_toPolynomial]
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
  rw [← Array.foldl_toList,
    factorizationProduct_toPolynomial_foldl φ.factors.toList (Hex.DensePoly.C φ.scalar),
    HexPolyZMathlib.toPolynomial_C]
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

set_option maxHeartbeats 3000000 in
/--
Recorded entries of the default executable factorization of a nonzero input are
pairwise non-associated after transport to `Polynomial ℤ`. Primitivity is
discharged from `f ≠ 0` (the self-certifying hybrid, #8383).
-/
theorem factorize_entries_not_associated
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    List.Pairwise
      (fun a b : Hex.ZPoly × Nat =>
        ¬ Associated (HexPolyZMathlib.toPolynomial a.1)
          (HexPolyZMathlib.toPolynomial b.1))
      (Hex.ZPoly.factorize f).factors.toList := by
  exact List.Pairwise.imp_of_mem
    (fun {a b} ha hb hab =>
      zpoly_not_associated_of_ne_of_primitive_pos_leading
        (Hex.factorize_entries_primitive_of_ne_zero f hf a (Array.mem_toList_iff.mp ha))
        (Hex.factorize_entries_primitive_of_ne_zero f hf b (Array.mem_toList_iff.mp hb))
        (Hex.factorize_entry_leadingCoeff_pos f a ha)
        (Hex.factorize_entry_leadingCoeff_pos f b hb)
        hab)
    (Hex.factorize_pairwise_first f)

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
theorem factorize_unique
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
    (primeData : Hex.PrimeFactorData) [Nontrivial (ZMod primeData.p)]
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
          rw [this, Array.getElem_toList]
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

/--
Soundness of the kernel-reducible integer checker: a certificate accepted by
`checkIrreducibleCertLinear` on literal data certifies irreducibility of the
transported polynomial. The primality hypothesis feeds both the
Linear→committed checker implication and the committed checker's own
soundness theorem.
-/
theorem checkIrreducibleCertLinear_sound
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : ∀ primeData ∈ cert.perPrime.toList, Nat.Prime primeData.p)
    (hprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive)
    (hpos : 0 < (HexPolyZMathlib.toPolynomial f).natDegree) :
    Hex.checkIrreducibleCertLinear f cert = true →
      Irreducible (HexPolyZMathlib.toPolynomial f) := by
  intro hcert
  refine checkIrreducibleCert_sound f cert hprime hprim hpos ?_
  refine Hex.checkIrreducibleCert_of_linear f cert ?_ hcert
  intro primeData hmem
  exact ⟨(hprime primeData hmem).two_le,
    fun m hm => (hprime primeData hmem).eq_one_or_self_of_dvd m hm⟩

/--
`checkIrreducibleCertLinear_sound` with every side condition stated as a
kernel-decidable Boolean check: primality of the recorded primes, content one,
and positive executable degree. This is the exact consumption shape of the
multi-prime arm of the `factor_poly`/`irreducibility` provider: it applies
this theorem (through `zpolyIrreducible_of_checkIrreducibleCertLinear` and
`checkMultiPrimeCert`) to a reified literal certificate with an
`Eq.refl true` proof in each hypothesis slot, so the whole obligation is
discharged by kernel reduction on literal data.
-/
theorem irreducible_of_checkIrreducibleCertLinear
    (f : Hex.ZPoly) (cert : Hex.ZPolyIrreducibilityCertificate)
    (hprime : cert.perPrime.all (fun primeData => decide (Nat.Prime primeData.p)) = true)
    (hcontent : decide (Hex.ZPoly.content f = 1) = true)
    (hpos : decide (0 < f.degree?.getD 0) = true)
    (hcert : Hex.checkIrreducibleCertLinear f cert = true) :
    Irreducible (HexPolyZMathlib.toPolynomial f) := by
  have hprime' : ∀ primeData ∈ cert.perPrime.toList, Nat.Prime primeData.p := by
    rw [Array.all_eq_true] at hprime
    intro primeData hmem
    rw [List.mem_iff_getElem] at hmem
    obtain ⟨i, hi, hget⟩ := hmem
    have hiArray : i < cert.perPrime.size := by simpa using hi
    have hdec := hprime i hiArray
    rw [← hget]
    simpa [Array.getElem_toList] using of_decide_eq_true hdec
  have hcontent' : Hex.ZPoly.content f = 1 := of_decide_eq_true hcontent
  have hdeg : (HexPolyZMathlib.toPolynomial f).natDegree = f.degree?.getD 0 :=
    HexPolyMathlib.natDegree_toPolynomial f
  exact checkIrreducibleCertLinear_sound f cert hprime'
    (HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive f hcontent')
    (by rw [hdeg]; exact of_decide_eq_true hpos) hcert

end

end HexBerlekampZassenhausMathlib
