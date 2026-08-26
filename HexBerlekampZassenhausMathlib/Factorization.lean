/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexPolyZMathlib.PolynomialEquivalence
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section
set_option backward.proofsInPublic true

/-!
# Integer polynomial factorizations

Product, irreducibility, normalization, divisibility, root, and uniqueness
facts for executable integer polynomial factorizations.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

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
theorem _root_.Hex.ZPoly.Irreducible_iff_polynomialIrreducible (f : Hex.ZPoly) :
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
theorem _root_.Hex.ZPoly.polynomialIrreducible_iff_irreducible (f : Hex.ZPoly) :
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
nonzero input is primitive. The public factorization verifies its own output,
so primitivity is discharged from `f ≠ 0` alone (the filtered product
reconstructs `f`); no raw-source hypothesis is needed.
-/
theorem factorize_entries_primitive_of_chosen_raw_primitive
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    ∀ entry ∈ (Hex.ZPoly.factorize f).factors, Hex.ZPoly.Primitive entry.1 :=
  Hex.factorize_entries_primitive_of_ne_zero f hf

/-- Conversion to Mathlib polynomials preserves a left-associated product. -/
theorem toPolynomial_foldl_mul (lst : List Hex.ZPoly) (init : Hex.ZPoly) :
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
theorem toPolynomial_one_zpoly :
    HexPolyZMathlib.toPolynomial (1 : Hex.ZPoly) = 1 := by
  show HexPolyZMathlib.toPolynomial (Hex.DensePoly.C (1 : Int)) = 1
  rw [HexPolyZMathlib.toPolynomial_C]
  simp

/-- Converting an executable factor product gives the corresponding Mathlib list product. -/
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

/-- Conversion to Mathlib polynomials preserves the executable factor power. -/
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

/--
Recorded entries of the default executable factorization of a nonzero input are
pairwise non-associated after transport to `Polynomial ℤ`. Primitivity is
discharged from `f ≠ 0` by the self-certifying path.
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

/-- Every recorded factor divides the transported input polynomial. -/
theorem factorize_entry_dvd (f : Hex.ZPoly) {entry : Hex.ZPoly × Nat}
    (hentry : entry ∈ (Hex.ZPoly.factorize f).factors) :
    HexPolyZMathlib.toPolynomial entry.1 ∣
      HexPolyZMathlib.toPolynomial f := by
  let φ := Hex.ZPoly.factorize f
  have hmult : entry.2 ≠ 0 := by
    have hpos := Hex.factorize_entry_multiplicity_pos f entry
      (Array.mem_toList_iff.mpr hentry)
    omega
  have hflat : entry.1 ∈ factorizationFlattenedFactors φ :=
    mem_factorizationFlattenedFactors_iff.mpr
      ⟨entry, Array.mem_toList_iff.mpr hentry, hmult, rfl⟩
  have hmapped : HexPolyZMathlib.toPolynomial entry.1 ∈
      (factorizationFlattenedFactors φ).map
        HexPolyZMathlib.toPolynomial :=
    List.mem_map.mpr ⟨entry.1, hflat, rfl⟩
  obtain ⟨r, hr⟩ := List.dvd_prod hmapped
  have hdvd : HexPolyZMathlib.toPolynomial entry.1 ∣
      Polynomial.C φ.scalar *
        ((factorizationFlattenedFactors φ).map
          HexPolyZMathlib.toPolynomial).prod := by
    refine ⟨Polynomial.C φ.scalar * r, ?_⟩
    rw [hr]
    ring
  have hproduct := congrArg HexPolyZMathlib.toPolynomial
    (factorize_product f)
  rw [factorizationProduct_toPolynomial] at hproduct
  exact hproduct ▸ hdvd

private theorem exists_isRoot_prod {z : ℂ}
    {polys : List (Polynomial ℂ)} (h : polys.prod.IsRoot z) :
    ∃ p ∈ polys, p.IsRoot z := by
  induction polys with
  | nil => simp [Polynomial.IsRoot] at h
  | cons p polys ih =>
      rw [List.prod_cons, Polynomial.IsRoot, Polynomial.eval_mul] at h
      rcases mul_eq_zero.mp h with hp | htail
      · exact ⟨p, List.mem_cons_self, hp⟩
      · obtain ⟨q, hq, hz⟩ := ih htail
        exact ⟨q, List.mem_cons_of_mem p hq, hz⟩

private theorem map_list_prod (polys : List (Polynomial ℤ)) :
    polys.prod.map (Int.castRingHom ℂ) =
      (polys.map fun p => p.map (Int.castRingHom ℂ)).prod := by
  induction polys with
  | nil => simp
  | cons p polys ih => simp [ih]

/-- Every complex root of a nonzero input is a root of one of the recorded
irreducible factors. -/
theorem factorize_exists_root (f : Hex.ZPoly) (hf : f ≠ 0) {z : ℂ}
    (hz : ((HexPolyZMathlib.toPolynomial f).map
      (Int.castRingHom ℂ)).IsRoot z) :
    ∃ entry ∈ (Hex.ZPoly.factorize f).factors,
      ((HexPolyZMathlib.toPolynomial entry.1).map
        (Int.castRingHom ℂ)).IsRoot z := by
  let φ := Hex.ZPoly.factorize f
  have hproduct := congrArg HexPolyZMathlib.toPolynomial
    (factorize_product f)
  rw [factorizationProduct_toPolynomial] at hproduct
  have hscalar : φ.scalar ≠ 0 := by
    intro hs
    have hzero : HexPolyZMathlib.toPolynomial f = 0 := by
      simpa [φ, hs] using hproduct.symm
    apply hf
    apply HexPolyZMathlib.equiv.injective
    simpa [HexPolyZMathlib.equiv_apply] using hzero
  have hproductℂ := congrArg (Polynomial.map (Int.castRingHom ℂ)) hproduct
  have hroot :
      (((factorizationFlattenedFactors φ).map
        ((fun p : Polynomial ℤ => p.map (Int.castRingHom ℂ)) ∘
          HexPolyZMathlib.toPolynomial)).prod).IsRoot z := by
    rw [← hproductℂ] at hz
    have heval :
        (φ.scalar : ℂ) *
        (((factorizationFlattenedFactors φ).map
          ((fun p : Polynomial ℤ => p.map (Int.castRingHom ℂ)) ∘
            HexPolyZMathlib.toPolynomial)).prod).eval z = 0 := by
      simpa [Polynomial.IsRoot, φ, map_list_prod, List.map_map,
        Function.comp_apply] using hz
    exact (mul_eq_zero.mp heval).resolve_left (by exact_mod_cast hscalar)
  obtain ⟨qℂ, hqℂ, hqroot⟩ := exists_isRoot_prod hroot
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hqℂ
  obtain ⟨entry, hentry, _hmult, rfl⟩ :=
    mem_factorizationFlattenedFactors_iff.mp hq
  exact ⟨entry, Array.mem_toList_iff.mp hentry,
    by simpa [Function.comp_apply] using hqroot⟩

/--
The transport coercion of `factorizationFlattenedFactors` to a multiset
equals the multiplicity sum over the original entry list. -/
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

/-- Sign normalization produces a nonnegative leading coefficient. -/
theorem leadingCoeff_normalizeFactorSign_nonneg (f : Hex.ZPoly) :
    0 ≤ Hex.DensePoly.leadingCoeff (Hex.normalizeFactorSign f) := by
  unfold Hex.normalizeFactorSign
  by_cases h : Hex.DensePoly.leadingCoeff f < 0
  · rw [if_pos h]
    rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero (-1 : Int) f (by decide)]
    omega
  · rw [if_neg h]
    omega

end

end HexBerlekampZassenhausMathlib
