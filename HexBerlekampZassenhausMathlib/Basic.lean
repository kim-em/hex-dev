import HexBerlekampZassenhaus
import HexBerlekampMathlib.Basic
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
A nonzero `Hex.ZPoly` factor with `Hex.normalizeFactorSign` fixed has a
nonnegative leading coefficient, so its Mathlib transport is
`normalize`-fixed in `Polynomial ℤ`.
-/
private theorem normalize_toPolynomial_of_normalizeFactorSign_id
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

/-! ### Mathlib bridge for executable certificate factor-product equalities

These bridges identify the executable `Hex.PrimeFactorData.factorProduct` with
the Mathlib `Polynomial.map (Int.castRingHom (ZMod p))` image of the underlying
integer polynomial and with the explicit product of recorded factor transports.
Both shapes are consumed by the integer irreducibility certificate soundness
composition.
-/

/-- Executable `FpPoly p` multiplication transports to Mathlib multiplication
through the polynomial bridge. -/
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

/-- Coefficientwise scaling on `FpPoly p` transports across the Mathlib bridge
to multiplication by the corresponding `Polynomial.C` of the `ZMod p` cast. -/
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
List `foldl (· * ·)` of executable `FpPoly p` factors transports across the
Mathlib bridge to the explicit Mathlib `List.prod` of the per-factor transports.
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
Mathlib basisSize bridge.
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
      -- Bridge `(Int.castRingHom (ZMod p)) F.leadingCoeff = toZMod (leadingCoeffModP f p)`
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
The monic modular image used for subset partition statements. This mirrors the
executable prime-choice normalization: zero stays zero, and nonzero inputs are
scaled by the inverse of their leading coefficient.
-/
def monicModPImage {p : Nat} [Hex.ZMod64.Bounds p] (f : Hex.FpPoly p) : Hex.FpPoly p :=
  if f.isZero then
    0
  else
    Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff f)⁻¹ f

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
square-free-reduction hypotheses. Downstream consumers should depend on the
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
Consumer-facing mod-`p` subset partition: an irreducible integer factor of the
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
Proof-facing package for the square-free Hensel subset correspondence over the
executable `PrimeChoiceData`/`LiftData` surface.

The two proposition parameters are hooks for the precise admissible-prime and
successful-lift hypotheses supplied by the later analytic Hensel proof.  The
consumer theorems below depend only on the resulting existence and uniqueness
fields, so downstream exhaustive-recombination proofs can be written against a
stable executable API.
-/
structure HenselSubsetCorrespondenceHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData) (admissiblePrime successfulLift : Prop) : Prop where
  lift_eq : d = Hex.henselLiftData core B primeData
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
Consumer-facing square-free Hensel subset correspondence: an irreducible
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
Proof-facing package for transporting the mod-`p` subset partition through a
successful Hensel lift.

The fields isolate the analytic Hensel obligations: the lift preserves the
factor count, every mod-`p` selected subset represents the same integer factor
after lifting, and every lifted representation descends to a mod-`p` selected
subset.  The consumer theorems below combine these fields with
`ModPSubsetPartitionHypotheses` to recover the existing lifted-subset
correspondence API.
-/
structure HenselSubsetLiftHypotheses
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (d : Hex.LiftData)
    (admissiblePrime squareFreeReduction successfulLift coprimeLift : Prop) :
    Prop where
  lift_eq : d = Hex.henselLiftData core B primeData
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
consumer-facing lifted-factor subset correspondence.
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
`HenselSubsetCorrespondenceHypotheses` package, so downstream consumers can
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
Mignotte recoverability for one represented integer factor.

If a subset of the executable lifted factors represents an integer divisor of
`core` modulo the Hensel modulus, and that modulus is beyond twice the default
Mignotte coefficient bound for `core`, then the executable centred-lift
operation recovers the integer factor exactly.
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
      factor := by
  exact
    Hex.centeredLiftPoly_eq_of_reduceModPow_eq
      factor (scaledLiftedFactorProduct core d S) d.p d.k
      (Hex.ZPoly.defaultFactorCoeffBound core)
      (defaultFactorCoeffBound_valid core hcore_ne factor hdvd)
      hprecision hrep

/--
Group A2 packaged for downstream exhaustive-search proofs: under the Hensel
subset-correspondence hypotheses, each irreducible integer factor has a unique
lifted-factor subset whose scaled product both represents it modulo the Hensel
modulus and centred-lifts back to the factor exactly at Mignotte precision.
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
          factor := by
  rcases h.exists_subset hirr hdvd with ⟨S, hS⟩
  refine ⟨S, ⟨hS, ?_⟩, ?_⟩
  · exact
      centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision
        hcore_ne hdvd hS hprecision
  · intro T hT
    exact
      (h.unique_subset (factor := factor) (S := S) (T := T)
        hirr hdvd hS hT.1).symm

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
Initial-state bridge: a Hensel subset correspondence implies the induced
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
Existence-uniqueness consumer view of the induced predicate, mirroring
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

/-! ### LiftedFactorSubset → executable recombination split bridge

The executable recombination search at the lifted-factor surface enumerates
order-preserving partitions of `d.liftedFactors.toList` via
`Hex.subsetSplitsWithFirst`.  These helpers transport a proof-side
`LiftedFactorSubset d` (a `Finset` of indices) into a concrete `(selected,
rest)` partition that lies in the executable enumeration, with the
selected/rejected lists ordered by their original `d.liftedFactors` index.

The bridge product equality matches the executable
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

/-- The A2 recovery equality reformulated against the executable centred-lift
of the **scaled** lifted product, ready to feed downstream packaging that
relates the scaled centered lift to the unscaled `recombinationCandidate`.

This is the cleanest form in which the proof-side recovery is expressed for
later integration with executable-side normalisation reasoning (which removes
the `lc(core)` scale and chooses a sign). -/
theorem centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_ne : core ≠ 0)
    (hdvd : factor ∣ core)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core < d.p ^ d.k) :
    Hex.centeredLiftPoly (scaledLiftedFactorProduct core d S) (d.p ^ d.k) =
      factor := by
  have h := centeredLift_scaledLiftedFactorProduct_eq_of_mignottePrecision
    hcore_ne hdvd hrep hprecision
  rwa [centeredLiftPoly_reduceModPow_eq _ _ _ d.p_pos] at h

private theorem densePoly_scale_one_int (f : Hex.ZPoly) :
    Hex.DensePoly.scale (1 : Int) f = f := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_scale (1 : Int) f n (by simp)]
  simp

/--
Under a monic core hypothesis, the scaled recovery theorem identifies the
unscaled executable recombination candidate with the represented integer
factor.
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
      centeredLiftPoly_scaledLiftedFactorProduct_eq_factor_of_recovery
        hcore_ne hdvd hrep hprecision
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
Hensel-correspondence wrapper for the monic-core recovery theorem.

Once a proof-side subset is known to represent an irreducible integer divisor
at the Hensel lift, the executable recombination candidate is exactly that
factor under the monic/primitive/sign-normalised hypotheses required by the
centered-lift recovery bound.
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
  recombinationCandidate_eq_factor_of_recovery
    hcore_ne hcore_monic hcore_record hdvd hfactor_prim hfactor_norm hirr
    hrep hprecision

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
Membership bridge from a successful fixed-lift recombination search into the
public exhaustive-core wrapper.  The non-empty branch is discharged by the
factor membership witness, so downstream coverage proofs can use an exact
`recombinationSearchMod` success without unfolding `exhaustiveCoreFactorsWithBound`.
-/
theorem exhaustiveCoreFactorsWithBound_mem_of_recombinationSearchMod_some
    {core factor : Hex.ZPoly} {B : Nat} {primeData : Hex.PrimeChoiceData}
    {d : Hex.LiftData} {factors : List Hex.ZPoly}
    (hB : B ≠ 0)
    (hd :
      d =
        Hex.henselLiftData core (Hex.precisionForCoeffBound B primeData.p)
          primeData)
    (hsearch :
      Hex.recombinationSearchMod core (d.p ^ d.k)
        d.liftedFactors.toList = some factors)
    (hmem : factor ∈ factors) :
    factor ∈ (Hex.exhaustiveCoreFactorsWithBound core B primeData).toList := by
  subst d
  have hrecombine :
      Hex.recombineExhaustive core
          (Hex.henselLiftData core (Hex.precisionForCoeffBound B primeData.p)
            primeData) =
        factors.toArray :=
    Hex.recombineExhaustive_eq_of_recombinationSearchMod_some hsearch
  have hnot_empty : factors.toArray.isEmpty = false := by
    cases factors with
    | nil => simp at hmem
    | cons head tail => simp
  simp [Hex.exhaustiveCoreFactorsWithBound, hB, hrecombine, hnot_empty, hmem]

/--
Public-wrapper membership bridge for a first successful fixed-lift split.

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
    (hd :
      d =
        Hex.henselLiftData core (Hex.precisionForCoeffBound B primeData.p)
          primeData)
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
      (d := d) (factors := factors) hB hd hsearch hmem

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
exhaustive branch consumers can ask directly for irreducibility under the
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
    (_hbranch : Hex.factorWithBoundUsesExhaustiveBranch f B)
    (_hentry_mem : entry ∈ (Hex.factorWithBound f B).factors.toList)
    (hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0)
    (hcore_record :
      Hex.shouldRecordPolynomialFactor
        (Hex.normalizeForFactor f).squareFreeCore = true)
    (hcount :
      ((Hex.exhaustiveCoreFactorsWithBound
          (Hex.normalizeForFactor f).squareFreeCore B
          (Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore)).toList.map
          HexPolyZMathlib.toPolynomial).length =
        (UniqueFactorizationMonoid.normalizedFactors
          (HexPolyZMathlib.toPolynomial
            (Hex.normalizeForFactor f).squareFreeCore)).card)
    (hcore_entry :
      ∃ raw ∈
        (Hex.exhaustiveCoreFactorsWithBound
          (Hex.normalizeForFactor f).squareFreeCore B
          (Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore)).toList,
        entry.1 = raw) :
    Hex.ZPoly.Irreducible entry.1 := by
  rcases hcore_entry with ⟨raw, hraw_mem, hentry_eq⟩
  have hirr_raw :
      Hex.ZPoly.Irreducible raw :=
    exhaustiveCoreFactorsWithBound_factor_zpolyIrreducible_of_count
      (core := (Hex.normalizeForFactor f).squareFreeCore)
      (B := B)
      (primeData := Hex.choosePrimeData (Hex.normalizeForFactor f).squareFreeCore)
      hcore_ne hcore_record hcount raw hraw_mem
  rw [hentry_eq]
  exact hirr_raw

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
`Hex.ZPoly.Irreducible_iff_polynomialIrreducible` bridge equivalence.

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

end

end HexBerlekampZassenhausMathlib
