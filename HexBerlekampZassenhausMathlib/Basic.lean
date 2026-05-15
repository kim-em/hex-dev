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
