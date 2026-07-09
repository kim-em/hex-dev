/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.ToMonicUniqueness
public import HexBerlekampMathlib.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Content
public import Mathlib.Algebra.Polynomial.Degree.Lemmas
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Eval.Irreducible
public import Mathlib.FieldTheory.Separable
public import Mathlib.FieldTheory.Perfect
public import Mathlib.RingTheory.Polynomial.Radical
public import Mathlib.RingTheory.Polynomial.GaussLemma
public import HexBerlekampZassenhausMathlib.IntReductionMod.Transport
import all HexBerlekampZassenhausMathlib.IntReductionMod.Descent
import all HexBerlekampZassenhausMathlib.IntReductionMod.Transport

public section
set_option backward.proofsInPublic true

/-!
Reduction-mod-`p` irreducibility for primitive integer polynomials. The
descent core and the repeatedPart/reassembly transport live in the
`IntReductionMod.*` submodules; this module exposes the public
factoring-entrypoint soundness theorems (`factorTrialFactorsWithBound_*`,
`factorClassicalFactorsWithBound_*`).
-/
namespace HexBerlekampZassenhausMathlib
/-- **#7584 core-facts producer (lifted-subset partition).**

`LiftedFactorSubsetPartition core (toMonicLiftData core B primeData) Finset.univ
core` from the executable `toMonicPrimeData?` selection witness and the standard
core side conditions alone.  The embedded Hensel correspondence comes from the
carrier-free `henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData` (no
`MonicDescentHypotheses` input), and the recovered-coordinate partition evidence
from
`IntReductionMod.initialLiftedFactorSubsetPartitionEvidence_of_toMonicChoosePrimeData`,
so the caller supplies neither the descent carrier nor a separate
`InitialLiftedFactorSubsetPartitionEvidence`.  The monic-only unscaled support
field stays guarded by `leadingCoeff core = 1`; the non-monic path routes through
the recovered `liftedRecoveryCandidate` coordinate. -/
theorem liftedFactorSubsetPartition_of_toMonicPrimeData_complete
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p) :
    let d := Hex.ZPoly.toMonicLiftData core B primeData
    LiftedFactorSubsetPartition core d Finset.univ core := by
  intro d
  have hp_prime : Hex.Nat.Prime primeData.p :=
    hval.prime
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hprec_spec :
      2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hmodulus :
      2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by omega
  have hprecision : 1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hmodulus
    omega
  exact liftedFactorSubsetPartition_of_toMonicPrimeData core B primeData hval
    (henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData core B primeData
      hval hcore_lc_pos hcore_pos hcore_prim hprecision hbound hB_ne_zero)
    hcore_sqfree
    (IntReductionMod.initialLiftedFactorSubsetPartitionEvidence_of_toMonicChoosePrimeData
      core B primeData hval hcore_lc_pos hcore_pos hcore_prim hB_ne_zero hbound)

/-- **#7584 core-facts producer (slow-path Hensel substrate).**

`SlowPathHenselSubstrate core B primeData` from the `toMonicPrimeData?` selection
witness and standard core side conditions alone -- the slow-modular / fast-BHKS
substrate package with no `MonicDescentHypotheses` carrier and no
`InitialLiftedFactorSubsetPartitionEvidence` input.  The `corr` and `partition`
fields are the carrier-free / complete `toMonicPrimeData?` producers above; the
remaining lifted-factor monic / positive-degree / injectivity and modulus /
precision facts discharge directly from the selection witness. -/
theorem slowPathHenselSubstrate_of_toMonicPrimeData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne_zero : B ≠ 0)
    (hbound :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound B primeData.p) :
    SlowPathHenselSubstrate core B primeData := by
  have hp_prime : Hex.Nat.Prime primeData.p :=
    hval.prime
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hprec_spec :
      2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hmodulus :
      2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by omega
  have hprec_pos : 1 ≤ Hex.precisionForCoeffBound B primeData.p := by
    by_contra hlt
    have hzero : Hex.precisionForCoeffBound B primeData.p = 0 := by omega
    rw [hzero, pow_zero] at hmodulus
    omega
  refine
    { corr := ?_
      partition := ?_
      liftedFactor_monic := ?_
      liftedFactor_natDegree_pos := ?_
      liftedFactor_inj := ?_
      modulus := ?_
      precision := ?_ }
  · exact henselSubsetCorrespondenceHypotheses_of_toMonicPrimeData
      core B primeData hval hcore_lc_pos hcore_pos hcore_prim
      hprec_pos hbound hB_ne_zero
  · exact liftedFactorSubsetPartition_of_toMonicPrimeData_complete
      core B primeData hval hcore_lc_pos hcore_pos hcore_prim
      hcore_sqfree hB_ne_zero hbound
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      hval hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      hval hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      hval hprec_pos
  · exact hmodulus
  · exact hprec_spec

/-- **#4549 base task (HO-1), outer-bound specialisation, rewired for #4553.**

Specialisation of `liftedFactorSubsetPartition_of_choosePrimeData`
(`HexBerlekampZassenhausMathlib`) at the precision count
actually consumed by the slow exhaustive branch of `Hex.ZPoly.factorize f`.
The resulting partition value has the exact `core` / `d` /
`J = Finset.univ` / `target = core` shape expected by the `hpartition`
hypothesis of the slow-path exhaustive-branch irreducibility wrapper
(PR #4537), so the HO-1 slow-path assembly can apply that wrapper
directly together with the #4543 base value at the same outer-bound
shape.

The explicit `hcore_sqfree` hypothesis previously threaded through this
constructor is now discharged internally from `f ≠ 0` via
`IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree`.
Downstream HO-1 assemblies only need to supply the much weaker non-zero
premise on `f`. -/
theorem liftedFactorSubsetPartition_outerBound_of_choosePrimeData
    (f : Hex.ZPoly) (hf : f ≠ 0)
    (hcore_pos : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0)
    (primeData : Hex.PrimeChoiceData)
    (hchoose :
      Hex.choosePrimeData? (Hex.normalizeForFactor f).squareFreeCore =
        some primeData)
    (hdescent :
      HenselLiftDescentHypotheses (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.exhaustiveLiftBound
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.defaultFactorCoeffBound f)) primeData
        (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.exhaustiveLiftBound
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f))
            primeData) True True)
    (hlifted_of_modP :
      ∀ {factor : Hex.ZPoly} {S : ModPFactorSubset primeData},
        Irreducible (HexPolyZMathlib.toPolynomial factor) →
        factor ∣ (Hex.normalizeForFactor f).squareFreeCore →
        RepresentsIntegerFactorModP primeData factor S →
        RepresentsIntegerFactorAtLift (Hex.normalizeForFactor f).squareFreeCore
          (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.exhaustiveLiftBound
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f))
            primeData) factor
          (liftedSubsetOfModPSubset primeData
            (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.exhaustiveLiftBound
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f))
            primeData)
            hdescent.factor_count_eq S))
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.toMonicLiftData
            (Hex.normalizeForFactor f).squareFreeCore
            (Hex.ZPoly.exhaustiveLiftBound
              (Hex.normalizeForFactor f).squareFreeCore
              (Hex.ZPoly.defaultFactorCoeffBound f))
            primeData)) :
    let core := (Hex.normalizeForFactor f).squareFreeCore
    let B := Hex.ZPoly.defaultFactorCoeffBound f
    let d := Hex.ZPoly.toMonicLiftData core (Hex.ZPoly.exhaustiveLiftBound core B)
      primeData
    LiftedFactorSubsetPartition core d Finset.univ core := by
  exact liftedFactorSubsetPartition_of_choosePrimeData_success_descent
    (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.exhaustiveLiftBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f))
      primeData (Hex.squareFreeCore_primitive_of_ne_zero f hf)
      (Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf)
      hcore_pos hchoose
      (IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf)
      hdescent hlifted_of_modP hinitial

/-- Descend irreducibility along the monic (`x ↦ x/ℓf`) transform: if the monic
transform of a primitive positive-degree core is irreducible, so is the core.
The dilation identity `dilate ℓf (toMonic core).monic = ℓf^(d-1) · core`
identifies the two up to a positive constant, which `primitivePart` strips. -/
theorem zpolyIrreducible_of_toMonicMonic_irreducible
    (core : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hm_irr : Hex.ZPoly.Irreducible (Hex.ZPoly.toMonic core).monic) :
    Hex.ZPoly.Irreducible core := by
  have hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree := by
    simp only [Hex.ZPoly.toMonic_degree]; omega
  have hM_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos (by simp only [Hex.ZPoly.toMonic_degree]; omega)
  have hkey : Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) (Hex.ZPoly.toMonic core).monic
      = Hex.DensePoly.scale
          (Hex.DensePoly.leadingCoeff core ^ ((Hex.ZPoly.toMonic core).degree - 1)) core := by
    have h := Hex.ZPoly.dilate_monic_toMonic core hdeg
    rwa [Hex.ZPoly.C_mul_eq_scale] at h
  have hrecover : Hex.ZPoly.primitivePart
      (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) (Hex.ZPoly.toMonic core).monic)
      = core := by
    rw [hkey]
    exact Hex.DensePoly.primitivePart_scale_of_primitive
      (pow_pos hcore_lc_pos _) hcore_prim
  rw [Hex.ZPoly.Irreducible_iff_polynomialIrreducible] at hm_irr ⊢
  exact (irreducible_toPolynomial_dilate_iff
    (ne_of_gt hcore_lc_pos) hM_monic hcore_prim hrecover).mpr hm_irr

/-- Small-mod singleton arm, keyed on the monic-transform prime selection
`toMonicPrimeData?` (the selector shared by the fast, lattice, and slow modular
tiers; #8519, #8533): a singleton mod-`p` factorisation of
`(toMonic core).monic` certifies its irreducibility over `ℤ`, which descends to
the primitive core along the dilation transform. -/
theorem squareFreeCore_irreducible_of_toMonicSmallModSingletonBranch
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hsmall : primeData.factorsModP.size ≤ 1) :
    Hex.ZPoly.Irreducible (Hex.normalizeForFactor f).squareFreeCore := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_prim : Hex.ZPoly.Primitive core :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hchoose : Hex.choosePrimeData? (Hex.ZPoly.toMonic core).monic = some primeData :=
    hselected
  have hM_monic : Hex.DensePoly.Monic (Hex.ZPoly.toMonic core).monic :=
    Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos (by simp only [Hex.ZPoly.toMonic_degree]; omega)
  have hm_deg : 0 < (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos
      (by simp only [Hex.ZPoly.toMonic_degree]; omega)]
    simpa using hcore_pos
  have hm_irr : Hex.ZPoly.Irreducible (Hex.ZPoly.toMonic core).monic :=
    IntReductionMod.squareFreeCore_irreducible_of_small_mod_singleton_of_choosePrimeData_squareFreeModP
      (Hex.ZPoly.toMonic core).monic primeData hchoose hm_deg hsmall
      (HexHenselMathlib.toPolynomial_monic_of_dense_monic _ hM_monic).isPrimitive
      (IntReductionMod.choosePrimeData?_leadingCoeff_castRingHom_ne_zero
        (Hex.ZPoly.toMonic core).monic primeData hchoose)
  exact zpolyIrreducible_of_toMonicMonic_irreducible core hcore_lc_pos hcore_pos
    hcore_prim hm_irr

set_option maxHeartbeats 8000000

set_option maxHeartbeats 4000000 in
set_option maxHeartbeats 8000000


/-- Divisibility propagation through `List.foldl (· * ·)` on `Hex.ZPoly`: if
`x` divides the accumulator at any point, it divides the final foldl. Used by
`mem_dvd_foldl_mul_zpoly`. -/
private theorem dvd_acc_foldl_mul_zpoly (x : Hex.ZPoly) :
    ∀ (l : List Hex.ZPoly) (acc : Hex.ZPoly),
      x ∣ acc → x ∣ l.foldl (· * ·) acc := by
  intro l
  induction l with
  | nil =>
      intro acc hacc
      simpa using hacc
  | cons head tail ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      refine ih (acc * head) ?_
      -- `x ∣ acc * head` from `x ∣ acc` via commutativity + `dvd_mul_left_poly`.
      have hcomm : acc * head = head * acc := Hex.DensePoly.mul_comm_poly (S := Int) acc head
      rw [hcomm]
      exact Hex.DensePoly.dvd_mul_left_poly head hacc

/-- An element of a `List Hex.ZPoly` divides the `List.foldl (· * ·)` of that
list. Used by the exhaustive-arm fuel-bound construction in
`reassemblyExpansionComplete_exhaustive_of_ne_zero`. -/
private theorem mem_dvd_foldl_mul_zpoly
    (l : List Hex.ZPoly) (acc : Hex.ZPoly) (x : Hex.ZPoly) (hx : x ∈ l) :
    x ∣ l.foldl (· * ·) acc := by
  induction l generalizing acc with
  | nil => exact absurd hx (List.not_mem_nil)
  | cons head tail ih =>
      rw [List.mem_cons] at hx
      simp only [List.foldl_cons]
      rcases hx with rfl | hx
      · -- `x = head`: divides `acc * x = acc * head`, and propagates through tail.
        refine dvd_acc_foldl_mul_zpoly x tail (acc * x) ?_
        have hcomm : acc * x = x * acc := Hex.DensePoly.mul_comm_poly (S := Int) acc x
        rw [hcomm]
        exact ⟨acc, rfl⟩
      · exact ih (acc * head) hx

/-- For a polynomial `q` of positive degree, the size of
`Hex.Factorization.factorPower q m` is at least `m + 1`. Each iteration of
`polyPow` multiplies the running product by `q`, increasing the size by at
least `q.size - 1 ≥ 1`. -/
private theorem factorPower_size_lower_bound
    {q : Hex.ZPoly} (hq_deg : 0 < q.degree?.getD 0) :
    ∀ m : Nat, m + 1 ≤ (Hex.Factorization.factorPower q m).size := by
  intro m
  -- From `0 < q.degree?.getD 0`, derive `2 ≤ q.size`.
  have hq_size_ge_two : 2 ≤ q.size := by
    have hdeg_unfold : q.degree?.getD 0 =
        (if q.size = 0 then 0 else q.size - 1) := by
      unfold Hex.DensePoly.degree?
      by_cases h : q.size = 0 <;> simp [h]
    rw [hdeg_unfold] at hq_deg
    by_cases h : q.size = 0
    · simp [h] at hq_deg
    · split at hq_deg <;> omega
  induction m with
  | zero =>
      show 1 ≤ (1 : Hex.ZPoly).size
      rfl
  | succ n ih =>
      rw [Hex.Factorization.factorPower_succ]
      have hprev_pos : 0 < (Hex.Factorization.factorPower q n).size := by
        omega
      have hq_pos : 0 < q.size := by omega
      have hmul_size :
          (Hex.Factorization.factorPower q n * q).size =
            (Hex.Factorization.factorPower q n).size + q.size - 1 :=
        Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_pos hq_pos
      omega

set_option maxHeartbeats 200000


/-- Mathlib-side abstract-bound wrapper for the slow-trial exhaustive arm.

Specialises the Mathlib-free
`Hex.exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible`
(`HexBerlekampZassenhaus`) to the normalized square-free
core of an `f ≠ 0` input, discharging the four core-shape hypotheses
(`ne_zero`, `Primitive`, `0 < leadingCoeff`, `SquareFreeRat`) from `hf_ne`
via the existing helpers:

* `Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero` for `0 < leadingCoeff`
  (and `zpoly_ne_zero_of_pos_lc` for `ne_zero`);
* `normalizeForFactor_squareFreeCore_primitive_of_ne_zero` (Mathlib-side)
  for `Primitive`;
* `Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore` for
  `SquareFreeRat`.

The divisor coefficient bound `hbound` stays explicit because two natural
specialisations live downstream: the intrinsic-core form
(`B := Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore`,
discharged below by `defaultFactorCoeffBound_valid` on the core) and the
public-bound form (`B := Hex.ZPoly.defaultFactorCoeffBound f`, required
by the slow-trial arm of the `h_raw` dispatch in
`factor_entry_zpolyIrreducible_of_chosen_raw_zpolyIrreducible`), which
needs the `g ∣ (Hex.normalizeForFactor f).squareFreeCore → g ∣ f`
divisibility chain through `primitiveSquareFreeDecomposition_reassembly_signed`
and the primitive-part divisibility relation. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat)
    (hbound : ∀ g : Hex.ZPoly,
      g ∣ (Hex.normalizeForFactor f).squareFreeCore →
      ∀ i, (g.coeff i).natAbs ≤ B) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore B).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_pos
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_sq : Hex.ZPoly.SquareFreeRat (Hex.normalizeForFactor f).squareFreeCore := by
    have hsq :=
      Hex.ZPoly.primitiveSquareFreeDecomposition_squareFreeCore
        (Hex.ZPoly.extractXPower (Hex.ZPoly.primitivePart f)).core
        (by simpa [Hex.normalizeForFactor] using hcore_ne)
    simpa [Hex.normalizeForFactor] using hsq
  exact Hex.exhaustiveIntegerTrialCoreFactorsWithBound_factor_irreducible
    (Hex.normalizeForFactor f).squareFreeCore B
    hcore_ne hcore_prim hcore_pos hcore_sq hbound factor hmem

/-- Intrinsic-core default-bound specialisation of
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound`
at `B := Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore`.

The divisor coefficient bound is discharged directly by
`defaultFactorCoeffBound_valid` applied to the (nonzero) square-free core.
This is the natural specialisation for callers that have already routed
through the core's intrinsic Mignotte data; the public slow-trial dispatch
in `Hex.factorTrialFactorsWithBound f (Hex.ZPoly.defaultFactorCoeffBound f)`
uses the outer bound `Hex.ZPoly.defaultFactorCoeffBound f`, which requires
an additional `(Hex.normalizeForFactor f).squareFreeCore ∣ f` divisibility
chain (tracked separately) to discharge against this wrapper's `hbound`. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_squareFreeCore_default
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.ZPoly.defaultFactorCoeffBound
                    (Hex.normalizeForFactor f).squareFreeCore)).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : (Hex.normalizeForFactor f).squareFreeCore ≠ 0 :=
    zpoly_ne_zero_of_pos_lc hcore_pos
  exact
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
      f hf_ne
      (Hex.ZPoly.defaultFactorCoeffBound (Hex.normalizeForFactor f).squareFreeCore)
      (defaultFactorCoeffBound_valid
        (Hex.normalizeForFactor f).squareFreeCore hcore_ne)
      factor hmem

/-- Transitivity of `∣` on `Hex.ZPoly`, Mathlib-side.  Composes the witness
multiplications explicitly. -/
private theorem zpoly_dvd_trans {a b c : Hex.ZPoly} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  obtain ⟨q, hq⟩ := hab
  obtain ⟨r, hr⟩ := hbc
  exact ⟨q * r, by rw [hr, hq, Hex.DensePoly.mul_assoc_poly (S := Int)]⟩

/-- Public-bound specialisation of
`exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound`
at the outer bound `B := Hex.ZPoly.defaultFactorCoeffBound f` consumed by the
slow-trial arm of the `h_raw` dispatch.

The divisor coefficient bound is discharged by lifting
`defaultFactorCoeffBound_valid f` along `Hex.squareFreeCore_dvd_self`: any
divisor of the square-free core also divides `f`, so its coefficients are
bounded by `Hex.ZPoly.defaultFactorCoeffBound f`. -/
theorem exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) :
    ∀ factor ∈ (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
                  (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.ZPoly.defaultFactorCoeffBound f)).toList,
      Hex.ZPoly.Irreducible factor := by
  intro factor hmem
  refine
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_of_bound
      f hf_ne (Hex.ZPoly.defaultFactorCoeffBound f) ?_ factor hmem
  intro g hg i
  exact defaultFactorCoeffBound_valid f hf_ne g
    (zpoly_dvd_trans hg (Hex.squareFreeCore_dvd_self f hf_ne)) i

/-- **Slow-trial exhaustive-arm reassembly discharger (Mathlib-side).**

When the slow trial path takes the exhaustive branch, the reassembly of the
integer-trial core factors of `(normalizeForFactor f).squareFreeCore` at the
public bound `B := Hex.ZPoly.defaultFactorCoeffBound f` is expansion-complete.
The integer-trial analog of
`reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero`: it
composes the public-bound core irreducibility wrapper, the polyProduct /
normalizeFactorSign / degree-positivity companions, and the non-monic
expansion-complete surface `reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc`.
Per-factor positive leading coefficient follows from the sign-normalisation
identity and irreducibility; the fuel bound from the per-factor
`factorPower` size lower bound and `size_le_of_dvd_nonzero`. -/
theorem reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f)
      (Hex.exhaustiveIntegerTrialCoreFactorsWithBound
        (Hex.normalizeForFactor f).squareFreeCore
        (Hex.ZPoly.defaultFactorCoeffBound f)) := by
  classical
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  set coreFactors :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f) with hcf
  have hirr : ∀ q ∈ coreFactors.toList, Hex.ZPoly.Irreducible q :=
    exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default f hf
  have hprod :
      Array.polyProduct coreFactors = (Hex.normalizeForFactor f).squareFreeCore :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_polyProduct _ _
  have hnorm : ∀ q ∈ coreFactors.toList, Hex.normalizeFactorSign q = q :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_normalizeFactorSign _ _ hcore_pos
  have hdegree : ∀ q ∈ coreFactors.toList, 0 < q.degree?.getD 0 :=
    Hex.exhaustiveIntegerTrialCoreFactorsWithBound_degree_pos _ _ hcore_prim hcore_pos
  -- Per-factor positive leading coefficient from `normalizeFactorSign q = q`
  -- and irreducibility (hence `q ≠ 0`).
  have hpos_lc : ∀ q ∈ coreFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      by_contra hlt
      have hlt' : Hex.DensePoly.leadingCoeff q < 0 := lt_of_not_ge hlt
      unfold Hex.normalizeFactorSign at hq_norm
      rw [if_pos hlt'] at hq_norm
      apply hq_ne
      apply Hex.DensePoly.ext_coeff
      intro n
      have hcoeff :
          (Hex.DensePoly.scale (-1 : Int) q).coeff n = q.coeff n := by
        rw [hq_norm]
      rw [Hex.DensePoly.coeff_scale (R := Int) (-1) q n
        (by decide : (-1 : Int) * 0 = 0)] at hcoeff
      rw [Hex.DensePoly.coeff_zero]
      omega
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  refine IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf coreFactors hirr hprod hnorm hpos_lc hdegree ?_
  -- Fuel bound.
  intro exponents hlen hdecomp
  have hsize_ge : ∀ q ∈ coreFactors.toList, 2 ≤ q.size := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_size_pos : 0 < q.size := Hex.ZPoly.size_pos_of_ne_zero q hq_ne
    have hq_deg := hdegree q hq
    have hq_deg_eq : q.degree?.getD 0 = q.size - 1 := by
      unfold Hex.DensePoly.degree?
      simp [Nat.ne_of_gt hq_size_pos]
    omega
  have hrp_ne_zero : (Hex.normalizeForFactor f).repeatedPart ≠ 0 := by
    intro hzero
    have hR_prim :=
      IntReductionMod.normalizeForFactor_repeatedPart_toPolynomial_isPrimitive f hf
    apply hR_prim.ne_zero
    show HexPolyZMathlib.toPolynomial (Hex.normalizeForFactor f).repeatedPart = 0
    rw [hzero]
    exact HexPolyZMathlib.toPolynomial_zero
  have dvd_foldl_one_of_mem :
      ∀ (x : Hex.ZPoly) (xs : List Hex.ZPoly),
        x ∈ xs → x ∣ xs.foldl (· * ·) (1 : Hex.ZPoly) := by
    intro x xs
    induction xs with
    | nil =>
        intro hmem
        exact absurd hmem List.not_mem_nil
    | cons y ys ih =>
        intro hmem
        rcases List.mem_cons.mp hmem with rfl | hin
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one]
          exact ⟨ys.foldl (· * ·) 1, rfl⟩
        · rw [List.foldl_cons, Hex.ZPoly.one_mul_zpoly,
              Hex.ZPoly.list_foldl_mul_eq_mul_foldl_one y ys]
          obtain ⟨k, hk⟩ := ih hin
          refine ⟨y * k, ?_⟩
          rw [hk, ← Hex.DensePoly.mul_assoc_poly (S := Int),
              Hex.DensePoly.mul_comm_poly (S := Int) y x,
              Hex.DensePoly.mul_assoc_poly (S := Int)]
  have factorPower_size_lb :
      ∀ (q : Hex.ZPoly) (e : Nat),
        2 ≤ q.size → e + 1 ≤ (Hex.Factorization.factorPower q e).size := by
    intro q e hq_size
    induction e with
    | zero =>
        show 1 ≤ (1 : Hex.ZPoly).size
        rfl
    | succ n ih =>
        rw [Hex.Factorization.factorPower_succ]
        have hprev_size_pos :
            0 < (Hex.Factorization.factorPower q n).size := by omega
        have hq_size_pos : 0 < q.size := by omega
        have hmul_size :
            (Hex.Factorization.factorPower q n * q).size =
              (Hex.Factorization.factorPower q n).size + q.size - 1 :=
          Hex.ZPoly.mul_size_eq_top_succ_of_nonzero _ _ hprev_size_pos hq_size_pos
        omega
  intro qe hqe_mem
  have hq_mem : qe.1 ∈ coreFactors.toList := List.of_mem_zip hqe_mem |>.1
  have hq_size := hsize_ge qe.1 hq_mem
  have hfp_size_lb :
      qe.2 + 1 ≤ (Hex.Factorization.factorPower qe.1 qe.2).size :=
    factorPower_size_lb qe.1 qe.2 hq_size
  have hfp_ne_zero : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
    intro hzero
    rw [hzero] at hfp_size_lb
    have h0 : (0 : Hex.ZPoly).size = 0 := rfl
    omega
  have hfp_mem :
      Hex.Factorization.factorPower qe.1 qe.2 ∈
        ((coreFactors.toList.zip exponents).map
          (fun qe' => Hex.Factorization.factorPower qe'.1 qe'.2)) :=
    List.mem_map.mpr ⟨qe, hqe_mem, rfl⟩
  have hfp_dvd_rp :
      Hex.Factorization.factorPower qe.1 qe.2 ∣
        (Hex.normalizeForFactor f).repeatedPart := by
    rw [hdecomp]
    exact dvd_foldl_one_of_mem _ _ hfp_mem
  have hfp_size_le :
      (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
    Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne_zero hrp_ne_zero hfp_dvd_rp
  omega

/--
Reassembly expansion-completeness for the fast BHKS core-success branch from loop
success plus core-factor irreducibility, with **no** forward-cut hypothesis.

This factors the cut-free part of `fastCoreComplete_of_cut`
(`PartitionRefinement.lean`): the product, sign-normalisation, degree, leading-
coefficient, and fuel facts are all unconditional consequences of the loop
success `hcore`; only the per-factor irreducibility `hirr` (there derived from
the forward cut) is taken as a hypothesis here, isolating the cut dependence.
Consumed by the capstone assembly `fastCoreRawGuarded_of_coreIrreducible`
(`FactorSoundness.lean`).
-/
theorem fastCoreReassemblyComplete_of_coreIrreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {expectedFactors : Array Hex.ZPoly}
    (hcore :
      Hex.bhksRecoveryCoreWithBound (Hex.normalizeForFactor f).squareFreeCore B
        primeData (Hex.initialHenselPrecision B)
        (Hex.ZPoly.quadraticDoublingSteps B + 2) =
          some expectedFactors)
    (hirr : ∀ q ∈ expectedFactors.toList, Hex.ZPoly.Irreducible q) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) expectedFactors := by
  have hprod :
      Array.polyProduct expectedFactors =
        (Hex.normalizeForFactor f).squareFreeCore := by
    simpa using
      Hex.bhksRecoveryCoreWithBound_product
        (Hex.normalizeForFactor f).squareFreeCore B primeData
        (Hex.initialHenselPrecision B) (Hex.ZPoly.quadraticDoublingSteps B + 2)
        expectedFactors hcore
  have hnorm :
      ∀ q ∈ expectedFactors.toList, Hex.normalizeFactorSign q = q := by
    intro q hq
    exact Hex.bhksRecoveryCoreWithBound_some_normalizeFactorSign hcore q hq
  have hdegree :
      ∀ q ∈ expectedFactors.toList, 0 < q.degree?.getD 0 := by
    intro q hq
    exact Hex.bhksRecoveryCoreWithBound_some_degree_pos hcore q hq
  have hpos_lc :
      ∀ q ∈ expectedFactors.toList, 0 < Hex.DensePoly.leadingCoeff q := by
    intro q hq
    have hq_ne : q ≠ 0 := (hirr q hq).not_zero
    have hq_norm : Hex.normalizeFactorSign q = q := hnorm q hq
    have hq_nonneg : 0 ≤ Hex.DensePoly.leadingCoeff q := by
      rw [← hq_norm]
      exact leadingCoeff_normalizeFactorSign_nonneg q
    have hq_lc_ne : Hex.DensePoly.leadingCoeff q ≠ 0 :=
      Hex.ZPoly.leadingCoeff_ne_zero_of_ne_zero q hq_ne
    omega
  have hrp_ne :
      (Hex.normalizeForFactor f).repeatedPart ≠ 0 :=
    Hex.repeatedPart_ne_zero_of_ne_zero f hf_ne
  have hfuel :
      ∀ exponents : List Nat,
        exponents.length = expectedFactors.size →
        (Hex.normalizeForFactor f).repeatedPart =
          ((expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 →
        ∀ (qe : Hex.ZPoly × Nat),
          qe ∈ expectedFactors.toList.zip exponents →
            qe.2 + 1 ≤ (Hex.normalizeForFactor f).repeatedPart.size + 1 := by
    intro exponents _ hdecomp qe hqe
    have hq_mem : qe.1 ∈ expectedFactors.toList :=
      (List.of_mem_zip hqe).1
    have hq_deg : 0 < qe.1.degree?.getD 0 := hdegree qe.1 hq_mem
    have hfp_size_lb : qe.2 + 1 ≤
        (Hex.Factorization.factorPower qe.1 qe.2).size :=
      factorPower_size_lower_bound hq_deg qe.2
    have hfp_ne : Hex.Factorization.factorPower qe.1 qe.2 ≠ 0 := by
      intro h0
      have : (Hex.Factorization.factorPower qe.1 qe.2).size = 0 := by
        rw [h0]
        rfl
      omega
    have hfp_in_map :
        Hex.Factorization.factorPower qe.1 qe.2 ∈
          (expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2) := by
      rw [List.mem_map]
      exact ⟨qe, hqe, rfl⟩
    have hfp_dvd :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          ((expectedFactors.toList.zip exponents).map
            (fun qe => Hex.Factorization.factorPower qe.1 qe.2)).foldl (· * ·) 1 :=
      mem_dvd_foldl_mul_zpoly _ 1 _ hfp_in_map
    have hfp_dvd_rp :
        Hex.Factorization.factorPower qe.1 qe.2 ∣
          (Hex.normalizeForFactor f).repeatedPart := by
      rw [hdecomp]
      exact hfp_dvd
    have hsize_le : (Hex.Factorization.factorPower qe.1 qe.2).size ≤
        (Hex.normalizeForFactor f).repeatedPart.size :=
      Hex.ZPoly.size_le_of_dvd_nonzero hfp_ne hrp_ne hfp_dvd_rp
    omega
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc
    f hf_ne expectedFactors hirr hprod hnorm hpos_lc hdegree hfuel

/-- **#8413 (classical-tier irreducibility).**  Every factor the size-ordered
classical recombination search returns is irreducible: when
`classicalCoreFactorsWithBound core B primeData = some cf` for a nonzero,
primitive, square-free, positive-degree `core` selected by `toMonicPrimeData?`,
each entry of `cf` is irreducible over `ℤ`.

The coefficient bound is surfaced as an abstract parameter `B'` (mirroring the
exhaustive-tier `…_of_bound` shape): the caller supplies the leading-coefficient
bound `(leadingCoeff core).natAbs ≤ B'`, the all-divisors validity
`∀ g ∣ core, ∀ i, |g.coeff i| ≤ B'`, and the precision `2 * B' < …`.  This lets a
factor of a *larger* polynomial `f` (with `core ∣ f`) be handled at
`B' = defaultFactorCoeffBound f` via Mignotte, without a
`defaultFactorCoeffBound core ≤ defaultFactorCoeffBound f` monotonicity lemma.
Every other input is discharged from `toMonicPrimeData?` and the core side
conditions.  Coverage (`RecoveredSmartSearch.covers_of_bound`) + product
reconstruction + the `shouldRecord` gate + the square-free counting
(`smartCore_factor_irreducible_of_covers_of_squarefree`) give irreducibility;
`trustworthyNone_of_bound` rules out the accepted-`none` branch. -/
theorem classicalCoreFactorsWithBound_factor_irreducible_of_validBound
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {cf : Array Hex.ZPoly}
    (hclassical : Hex.classicalCoreFactorsWithBound core B primeData = some cf)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hcore_pos : 0 < core.degree?.getD 0)
    (hB_ne : B ≠ 0)
    (B' : Nat)
    (hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤ B')
    (hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i, (g.coeff i).natAbs ≤ B')
    (hprecision : 2 * B' <
      primeData.p ^
        Hex.precisionForCoeffBound (Hex.ZPoly.exhaustiveLiftBound core B) primeData.p) :
    ∀ g ∈ cf.toList, Irreducible (HexPolyZMathlib.toPolynomial g) := by
  classical
  set LB := Hex.ZPoly.exhaustiveLiftBound core B with hLB_def
  have hLB_ne : LB ≠ 0 := by
    have := Hex.ZPoly.le_exhaustiveLiftBound core B; rw [← hLB_def] at this; omega
  have hp_prime : Hex.Nat.Prime primeData.p :=
    hval.prime
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hbound_monic :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        primeData.p ^ Hex.precisionForCoeffBound LB primeData.p := by
    rw [hLB_def]; exact IntReductionMod.exhaustiveLiftBound_monic_precision core B primeData.p hp2
  have hmodulus : 2 ≤ primeData.p ^ Hex.precisionForCoeffBound LB primeData.p := by
    have hprec_spec : 2 * LB < primeData.p ^ Hex.precisionForCoeffBound LB primeData.p :=
      Hex.precisionForCoeffBound_spec hp2 LB
    have : 1 ≤ LB := Nat.one_le_iff_ne_zero.mpr hLB_ne; omega
  have hprec_pos : 1 ≤ Hex.precisionForCoeffBound LB primeData.p := by
    by_contra hlt
    have hz : Hex.precisionForCoeffBound LB primeData.p = 0 := by omega
    rw [hz, pow_zero] at hmodulus; omega
  have hp_eq : (Hex.ZPoly.toMonicLiftData core LB primeData).p = primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_p _ _ _
  have hk_eq : (Hex.ZPoly.toMonicLiftData core LB primeData).k =
      Hex.precisionForCoeffBound LB primeData.p := by
    unfold Hex.ZPoly.toMonicLiftData; exact Hex.henselLiftData_k _ _ _
  have hd_modulus : 2 ≤ (Hex.ZPoly.toMonicLiftData core LB primeData).p ^
      (Hex.ZPoly.toMonicLiftData core LB primeData).k := by rw [hp_eq, hk_eq]; exact hmodulus
  have hprecision_dk : 2 * B' <
      (Hex.ZPoly.toMonicLiftData core LB primeData).p ^
        (Hex.ZPoly.toMonicLiftData core LB primeData).k := by
    rw [hp_eq, hk_eq]; exact hprecision
  have hlf_monic : ∀ i, Hex.DensePoly.Monic
      (liftedFactor (Hex.ZPoly.toMonicLiftData core LB primeData) i) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData core LB primeData
      hcore_lc_pos hcore_pos
      hval hprec_pos
  have hlf_natdeg : ∀ i, 0 < (HexPolyZMathlib.toPolynomial
      (liftedFactor (Hex.ZPoly.toMonicLiftData core LB primeData) i)).natDegree :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData core LB primeData
      hcore_lc_pos hcore_pos
      hval hprec_pos
  have hlf_inj : Function.Injective (liftedFactor (Hex.ZPoly.toMonicLiftData core LB primeData)) :=
    Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData core LB primeData
      hcore_lc_pos hcore_pos
      hval hprec_pos
  have hpartition : LiftedFactorSubsetPartition core
      (Hex.ZPoly.toMonicLiftData core LB primeData) Finset.univ core :=
    liftedFactorSubsetPartition_of_toMonicPrimeData_complete core LB primeData hval
      hcore_lc_pos hcore_pos hcore_primitive hcore_sqfree hLB_ne hbound_monic
  have hmatches : LiftedFactorListMatches (Hex.ZPoly.toMonicLiftData core LB primeData)
      Finset.univ (Hex.ZPoly.toMonicLiftData core LB primeData).liftedFactors.toList :=
    LiftedFactorListMatches.univ _
  -- `Finset.univ` cardinality equals the local-factor list length.
  have hcard : (Finset.univ : LiftedFactorSubset
      (Hex.ZPoly.toMonicLiftData core LB primeData)).card =
      (Hex.ZPoly.toMonicLiftData core LB primeData).liftedFactors.toList.length :=
    LiftedFactorListMatches.length_eq_card hmatches |>.symm
  -- Extract the underlying `scaledRecombinationSmartAux` result from the search.
  rw [Hex.classicalCoreFactorsWithBound, if_neg hB_ne] at hclassical
  simp only [Hex.scaledRecombinationSmart, ← hLB_def] at hclassical
  set localFactors := (Hex.ZPoly.toMonicLiftData core LB primeData).liftedFactors.toList
    with hlf_def
  set budget := Hex.levelAwareSubsetBudget localFactors.length Hex.defaultSubsetBudget
    with hbudget_def
  set fuel := budget + (localFactors.length + 1) * (2 * localFactors.length + 3)
    with hfuel_def
  have hfuel_adeq : budget + smartFuelBound
      (Finset.univ : LiftedFactorSubset
        (Hex.ZPoly.toMonicLiftData core LB primeData)).card ≤ fuel := by
    rw [hcard, hfuel_def]; simp only [smartFuelBound, le_refl]
  have hmod_bridge :
      Hex.liftModulus (Hex.ZPoly.toMonicLiftData core LB primeData) =
        (Hex.ZPoly.toMonicLiftData core LB primeData).p ^
          (Hex.ZPoly.toMonicLiftData core LB primeData).k := rfl
  have hcore_dvd : core ∣ core := Hex.DensePoly.dvd_refl_poly core
  cases haux : Hex.scaledRecombinationSmartAux (Hex.DensePoly.leadingCoeff core) core
      (Hex.liftModulus (Hex.ZPoly.toMonicLiftData core LB primeData)) localFactors
      budget fuel with
  | mk res remaining =>
    rw [haux] at hclassical
    rw [hmod_bridge] at haux
    cases res with
    | none =>
      simp only [Option.isNone_none, Bool.true_and] at hclassical
      by_cases hrem : remaining = 0
      · subst hrem; simp at hclassical
      · exact absurd
          (RecoveredSmartSearch.trustworthyNone_of_bound B' hcore_lc_le hvalid
            hcore_ne hcore_primitive hcore_lc_pos
            hd_modulus hlf_monic hlf_natdeg hlf_inj hprecision_dk hcore_primitive
            hcore_lc_pos hcore_dvd hpartition hmatches hfuel_adeq haux) hrem
    | some factors =>
      simp only [Option.isNone_some, Bool.false_and, Bool.false_eq_true, if_false]
        at hclassical
      have hcover := RecoveredSmartSearch.covers_of_bound B' hcore_lc_le hvalid
        hcore_ne hcore_primitive hcore_lc_pos
        hd_modulus hlf_monic hlf_natdeg hlf_inj hprecision_dk hcore_primitive hcore_lc_pos
        hcore_dvd hpartition hmatches hfuel_adeq haux
      have hprod := Hex.scaledRecombinationSmartAux_product _ _ _ _ _ _ _ _ haux
      have hrecord := Hex.scaledRecombinationSmartAux_shouldRecord _ _ _ _ _ _ _ _ haux
      have hirr := smartCore_factor_irreducible_of_covers_of_squarefree hcore_ne hcore_sqfree
        hprod hrecord hcover
      have hne : factors.isEmpty = false := by
        by_contra hc
        simp only [Bool.not_eq_false] at hc
        rw [List.isEmpty_iff] at hc
        rw [hc, show (([] : List Hex.ZPoly).toArray) = (#[] : Array Hex.ZPoly) from rfl,
          Hex.ZPoly.polyProduct_empty] at hprod
        rw [← hprod, show (1 : Hex.ZPoly) = Hex.DensePoly.C 1 from rfl,
          Hex.DensePoly.degree?_C_getD] at hcore_pos
        exact absurd hcore_pos (lt_irrefl 0)
      simp only [hne] at hclassical
      obtain rfl := Option.some.inj hclassical
      intro g hg
      rw [List.toList_toArray] at hg
      exact hirr g hg

/-- **#8413 (classical-tier irreducibility, default-bound form).**  The
`B' = defaultFactorCoeffBound core` specialization of
`classicalCoreFactorsWithBound_factor_irreducible_of_validBound`: the abstract
leading-coefficient and all-divisors bound hypotheses are discharged from
`defaultFactorCoeffBound_leadingCoeff_natAbs_le` and `defaultFactorCoeffBound_valid`,
so the only precision side condition is
`2 * defaultFactorCoeffBound core < …`, threaded as in the exhaustive-tier
`…_of_bound` theorems. -/
theorem classicalCoreFactorsWithBound_factor_irreducible_of_bound
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {cf : Array Hex.ZPoly}
    (hclassical : Hex.classicalCoreFactorsWithBound core B primeData = some cf)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hcore_pos : 0 < core.degree?.getD 0)
    (hB_ne : B ≠ 0)
    (hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core <
      primeData.p ^
        Hex.precisionForCoeffBound (Hex.ZPoly.exhaustiveLiftBound core B) primeData.p) :
    ∀ g ∈ cf.toList, Irreducible (HexPolyZMathlib.toPolynomial g) :=
  classicalCoreFactorsWithBound_factor_irreducible_of_validBound core B primeData
    hclassical
    (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos)
    hcore_ne hcore_primitive hcore_lc_pos hcore_sqfree hcore_pos
    hB_ne (Hex.ZPoly.defaultFactorCoeffBound core)
    (defaultFactorCoeffBound_leadingCoeff_natAbs_le hcore_ne)
    (defaultFactorCoeffBound_valid core hcore_ne) hprecision

/-- **#8413 (classical-tier irreducibility, natural-bound form).**  The precision
side condition of `classicalCoreFactorsWithBound_factor_irreducible_of_bound` is
discharged from the natural hypothesis `defaultFactorCoeffBound core ≤ B` (which
also gives `B ≠ 0`, since a positive-degree core has a positive Mignotte bound):
`exhaustiveLiftBound core B` dominates `B` and hence `defaultFactorCoeffBound
core`, so `precisionForCoeffBound_spec` supplies the Mignotte precision.  In
particular this applies with `B = defaultFactorCoeffBound core` (`le_refl`). -/
theorem classicalCoreFactorsWithBound_factor_irreducible
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    {cf : Array Hex.ZPoly}
    (hclassical : Hex.classicalCoreFactorsWithBound core B primeData = some cf)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_ne : core ≠ 0)
    (hcore_primitive : Hex.ZPoly.Primitive core)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hcore_pos : 0 < core.degree?.getD 0)
    (hbound_le : Hex.ZPoly.defaultFactorCoeffBound core ≤ B) :
    ∀ g ∈ cf.toList, Irreducible (HexPolyZMathlib.toPolynomial g) := by
  have hdfb_pos : 0 < Hex.ZPoly.defaultFactorCoeffBound core :=
    Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hcore_ne
  have hB_ne : B ≠ 0 := by omega
  have hp2 : 2 ≤ primeData.p :=
    (Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected).two_le
  have hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound core <
      primeData.p ^
        Hex.precisionForCoeffBound (Hex.ZPoly.exhaustiveLiftBound core B) primeData.p := by
    have hle : Hex.ZPoly.defaultFactorCoeffBound core ≤ Hex.ZPoly.exhaustiveLiftBound core B :=
      le_trans hbound_le (Hex.ZPoly.le_exhaustiveLiftBound core B)
    have hspec := Hex.precisionForCoeffBound_spec hp2 (Hex.ZPoly.exhaustiveLiftBound core B)
    omega
  exact classicalCoreFactorsWithBound_factor_irreducible_of_bound core B primeData
    hclassical hselected hcore_ne hcore_primitive hcore_lc_pos hcore_sqfree hcore_pos
    hB_ne hprecision

/-- **#8510 (classical residual-arm specialization).**  Every factor the
size-ordered classical recombination search returns for the square-free core of
`normalizeForFactor f` at the hybrid search bound `B = defaultFactorCoeffBound f`
is irreducible in the executable `Hex.ZPoly` sense.

This is the classical analogue of the exhaustive-tier default-bound block: the
search runs at `defaultFactorCoeffBound f`, but the *coefficient* bound is set to
`B' = defaultFactorCoeffBound f` (not `defaultFactorCoeffBound core`, for which no
monotonicity lemma exists).  Validity is sound because
`core = (normalizeForFactor f).squareFreeCore ∣ f`, so every divisor of `core` is
a divisor of `f`, bounded by `defaultFactorCoeffBound f` via Mignotte
(`defaultFactorCoeffBound_valid f ∘ zpoly_dvd_trans ∘ squareFreeCore_dvd_self`),
and the lift modulus exceeds `2 * defaultFactorCoeffBound f`
(`exhaustiveLiftBound_precision`).  The `Polynomial ℤ` irreducibility from
`classicalCoreFactorsWithBound_factor_irreducible_of_validBound` is transported
back to `Hex.ZPoly.Irreducible` per factor.  Consumed (with the
completeness-structural lemmas of #8511) by the classical residual arm of #8414. -/
theorem classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible
    (f : Hex.ZPoly) (hf_ne : f ≠ 0) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {cf : Array Hex.ZPoly}
    (hclassical : Hex.classicalCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f) primeData = some cf) :
    ∀ g ∈ cf.toList, Hex.ZPoly.Irreducible g := by
  set core := (Hex.normalizeForFactor f).squareFreeCore with hcore_def
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf_ne
  have hcore_ne : core ≠ 0 := zpoly_ne_zero_of_pos_lc hcore_lc_pos
  have hcore_primitive : Hex.ZPoly.Primitive core :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf_ne
  have hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core) :=
    IntReductionMod.normalizeForFactor_squareFreeCore_toPolynomial_squarefree f hf_ne
  have hcore_pos : 0 < core.degree?.getD 0 := Nat.pos_of_ne_zero hdeg_ne
  have hp2 : 2 ≤ primeData.p :=
    (Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected).two_le
  have hcore_dvd_f : core ∣ f := Hex.squareFreeCore_dvd_self f hf_ne
  have hcore_lc_le : (Hex.DensePoly.leadingCoeff core).natAbs ≤
      Hex.ZPoly.defaultFactorCoeffBound f := by
    have hsize_pos : 0 < core.size := Hex.ZPoly.size_pos_of_ne_zero core hcore_ne
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last _ hsize_pos]
    exact defaultFactorCoeffBound_valid f hf_ne core hcore_dvd_f (core.size - 1)
  have hvalid : ∀ g : Hex.ZPoly, g ∣ core → ∀ i,
      (g.coeff i).natAbs ≤ Hex.ZPoly.defaultFactorCoeffBound f := by
    intro g hg i
    exact defaultFactorCoeffBound_valid f hf_ne g (zpoly_dvd_trans hg hcore_dvd_f) i
  have hprecision : 2 * Hex.ZPoly.defaultFactorCoeffBound f <
      primeData.p ^
        Hex.precisionForCoeffBound
          (Hex.ZPoly.exhaustiveLiftBound core (Hex.ZPoly.defaultFactorCoeffBound f))
          primeData.p :=
    IntReductionMod.exhaustiveLiftBound_precision core
      (Hex.ZPoly.defaultFactorCoeffBound f) primeData.p hp2
  have hB_ne : Hex.ZPoly.defaultFactorCoeffBound f ≠ 0 :=
    (Hex.ZPoly.defaultFactorCoeffBound_pos_of_ne_zero hf_ne).ne'
  have hirr := classicalCoreFactorsWithBound_factor_irreducible_of_validBound core
    (Hex.ZPoly.defaultFactorCoeffBound f) primeData hclassical
    (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos)
    hcore_ne
    hcore_primitive hcore_lc_pos hcore_sqfree hcore_pos hB_ne
    (Hex.ZPoly.defaultFactorCoeffBound f) hcore_lc_le hvalid hprecision
  intro g hg
  exact (Hex.ZPoly.Irreducible_iff_polynomialIrreducible g).mpr (hirr g hg)

/-- **Classical residual-arm reassembly discharger (Mathlib-side).**

When the classical small-`r` tier returns a recombination of the classical core
factors of `(normalizeForFactor f).squareFreeCore` at the public bound
`B := Hex.ZPoly.defaultFactorCoeffBound f`, the reassembly is
expansion-complete.  The size-ordered classical analog of
`reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero`: it composes the
public-bound classical-core irreducibility wrapper
`classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible` (#8510),
the polyProduct / normalizeFactorSign / degree-positivity structural companions
(#8511, `classicalCoreFactorsWithBound_{polyProduct,normalizeFactorSign,degree_pos}`),
and the sign-normalized expansion-complete surface
`reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm` (which
derives the per-factor positive leading coefficient and the fuel bound
internally).  Consumed by the classical residual arm of
`factorClassicalFactorsWithBound_factor_irreducible` (#8414). -/
theorem reassemblyExpansionComplete_classicalCore_of_ne_zero
    (f : Hex.ZPoly) (hf : f ≠ 0) (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore
      = some primeData)
    (hdeg_ne : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 ≠ 0)
    {cf : Array Hex.ZPoly}
    (hclassical : Hex.classicalCoreFactorsWithBound
      (Hex.normalizeForFactor f).squareFreeCore
      (Hex.ZPoly.defaultFactorCoeffBound f) primeData = some cf) :
    Hex.reassemblyExpansionComplete (Hex.normalizeForFactor f) cf := by
  classical
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_deg : 0 < (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 :=
    Nat.pos_of_ne_zero hdeg_ne
  exact IntReductionMod.reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_norm
    f hf cf
    (classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible
      f hf primeData hselected hdeg_ne hclassical)
    (Hex.classicalCoreFactorsWithBound_polyProduct _ _ _ hclassical)
    (Hex.classicalCoreFactorsWithBound_normalizeFactorSign _ _ _ hcore_pos hclassical)
    (Hex.classicalCoreFactorsWithBound_degree_pos _ _ _ hcore_deg hclassical)

/-- **Trial-branch raw-factor irreducibility (hybrid guard form).**

Trial-branch raw-factor irreducibility for the cost-based hybrid, where the
trial arm fires as the totality backstop.  Because the deg-0 (constant-core)
short-circuit is reachable, the raw output can contain the unit `1`, so the
statement carries the `shouldRecordPolynomialFactor` guard that excludes it.  The
two positive-degree arms reuse the quadratic and exhaustive integer-trial
completeness/irreducibility content. -/
theorem factorTrialFactorsWithBound_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ (Hex.factorTrialFactorsWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f)).toList)
    (hrec : Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  simp only [Hex.factorTrialFactorsWithBound] at hmem
  by_cases hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdeg] at hmem
    have hcomplete := Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf hdeg
    rcases Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
        _ _ raw hcomplete hmem with hx | hcore
    · exact Hex.xPowerFactorArray_irreducible _ raw hx
    · exfalso
      have hraw_one : raw = 1 := by
        have hraw_core : raw = (Hex.normalizeForFactor f).squareFreeCore := by
          simpa using hcore
        rw [hraw_core, Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdeg]
      rw [hraw_one, Hex.normalizeFactorSign_one, Hex.shouldRecordPolynomialFactor_one] at hrec
      exact absurd hrec (by decide)
  · rw [if_neg hdeg] at hmem
    cases hquad :
        Hex.quadraticIntegerRootFactors? (Hex.normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        simp only [hquad] at hmem
        refine Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          _ _ ?_ ?_ hmem
        · exact IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
            f hf hquad
        · intro factor hfmem
          exact Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
            hcore_pos hcore_prim hquad hfmem
    | none =>
        simp only [hquad] at hmem
        refine Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          _ _ ?_ ?_ hmem
        · exact reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero f hf
        · exact
            exhaustiveIntegerTrialCoreFactorsWithBound_normalizeForFactor_factor_irreducible_at_default
              f hf

/-- **Classical-branch raw-factor irreducibility.**

Every raw factor of the classical tier's output `factorClassicalFactorsWithBound
f (defaultFactorCoeffBound f)` that passes the recorded-factor filter is
irreducible.  Case-split over the branch: deg-0 constant short-circuit, quadratic
integer-root short-circuit, and the size-ordered recombination residual.

The residual arm composes the bound-parameterized classical core irreducibility
`classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible` (#8510) with
the reassembly-completeness discharger
`reassemblyExpansionComplete_classicalCore_of_ne_zero` (#8511) through the lift
`reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible`.
The bound is handled at `defaultFactorCoeffBound f` directly (validity from
`core ∣ f`, precision from `exhaustiveLiftBound_precision`), so no
`defaultFactorCoeffBound core ≤ defaultFactorCoeffBound f` monotonicity is needed. -/
theorem factorClassicalFactorsWithBound_factor_irreducible
    (f : Hex.ZPoly) (hf : f ≠ 0)
    {cf : Array Hex.ZPoly}
    (hcf : Hex.factorClassicalFactorsWithBound f
      (Hex.ZPoly.defaultFactorCoeffBound f) = some cf)
    {raw : Hex.ZPoly}
    (hmem : raw ∈ cf.toList)
    (hrec : Hex.shouldRecordPolynomialFactor (Hex.normalizeFactorSign raw) = true) :
    Hex.ZPoly.Irreducible raw := by
  have hcore_pos := Hex.squareFreeCore_leadingCoeff_pos_of_ne_zero f hf
  have hcore_prim :=
    IntReductionMod.normalizeForFactor_squareFreeCore_primitive_of_ne_zero f hf
  simp only [Hex.factorClassicalFactorsWithBound] at hcf
  by_cases hdeg : (Hex.normalizeForFactor f).squareFreeCore.degree?.getD 0 = 0
  · rw [if_pos hdeg] at hcf
    obtain rfl := Option.some.inj hcf
    have hcomplete := Hex.reassemblyExpansionComplete_constant_of_ne_zero f hf hdeg
    rcases Hex.reassemblePolynomialFactors_mem_xPower_or_core_of_expansionComplete
        _ _ raw hcomplete hmem with hx | hcore
    · exact Hex.xPowerFactorArray_irreducible _ raw hx
    · exfalso
      have hraw_one : raw = 1 := by
        have hraw_core : raw = (Hex.normalizeForFactor f).squareFreeCore := by
          simpa using hcore
        rw [hraw_core, Hex.squareFreeCore_eq_one_of_constant_of_ne_zero f hf hdeg]
      rw [hraw_one, Hex.normalizeFactorSign_one, Hex.shouldRecordPolynomialFactor_one] at hrec
      exact absurd hrec (by decide)
  · rw [if_neg hdeg] at hcf
    cases hquad :
        Hex.quadraticIntegerRootFactors? (Hex.normalizeForFactor f).squareFreeCore with
    | some coreFactors =>
        simp only [hquad] at hcf
        obtain rfl := Option.some.inj hcf
        refine Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
          _ _ ?_ ?_ hmem
        · exact IntReductionMod.reassemblyExpansionComplete_quadraticIntegerRootFactors_of_ne_zero
            f hf hquad
        · intro factor hfmem
          exact Hex.quadraticIntegerRootFactors?_factor_irreducible_of_primitive
            hcore_pos hcore_prim hquad hfmem
    | none =>
        simp only [hquad] at hcf
        cases hsel :
            Hex.ZPoly.toMonicPrimeData? (Hex.normalizeForFactor f).squareFreeCore with
        | none => simp [hsel] at hcf
        | some primeData =>
            simp only [hsel, Option.bind_some] at hcf
            cases hcore :
                Hex.classicalCoreFactorsWithBound (Hex.normalizeForFactor f).squareFreeCore
                  (Hex.ZPoly.defaultFactorCoeffBound f) primeData with
            | none => simp [hcore] at hcf
            | some coreFactors =>
                simp only [hcore, Option.map_some] at hcf
                obtain rfl := Option.some.inj hcf
                -- Residual arm: the size-ordered classical recombination core.
                -- Per-factor irreducibility from #8510, reassembly completeness
                -- from #8511.
                exact
                  Hex.reassemblePolynomialFactors_factor_irreducible_of_complete_and_core_irreducible
                    _ _
                    (reassemblyExpansionComplete_classicalCore_of_ne_zero
                      f hf primeData hsel hdeg hcore)
                    (classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible
                      f hf primeData hsel hdeg hcore)
                    hmem


end HexBerlekampZassenhausMathlib
