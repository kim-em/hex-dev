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

public import HexBerlekampZassenhausMathlib.SearchAssembly
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.SubsetCoprimality
import all HexBerlekampZassenhausMathlib.ForwardHenselTransport
import all HexBerlekampZassenhausMathlib.RecombinationMonic
import all HexBerlekampZassenhausMathlib.PrimitivityDegreeCover
import all HexBerlekampZassenhausMathlib.ScaledSearchCoverage
import all HexBerlekampZassenhausMathlib.SmartSearchCoverage
import all HexBerlekampZassenhausMathlib.SearchAssembly

public section
set_option backward.proofsInPublic true

/-!
This module collects the `ZPoly` scale/dilate helpers and the forward monic correspondent.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- **#5214 supporting bundle (HO-1 slow-path substrate).**

Bundled substrate package for the slow-path arm of the HO-1 capstone
`factorize_irreducible_of_nonUnit` (#4170).  The seven fields are exactly the
hypothesis set on the lifted-Hensel side consumed by the slow-path
exhaustive-branch irreducibility reasoning,
packaged so the capstone can obtain all of them from a single
`Hex.choosePrimeData? core = some primeData` witness together with monic /
positive-degree / square-free hypotheses on the core, without rediscovering
each fact independently.

* `corr` — `HenselSubsetCorrespondenceHypotheses` value (sourced from
  explicit successful correspondence evidence).
* `partition` — `LiftedFactorSubsetPartition core d Finset.univ core`
  covering / disjointness / recombination support (sourced from
  `liftedFactorSubsetPartition_of_choosePrimeData` with the same
  correspondence evidence).
* `liftedFactor_monic`, `liftedFactor_natDegree_pos`, `liftedFactor_inj` —
  per-lifted-factor monicness, positive transported natural degree,
  and `Function.Injective (liftedFactor d)`.
* `modulus`, `precision` — the Mignotte modulus and precision bounds
  `2 ≤ d.p ^ d.k` and `2 * B < d.p ^ d.k`.

The constructor below threads the witnesses through the existing
non-circular primitives in this file; no new analytic obligation is
introduced.  The recovered lifted-partition analytic content is exposed as the
`InitialLiftedFactorSubsetPartitionEvidence` argument. -/
structure SlowPathHenselSubstrate
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData) : Prop where
  corr :
    HenselSubsetCorrespondenceHypotheses core B primeData
      (Hex.ZPoly.toMonicLiftData core B primeData) True True
  partition :
    LiftedFactorSubsetPartition core
      (Hex.ZPoly.toMonicLiftData core B primeData) Finset.univ core
  liftedFactor_monic :
    ∀ i, Hex.DensePoly.Monic
      (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)
  liftedFactor_natDegree_pos :
    ∀ i,
      0 < (HexPolyZMathlib.toPolynomial
        (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData) i)).natDegree
  liftedFactor_inj :
    Function.Injective
      (liftedFactor (Hex.ZPoly.toMonicLiftData core B primeData))
  modulus :
    2 ≤ (Hex.ZPoly.toMonicLiftData core B primeData).p ^
      (Hex.ZPoly.toMonicLiftData core B primeData).k
  precision :
    2 * B < (Hex.ZPoly.toMonicLiftData core B primeData).p ^
      (Hex.ZPoly.toMonicLiftData core B primeData).k

/-- **#5214 supporting lemma (HO-1 slow-path substrate constructor).**

Constructor for `SlowPathHenselSubstrate` from a `Hex.choosePrimeData?
core = some primeData` witness together with monic, positive-degree, and
square-free hypotheses on the core, plus `B ≠ 0` and an explicit successful
Hensel subset correspondence package.

Composes (no new analytic obligation):

* `hcorr` for `corr`;
* `liftedFactorSubsetPartition_of_choosePrimeData` applied to `hcorr` for
  `partition`;
* the `_of_monicPrimeData` umbrellas
  (`Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData`,
  `..._natDegree_pos_of_monicPrimeData`,
  `..._injective_of_monicPrimeData`) for the lifted-factor monicness /
  natDegree positivity / injectivity facts.  The `Hex.choosePrimeData?
  core = some primeData` witness transports to `Hex.ZPoly.toMonicPrimeData?
  core = some primeData` via `(Hex.ZPoly.toMonic core).monic = core`
  on monic input (`Hex.ZPoly.toMonic_monic_eq_core_of_leadingCoeff_eq_one`);
* `Hex.precisionForCoeffBound_spec` for `precision`, refined to `modulus`
  via `B ≠ 0`. -/
theorem slowPathHenselSubstrate_of_choosePrimeData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne_zero : B ≠ 0)
    (hcorr :
      HenselSubsetCorrespondenceHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    SlowPathHenselSubstrate core B primeData := by
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    zpoly_lc_pos_of_monic hcore_monic
  have htoMonic_eq : (Hex.ZPoly.toMonic core).monic = core :=
    Hex.ZPoly.toMonic_monic_eq_core_of_leadingCoeff_eq_one core hcore_monic
  have hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData := by
    show Hex.choosePrimeData? (Hex.ZPoly.toMonic core).monic = some primeData
    rw [htoMonic_eq]
    exact hchoose
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hchoose
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hprec_spec :
      2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hmodulus :
      2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by
    omega
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
  · exact hcorr
  · exact liftedFactorSubsetPartition_of_choosePrimeData
      core B primeData hchoose hcorr hcore_sqfree hinitial
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact hmodulus
  · exact hprec_spec

/-- **#6354 supporting lemma (HO-1 slow-path substrate constructor).**

Successful-branch variant of `slowPathHenselSubstrate_of_choosePrimeData`.
When callers supply primitive lifted-side descent plus forward Hensel transport,
the `corr` field and the partition's embedded correspondence are built through
`henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success_descent`
instead of assuming a correspondence for arbitrary prime data.

The older substrate constructor now consumes explicit correspondence evidence;
this wrapper builds that evidence from the descent/forward-transport package. -/
theorem slowPathHenselSubstrate_of_choosePrimeData_success_descent
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hchoose : Hex.choosePrimeData? core = some primeData)
    (hcore_monic : Hex.DensePoly.Monic core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne_zero : B ≠ 0)
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
            hdescent.factor_count_eq S))
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    SlowPathHenselSubstrate core B primeData := by
  have hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core :=
    zpoly_lc_pos_of_monic hcore_monic
  have htoMonic_eq : (Hex.ZPoly.toMonic core).monic = core :=
    Hex.ZPoly.toMonic_monic_eq_core_of_leadingCoeff_eq_one core hcore_monic
  have hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData := by
    show Hex.choosePrimeData? (Hex.ZPoly.toMonic core).monic = some primeData
    rw [htoMonic_eq]
    exact hchoose
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.choosePrimeData?_prime core primeData hchoose
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hprec_spec :
      2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hmodulus :
      2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by
    omega
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
  · exact henselSubsetCorrespondenceHypotheses_of_choosePrimeData_success_descent
      core B primeData (zpoly_primitive_of_monic hcore_monic)
      (zpoly_lc_pos_of_monic hcore_monic) hcore_pos hchoose hdescent hlifted_of_modP
  · exact liftedFactorSubsetPartition_of_choosePrimeData_success_descent
      core B primeData (zpoly_primitive_of_monic hcore_monic)
      (zpoly_lc_pos_of_monic hcore_monic) hcore_pos hchoose hcore_sqfree hdescent
      hlifted_of_modP hinitial
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact hmodulus
  · exact hprec_spec

/-- **#6172 (HO-1 slow-path substrate constructor, non-monic-core sibling).**

Constructor for `SlowPathHenselSubstrate` from a
`Hex.ZPoly.toMonicPrimeData? core = some primeData` witness together with
positive-leading-coefficient, positive-degree, and square-free hypotheses
on the core, plus `B ≠ 0` and an explicit successful Hensel subset
correspondence package.  In contrast to
`slowPathHenselSubstrate_of_choosePrimeData`, this sibling does not
require `core` to be monic — the prime-data witness operates on the
integral-normalisation `(Hex.ZPoly.toMonic core).monic`, so non-monic
square-free cores (e.g. `(Hex.normalizeForFactor f).squareFreeCore`) can
feed the slow-path arm of #4170 directly.

Composes (no new analytic obligation; the recovered initial partition fields
come from the explicit `InitialLiftedFactorSubsetPartitionEvidence` argument):

* `hcorr` for `corr`;
* `liftedFactorSubsetPartition_of_toMonicPrimeData` applied to `hcorr` for
  `partition`;
* the `_of_monicPrimeData` umbrellas
  (`Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData`,
  `..._natDegree_pos_of_monicPrimeData`,
  `..._injective_of_monicPrimeData`) for the lifted-factor monicness /
  natDegree positivity / injectivity facts;
* `Hex.precisionForCoeffBound_spec` for `precision`, refined to `modulus`
  via `B ≠ 0`. -/
theorem slowPathHenselSubstrate_of_toMonicChoosePrimeData
    (core : Hex.ZPoly) (B : Nat)
    (primeData : Hex.PrimeChoiceData)
    (hselected : Hex.ZPoly.toMonicPrimeData? core = some primeData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_sqfree : Squarefree (HexPolyZMathlib.toPolynomial core))
    (hB_ne_zero : B ≠ 0)
    (hcorr :
      HenselSubsetCorrespondenceHypotheses core B primeData
        (Hex.ZPoly.toMonicLiftData core B primeData) True True)
    (hinitial :
      InitialLiftedFactorSubsetPartitionEvidence core
        (Hex.ZPoly.toMonicLiftData core B primeData)) :
    SlowPathHenselSubstrate core B primeData := by
  have hp_prime : Hex.Nat.Prime primeData.p :=
    Hex.ZPoly.toMonicPrimeData?_prime core primeData hselected
  have hp2 : 2 ≤ primeData.p := hp_prime.two_le
  have hprec_spec :
      2 * B < primeData.p ^ Hex.precisionForCoeffBound B primeData.p :=
    Hex.precisionForCoeffBound_spec hp2 B
  have hB1 : 1 ≤ B := Nat.one_le_iff_ne_zero.mpr hB_ne_zero
  have hmodulus :
      2 ≤ primeData.p ^ Hex.precisionForCoeffBound B primeData.p := by
    omega
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
  · exact hcorr
  · exact liftedFactorSubsetPartition_of_toMonicPrimeData
      core B primeData
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos)
      hcorr hcore_sqfree hinitial
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_monic_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_natDegree_pos_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact Hex.ZPoly.toMonicLiftData_liftedFactor_injective_of_monicPrimeData
      core B primeData hcore_lc_pos hcore_pos
      (modPFactorization_of_toMonicPrimeData hselected hcore_lc_pos hcore_pos) hprec_pos
  · exact hmodulus
  · exact hprec_spec

/-! ### Forward monic correspondent

`exists_monicCorrespondent_of_dvd` is the forward map from an integer factor of
`core` to a monic factor of `(toMonic core).monic`, the section of the
`primitivePart ∘ dilate` recovery map proved in `dilate_recovery`.

Sign note (the caveat #7365 flagged): `Hex.ZPoly.primitivePart` divides by the
*nonnegative* content but does **not** sign-normalize, so
`primitivePart (dilate lc g) = sign(lc)^(deg) * sign(lf) * factor`.  The
hypothesis `normalizeFactorSign factor = factor` only forces
`0 < leadingCoeff factor`; recovering exactly `factor` (rather than `-factor`)
additionally requires `0 < leadingCoeff core`, threaded here as `hlc`.  Without
it the statement is false, e.g. `core = -X^2 + 1`, `factor = X - 1`. -/

private theorem array_push_one_back?_ne_zero (xs : Array Int) :
    (xs.push 1).back? ≠ some (0 : Int) := by
  simp

private theorem zpoly_array_getD_toList (xs : Array Int) (i : Nat) (d : Int) :
    xs.getD i d = xs.toList.getD i d := by
  cases xs with
  | mk data =>
      rw [List.getD_eq_getElem?_getD]
      unfold Array.getD Array.size Array.getInternal
      by_cases hlt : i < data.length
      · rw [dif_pos hlt]
        simp [List.getElem?_eq_getElem hlt]
      · rw [dif_neg hlt]
        simp [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt hlt)]

/-- For a nonzero executable polynomial the defaulted degree is `size - 1`. -/
theorem degree?_getD_of_ne_zero (p : Hex.ZPoly) (hp : p ≠ 0) :
    p.degree?.getD 0 = p.size - 1 := by
  have hpos := Hex.ZPoly.size_pos_of_ne_zero p hp
  have hne : ¬ p.size = 0 := by omega
  simp [Hex.DensePoly.degree?, hne]

/-- Variable dilation by a nonzero factor is injective: the `n`-th coefficient is
multiplied by the unit power `c ^ n`. -/
theorem dilate_injective {c : Int} (hc : c ≠ 0) :
    Function.Injective (Hex.ZPoly.dilate c) := by
  intro p q h
  apply Hex.DensePoly.ext_coeff
  intro n
  have hn : (Hex.ZPoly.dilate c p).coeff n = (Hex.ZPoly.dilate c q).coeff n := by rw [h]
  rw [Hex.ZPoly.coeff_dilate, Hex.ZPoly.coeff_dilate] at hn
  exact mul_left_cancel₀ (pow_ne_zero n hc) hn

/-- Scalar multiplication by a nonzero integer is injective on `Hex.ZPoly`. -/
theorem scale_injective {c : Int} (hc : c ≠ 0) (p q : Hex.ZPoly)
    (h : Hex.DensePoly.scale c p = Hex.DensePoly.scale c q) : p = q := by
  apply Hex.DensePoly.ext_coeff
  intro n
  have hn : (Hex.DensePoly.scale c p).coeff n = (Hex.DensePoly.scale c q).coeff n := by rw [h]
  rw [Hex.DensePoly.coeff_scale (R := Int) c p n (Int.mul_zero c),
    Hex.DensePoly.coeff_scale (R := Int) c q n (Int.mul_zero c)] at hn
  exact mul_left_cancel₀ hc hn

/-- Scalar multiplications compose: `scale a (scale b p) = scale (a*b) p`. -/
theorem scale_scale (a b : Int) (p : Hex.ZPoly) :
    Hex.DensePoly.scale a (Hex.DensePoly.scale b p) = Hex.DensePoly.scale (a * b) p := by
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.DensePoly.coeff_scale (R := Int) a _ n (Int.mul_zero a),
    Hex.DensePoly.coeff_scale (R := Int) b p n (Int.mul_zero b),
    Hex.DensePoly.coeff_scale (R := Int) (a * b) p n (Int.mul_zero (a * b)),
    ← Int.mul_assoc]

/-- Scalar multiplications multiply through a product:
`scale a p * scale b q = scale (a*b) (p*q)`. -/
theorem scale_mul_scale (a b : Int) (p q : Hex.ZPoly) :
    Hex.DensePoly.scale a p * Hex.DensePoly.scale b q =
      Hex.DensePoly.scale (a * b) (p * q) := by
  rw [← Hex.ZPoly.C_mul_eq_scale, ← Hex.ZPoly.C_mul_eq_scale, ← Hex.ZPoly.C_mul_eq_scale]
  apply HexPolyZMathlib.equiv.injective
  simp only [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.toPolynomial_mul,
    HexPolyZMathlib.toPolynomial_C, Polynomial.C_mul]
  ring

/-- **Honest scale-coordinate congruence from a `monicTarget` subset correspondence**
(the algebraic core of deliverable (b) of #8319).

Given the per-support `monicTarget`-coordinate correspondence
`scale (leadingCoeff factor) (∏ S) ≡ factor (mod p^k)` — the selected lifted
product, rescaled to `factor`'s leading coefficient, lands on `factor` itself —
together with the leading-coefficient factorisation
`leadingCoeff core = leadingCoeff factor * cofactorLc`, the honest proportional
congruence `scale (leadingCoeff core) (∏ S) ≡ scale cofactorLc factor (mod p^k)`
follows by scaling the correspondence by `cofactorLc` and composing the two
scalings (`scale_scale`).  This is exactly the `hhonest` field that
`recoveredAtLiftM1_of_recovery` / `cutProjectionHypotheses_of_recoveryData`
consume per support.

The spurious constant `cofactorLc` is the cofactor's leading coefficient; it is
the `c` of the M1 recovery, stripped by `primitivePart` in `recovered_eq`.  This
lemma is the `dilate`-free, soundness-clean reduction: it leaves a *single*
remaining obligation — the correspondence hypothesis `hcorr`, i.e. the
Hensel-uniqueness subset recovery in the `monicTarget` coordinate, which the
`dilate`-coordinate `RecoveredAtLift` witness backing each true support does not
itself supply (the two coordinates diverge). -/
theorem honestCongr_of_correspondence
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (cofactorLc : Int)
    (hlc : Hex.DensePoly.leadingCoeff core
        = Hex.DensePoly.leadingCoeff factor * cofactorLc)
    (hcorr :
      Hex.ZPoly.congr
        (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff factor) (liftedFactorProduct d S))
        factor (d.p ^ d.k)) :
    Hex.ZPoly.congr
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core) (liftedFactorProduct d S))
      (Hex.DensePoly.scale cofactorLc factor)
      (d.p ^ d.k) := by
  have hscaled := scale_congr_of_congr cofactorLc _ _ _ hcorr
  rw [scale_scale] at hscaled
  rwa [show cofactorLc * Hex.DensePoly.leadingCoeff factor
        = Hex.DensePoly.leadingCoeff core by rw [hlc]; ring] at hscaled

/-- Turn a `monicTarget factor` subset congruence into the scale-coordinate
correspondence consumed by `honestCongr_of_correspondence`.

This is the per-factor specialization of the global M1 bridge
`scaledLiftedFactorProduct_congr_core_of_product_congr_monicTarget`: scaling the
selected lifted product by `leadingCoeff factor` recovers `factor` modulo the
Hensel modulus. -/
theorem factorCongr_of_product_congr_monicTarget
    {factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hprod :
      Hex.ZPoly.congr
        (liftedFactorProduct d S)
        (Hex.ZPoly.monicTarget factor d.p d.k)
        (d.p ^ d.k))
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff factor)
      (Int.ofNat (d.p ^ d.k)) = 1)
    (hpk : 1 < d.p ^ d.k) :
    Hex.ZPoly.congr
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff factor)
        (liftedFactorProduct d S))
      factor
      (d.p ^ d.k) := by
  simpa [scaledLiftedFactorProduct] using
    (scaledLiftedFactorProduct_congr_core_of_product_congr_monicTarget
      (core := factor) (d := d) (S := S) hpk hgcd hprod)

/-- Compose the per-factor `monicTarget` bridge with the honest M1
scale-coordinate wrapper.

Given the leading-coefficient split
`leadingCoeff core = leadingCoeff factor * cofactorLc`, a subset product
congruent to `monicTarget factor` yields the per-support honest congruence
`scale (leadingCoeff core) (∏ S) ≡ scale cofactorLc factor (mod p^k)`. -/
theorem honestCongr_of_product_congr_monicTarget
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (cofactorLc : Int)
    (hlc : Hex.DensePoly.leadingCoeff core
        = Hex.DensePoly.leadingCoeff factor * cofactorLc)
    (hprod :
      Hex.ZPoly.congr
        (liftedFactorProduct d S)
        (Hex.ZPoly.monicTarget factor d.p d.k)
        (d.p ^ d.k))
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff factor)
      (Int.ofNat (d.p ^ d.k)) = 1)
    (hpk : 1 < d.p ^ d.k) :
    Hex.ZPoly.congr
      (Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff core)
        (liftedFactorProduct d S))
      (Hex.DensePoly.scale cofactorLc factor)
      (d.p ^ d.k) :=
  honestCongr_of_correspondence cofactorLc hlc
    (factorCongr_of_product_congr_monicTarget hprod hgcd hpk)

/-- The monic dilation transform of `base` by `c`: coefficient `n` is
`c ^ (deg - n) * base.coeff n / leadingCoeff base` below the degree `deg`, and `1`
at `deg`.  When `leadingCoeff base ∣ c`, dilating this by `c` recovers a scalar
multiple of `base` (`dilate_monicDilate`); it is the monic correspondent of a
factor consumed by recombination recovery. -/
def Hex.ZPoly.monicDilate (c : Int) (base : Hex.ZPoly) : Hex.ZPoly where
  coeffs :=
    (((List.range (base.degree?.getD 0)).map
        (fun i => c ^ (base.degree?.getD 0 - i) * base.coeff i /
          Hex.DensePoly.leadingCoeff base)).toArray).push 1
  normalized := by
    right
    exact array_push_one_back?_ne_zero _

theorem monicDilate_monic (c : Int) (base : Hex.ZPoly) :
    Hex.DensePoly.Monic (Hex.ZPoly.monicDilate c base) := by
  unfold Hex.DensePoly.Monic Hex.DensePoly.leadingCoeff Hex.ZPoly.monicDilate
  simp

theorem monicDilate_coeff (c : Int) (base : Hex.ZPoly) (n : Nat) :
    (Hex.ZPoly.monicDilate c base).coeff n =
      if n < base.degree?.getD 0 then
        c ^ (base.degree?.getD 0 - n) * base.coeff n / Hex.DensePoly.leadingCoeff base
      else if n = base.degree?.getD 0 then 1 else 0 := by
  set deg := base.degree?.getD 0 with hdeg
  set L : List Int := (List.range deg).map
      (fun i => c ^ (deg - i) * base.coeff i / Hex.DensePoly.leadingCoeff base) with hL
  have hLlen : L.length = deg := by rw [hL]; simp
  have hcoeff : (Hex.ZPoly.monicDilate c base).coeff n = (L ++ [1]).getD n (0 : Int) := by
    show (L.toArray.push 1).getD n (0 : Int) = _
    rw [zpoly_array_getD_toList, Array.toList_push, List.toList_toArray]
  rw [hcoeff, List.getD_eq_getElem?_getD]
  rcases lt_trichotomy n deg with h | h | h
  · rw [if_pos h, List.getElem?_append_left (by rw [hLlen]; exact h), hL,
      List.getElem?_map, List.getElem?_range h]
    rfl
  · rw [if_neg (by omega), if_pos h,
      List.getElem?_append_right (by rw [hLlen]; omega), hLlen, h, Nat.sub_self]
    rfl
  · rw [if_neg (by omega), if_neg (by omega),
      List.getElem?_append_right (by rw [hLlen]; omega), hLlen,
      List.getElem?_eq_none (by simp; omega)]
    rfl

/-- Dilating the monic transform recovers a scalar multiple of `base`. -/
theorem dilate_monicDilate (c : Int) (base : Hex.ZPoly)
    (hbase : base ≠ 0) (hdeg : 1 ≤ base.degree?.getD 0)
    (hdvd : Hex.DensePoly.leadingCoeff base ∣ c) :
    Hex.ZPoly.dilate c (Hex.ZPoly.monicDilate c base) =
      Hex.DensePoly.scale (c ^ (base.degree?.getD 0) / Hex.DensePoly.leadingCoeff base) base := by
  set deg := base.degree?.getD 0 with hdegdef
  set lf := Hex.DensePoly.leadingCoeff base with hlfdef
  have hszpos := Hex.ZPoly.size_pos_of_ne_zero base hbase
  have hlf0 : lf ≠ 0 :=
    Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size base hszpos
  have hsize : base.size = deg + 1 := by
    have := degree?_getD_of_ne_zero base hbase
    rw [← hdegdef] at this
    omega
  have hcoeff_deg : base.coeff deg = lf := by
    rw [hlfdef, Hex.DensePoly.leadingCoeff_eq_coeff_last base hszpos, hsize,
      Nat.add_sub_cancel]
  have hcdeg : lf ∣ c ^ deg := dvd_pow hdvd (by omega)
  apply Hex.DensePoly.ext_coeff
  intro n
  rw [Hex.ZPoly.coeff_dilate, monicDilate_coeff,
    Hex.DensePoly.coeff_scale (R := Int) _ base n (Int.mul_zero _)]
  rw [← hdegdef, ← hlfdef]
  rcases lt_trichotomy n deg with h | h | h
  · rw [if_pos h]
    have hexp : lf ∣ c ^ (deg - n) := dvd_pow hdvd (by omega)
    obtain ⟨t, ht⟩ := hexp
    have hcn : c ^ deg = c ^ n * c ^ (deg - n) := by
      rw [← pow_add]
      congr 1
      omega
    have hdiv1 : c ^ (deg - n) * base.coeff n / lf = t * base.coeff n := by
      rw [ht, Int.mul_assoc, Int.mul_ediv_cancel_left _ hlf0]
    have hdiv2 : c ^ deg / lf = c ^ n * t := by
      have hcd : c ^ deg = lf * (c ^ n * t) := by rw [hcn, ht]; ring
      rw [hcd, Int.mul_ediv_cancel_left _ hlf0]
    rw [hdiv1, hdiv2]
    ring
  · rw [if_neg (by omega), if_pos h, h, hcoeff_deg,
      Int.ediv_mul_cancel hcdeg, Int.mul_one]
  · rw [if_neg (by omega), if_neg (by omega), Int.mul_zero]
    have : base.coeff n = 0 :=
      Hex.DensePoly.coeff_eq_zero_of_size_le base (by omega)
    rw [this, Int.mul_zero]

/-- **Forward monic correspondent.** For a primitive, sign-normalized integer
factor `factor` of a positive-leading-coefficient `core` of positive degree,
there is a monic factor `g` of `(toMonic core).monic` whose dilation by
`leadingCoeff core` has `factor` as its primitive part — the section of the
`dilate_recovery` map. -/
theorem exists_monicCorrespondent_of_dvd
    (core factor : Hex.ZPoly)
    (hcore0 : core ≠ 0)
    (hlc : 0 < Hex.DensePoly.leadingCoeff core)
    (hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree)
    (hfdeg : 1 ≤ factor.degree?.getD 0)
    (hdvd : factor ∣ core)
    (hfactor_prim : Hex.ZPoly.Primitive factor)
    (hfactor_norm : Hex.normalizeFactorSign factor = factor) :
    ∃ g : Hex.ZPoly,
      Hex.DensePoly.Monic g ∧
      g ∣ (Hex.ZPoly.toMonic core).monic ∧
      Hex.ZPoly.primitivePart
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) g) = factor := by
  classical
  obtain ⟨cof, hcof⟩ := hdvd
  set lc := Hex.DensePoly.leadingCoeff core with hlcdef
  set lf := Hex.DensePoly.leadingCoeff factor with hlfdef
  set lcof := Hex.DensePoly.leadingCoeff cof with hlcofdef
  set a := factor.degree?.getD 0 with hadef
  set b := cof.degree?.getD 0 with hbdef
  set d := (Hex.ZPoly.toMonic core).degree with hddef
  have hlc0 : lc ≠ 0 := ne_of_gt hlc
  have hf0 : factor ≠ 0 := by
    rintro rfl
    simp [hadef] at hfdeg
  have hcof0 : cof ≠ 0 := by
    rintro rfl
    apply hcore0
    apply HexPolyZMathlib.equiv.injective
    rw [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.equiv_apply, hcof,
      HexPolyZMathlib.toPolynomial_mul]
    simp
  -- leading coefficient multiplicativity
  have hlc_eq : lc = lf * lcof := by
    rw [hlcdef, hlfdef, hlcofdef, hcof]
    exact Hex.ZPoly.leadingCoeff_mul_of_nonzero factor cof hf0 hcof0
  -- positivity / divisibility of leading coefficients
  have hlf_pos : 0 < lf := by
    rcases lt_or_ge lf 0 with hneg | hpos
    · exfalso
      have hh := hfactor_norm
      unfold Hex.normalizeFactorSign at hh
      rw [if_pos (by rw [← hlfdef]; exact hneg)] at hh
      have hlead := congrArg Hex.DensePoly.leadingCoeff hh
      rw [Hex.ZPoly.leadingCoeff_scale_of_nonzero (-1) factor (by decide), ← hlfdef] at hlead
      omega
    · rcases lt_or_eq_of_le hpos with h | h
      · exact h
      · exact absurd h.symm (Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size factor
          (Hex.ZPoly.size_pos_of_ne_zero factor hf0))
  have hlf_dvd : lf ∣ lc := ⟨lcof, hlc_eq⟩
  have hlcof_dvd : lcof ∣ lc := ⟨lf, by rw [hlc_eq]; ring⟩
  -- degree additivity: a + b = d
  have hF0 : HexPolyZMathlib.toPolynomial factor ≠ 0 := by
    intro hz
    exact hf0 (HexPolyZMathlib.equiv.injective (by
      rw [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.equiv_apply, hz]; simp))
  have hCof0 : HexPolyZMathlib.toPolynomial cof ≠ 0 := by
    intro hz
    exact hcof0 (HexPolyZMathlib.equiv.injective (by
      rw [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.equiv_apply, hz]; simp))
  have hd_eq : d = core.degree?.getD 0 := by rw [hddef]; exact Hex.ZPoly.toMonic_degree core
  have hab : a + b = d := by
    have hcoreP : HexPolyZMathlib.toPolynomial core =
        HexPolyZMathlib.toPolynomial factor * HexPolyZMathlib.toPolynomial cof := by
      rw [hcof, HexPolyZMathlib.toPolynomial_mul]
    have hnd : (HexPolyZMathlib.toPolynomial core).natDegree =
        (HexPolyZMathlib.toPolynomial factor).natDegree +
          (HexPolyZMathlib.toPolynomial cof).natDegree := by
      rw [hcoreP, Polynomial.natDegree_mul hF0 hCof0]
    simp only [HexPolyMathlib.natDegree_toPolynomial] at hnd
    rw [← hadef, ← hbdef, ← hd_eq] at hnd
    omega
  -- the correspondent
  set g := Hex.ZPoly.monicDilate lc factor with hgdef
  have hg_monic : Hex.DensePoly.Monic g := monicDilate_monic lc factor
  have hdg : Hex.ZPoly.dilate lc g = Hex.DensePoly.scale (lc ^ a / lf) factor := by
    rw [hgdef]
    have := dilate_monicDilate lc factor hf0 hfdeg (by rw [← hlfdef]; exact hlf_dvd)
    rw [← hadef, ← hlfdef] at this
    exact this
  -- the scalar lc ^ a / lf is positive and pairs back with lf
  have hsg_mul : lf * (lc ^ a / lf) = lc ^ a := by
    have : lf ∣ lc ^ a := dvd_pow hlf_dvd (by omega)
    exact Int.mul_ediv_cancel' this
  have hsg_pos : 0 < lc ^ a / lf := by
    have hpa : 0 < lc ^ a := pow_pos hlc a
    nlinarith [hsg_mul, hlf_pos, hpa]
  -- primitive part of the dilation
  have hprim : Hex.ZPoly.primitivePart
      (Hex.ZPoly.dilate lc g) = factor := by
    rw [hdg]
    have hcontent : Hex.ZPoly.content (Hex.DensePoly.scale (lc ^ a / lf) factor) = lc ^ a / lf := by
      show Hex.DensePoly.content (Hex.DensePoly.scale (lc ^ a / lf) factor) = lc ^ a / lf
      rw [Hex.DensePoly.content_scale_int]
      have hcf1 : Hex.DensePoly.content factor = 1 := hfactor_prim
      rw [hcf1, Int.mul_one]
      exact Int.natAbs_of_nonneg (le_of_lt hsg_pos)
    have hmp := Hex.ZPoly.content_mul_primitivePart (Hex.DensePoly.scale (lc ^ a / lf) factor)
    rw [hcontent] at hmp
    have hppself : Hex.ZPoly.primitivePart factor = factor :=
      Hex.ZPoly.primitivePart_eq_self_of_primitive factor hfactor_prim
    -- hmp : scale (lc^a/lf) (primitivePart (scale (lc^a/lf) factor)) = scale (lc^a/lf) factor
    exact scale_injective (ne_of_gt hsg_pos) _ _ hmp
  -- divisibility g ∣ (toMonic core).monic
  have hkey : Hex.ZPoly.dilate lc (Hex.ZPoly.toMonic core).monic =
      Hex.DensePoly.scale (lc ^ (d - 1)) core := by
    have := Hex.ZPoly.dilate_monic_toMonic core hdeg
    rw [← hlcdef, ← hddef, Hex.ZPoly.C_mul_eq_scale] at this
    exact this
  have hdvdg : g ∣ (Hex.ZPoly.toMonic core).monic := by
    rcases Nat.eq_zero_or_pos b with hb0 | hbpos
    · -- cof is constant
      have hcofC : cof = Hex.DensePoly.C lcof := by
        apply Hex.DensePoly.ext_coeff
        intro n
        have hszcof : cof.size = 1 := by
          have := degree?_getD_of_ne_zero cof hcof0
          rw [← hbdef, hb0] at this
          have hpos := Hex.ZPoly.size_pos_of_ne_zero cof hcof0
          omega
        have hidx : cof.size - 1 = 0 := by omega
        have hc0 : cof.coeff 0 = lcof := by
          rw [hlcofdef, Hex.DensePoly.leadingCoeff_eq_coeff_last cof
            (Hex.ZPoly.size_pos_of_ne_zero cof hcof0), hidx]
        cases n with
        | zero =>
            rw [Hex.DensePoly.coeff_C, if_pos rfl, hc0]
        | succ m =>
            rw [Hex.DensePoly.coeff_C, if_neg (Nat.succ_ne_zero m)]
            exact Hex.DensePoly.coeff_eq_zero_of_size_le cof (by omega)
      have ha_eq : a = d := by omega
      have hcore_scale : core = Hex.DensePoly.scale lcof factor := by
        apply HexPolyZMathlib.equiv.injective
        rw [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.equiv_apply, hcof, hcofC,
          ← Hex.ZPoly.C_mul_eq_scale, HexPolyZMathlib.toPolynomial_mul,
          HexPolyZMathlib.toPolynomial_mul, HexPolyZMathlib.toPolynomial_C]
        ring
      have hsg_val : lc ^ a / lf = lc ^ (d - 1) * lcof := by
        have hlhs : lf * (lc ^ a / lf) = lc ^ a := hsg_mul
        have hrhs : lf * (lc ^ (d - 1) * lcof) = lc ^ a := by
          rw [ha_eq]
          have : lf * lcof = lc := hlc_eq.symm
          calc lf * (lc ^ (d - 1) * lcof)
              = (lf * lcof) * lc ^ (d - 1) := by ring
            _ = lc * lc ^ (d - 1) := by rw [this]
            _ = lc ^ d := by rw [← pow_succ']; congr 1; omega
        have := hlhs.trans hrhs.symm
        exact mul_left_cancel₀ (ne_of_gt hlf_pos) this
      have hgM : g = (Hex.ZPoly.toMonic core).monic := by
        apply dilate_injective hlc0
        rw [hdg, hkey, hsg_val, hcore_scale, scale_scale]
      rw [hgM]
      exact Hex.DensePoly.dvd_refl_poly _
    · -- cof has positive degree: build the cofactor correspondent
      set h := Hex.ZPoly.monicDilate lc cof with hhdef
      have hdh : Hex.ZPoly.dilate lc h = Hex.DensePoly.scale (lc ^ b / lcof) cof := by
        rw [hhdef]
        have := dilate_monicDilate lc cof hcof0 (by rw [← hbdef]; exact hbpos)
          (by rw [← hlcofdef]; exact hlcof_dvd)
        rw [← hbdef, ← hlcofdef] at this
        exact this
      have hsh_mul : lcof * (lc ^ b / lcof) = lc ^ b := by
        have : lcof ∣ lc ^ b := dvd_pow hlcof_dvd (by omega)
        exact Int.mul_ediv_cancel' this
      have hprod : (lc ^ a / lf) * (lc ^ b / lcof) = lc ^ (d - 1) := by
        have hkey2 : lc * ((lc ^ a / lf) * (lc ^ b / lcof)) = lc ^ d := by
          calc lc * ((lc ^ a / lf) * (lc ^ b / lcof))
              = (lf * lcof) * ((lc ^ a / lf) * (lc ^ b / lcof)) := by rw [← hlc_eq]
            _ = (lf * (lc ^ a / lf)) * (lcof * (lc ^ b / lcof)) := by ring
            _ = lc ^ a * lc ^ b := by rw [hsg_mul, hsh_mul]
            _ = lc ^ (a + b) := by rw [pow_add]
            _ = lc ^ d := by rw [hab]
        have hdd : lc ^ d = lc * lc ^ (d - 1) := by
          rw [← pow_succ']; congr 1; omega
        rw [hdd] at hkey2
        exact mul_left_cancel₀ hlc0 hkey2
      have hgh : g * h = (Hex.ZPoly.toMonic core).monic := by
        apply dilate_injective hlc0
        rw [HexPolyZMathlib.dilate_mul, hdg, hdh, scale_mul_scale, hprod, hkey, ← hcof]
      exact ⟨h, hgh.symm⟩
  exact ⟨g, hg_monic, hdvdg, hprim⟩

/-- **Recovery-map injectivity on monics.** The map `m ↦ primitivePart (dilate c m)`
is injective on monic polynomials for a nonzero scalar `c`.  This is the
uniqueness counterpart of `exists_monicCorrespondent_of_dvd`'s existence: it
pins a centred-lift monic factor against the monic correspondent of a
recombination candidate, both of which recover the same primitive integer
factor under `primitivePart ∘ dilate (leadingCoeff core)`. -/
theorem monic_eq_of_primitivePart_dilate_eq
    {c : Int} (hc : c ≠ 0) {m₁ m₂ : Hex.ZPoly}
    (hm₁ : Hex.DensePoly.Monic m₁) (hm₂ : Hex.DensePoly.Monic m₂)
    (h : Hex.ZPoly.primitivePart (Hex.ZPoly.dilate c m₁) =
         Hex.ZPoly.primitivePart (Hex.ZPoly.dilate c m₂)) :
    m₁ = m₂ := by
  -- The dilations of monic polynomials are nonzero (size preserved).
  have hdil_ne : ∀ m : Hex.ZPoly, Hex.DensePoly.Monic m →
      Hex.ZPoly.dilate c m ≠ 0 := by
    intro m hm hz
    have hsize : (Hex.ZPoly.dilate c m).size = m.size :=
      size_dilate_eq_of_monic_of_ne_zero hc hm
    rw [hz, Hex.DensePoly.size_zero] at hsize
    have := zpoly_size_pos_of_monic hm
    omega
  set pp := Hex.ZPoly.primitivePart (Hex.ZPoly.dilate c m₁) with hpp
  set K₁ := Hex.ZPoly.content (Hex.ZPoly.dilate c m₁) with hK₁
  set K₂ := Hex.ZPoly.content (Hex.ZPoly.dilate c m₂) with hK₂
  have hrec₁ : Hex.DensePoly.scale K₁ pp = Hex.ZPoly.dilate c m₁ :=
    Hex.ZPoly.content_mul_primitivePart _
  have hrec₂ : Hex.DensePoly.scale K₂ pp = Hex.ZPoly.dilate c m₂ := by
    rw [h]; exact Hex.ZPoly.content_mul_primitivePart _
  have hK₁_ne : K₁ ≠ 0 := HexPolyZMathlib.content_ne_zero _ (hdil_ne m₁ hm₁)
  have hK₂_ne : K₂ ≠ 0 := HexPolyZMathlib.content_ne_zero _ (hdil_ne m₂ hm₂)
  -- `pp` is nonzero with positive size, so its leading coefficient is nonzero.
  have hpp_size : pp.size = m₁.size := by
    have : (Hex.DensePoly.scale K₁ pp).size = m₁.size := by
      rw [hrec₁]; exact size_dilate_eq_of_monic_of_ne_zero hc hm₁
    rwa [Hex.ZPoly.scale_size_of_nonzero K₁ pp hK₁_ne] at this
  have hpp_lead_ne : Hex.DensePoly.leadingCoeff pp ≠ 0 :=
    Hex.DensePoly.leadingCoeff_ne_zero_of_pos_size pp
      (by rw [hpp_size]; exact zpoly_size_pos_of_monic hm₁)
  -- Sizes of `m₁`, `m₂` both equal `pp.size`, so the `c`-powers match.
  have hpp_size₂ : pp.size = m₂.size := by
    have : (Hex.DensePoly.scale K₂ pp).size = m₂.size := by
      rw [hrec₂]; exact size_dilate_eq_of_monic_of_ne_zero hc hm₂
    rwa [Hex.ZPoly.scale_size_of_nonzero K₂ pp hK₂_ne] at this
  have hsize_eq : m₁.size = m₂.size := hpp_size ▸ hpp_size₂
  -- Match leading coefficients to deduce `K₁ = K₂`.
  have hlc₁ : c ^ (m₁.size - 1) = K₁ * Hex.DensePoly.leadingCoeff pp := by
    rw [← leadingCoeff_dilate_of_monic hc hm₁, ← hrec₁,
      Hex.ZPoly.leadingCoeff_scale_of_nonzero K₁ pp hK₁_ne]
  have hlc₂ : c ^ (m₂.size - 1) = K₂ * Hex.DensePoly.leadingCoeff pp := by
    rw [← leadingCoeff_dilate_of_monic hc hm₂, ← hrec₂,
      Hex.ZPoly.leadingCoeff_scale_of_nonzero K₂ pp hK₂_ne]
  have hKeq : K₁ = K₂ := by
    have hpow : c ^ (m₁.size - 1) = c ^ (m₂.size - 1) := by rw [hsize_eq]
    rw [hlc₁, hlc₂] at hpow
    exact mul_right_cancel₀ hpp_lead_ne hpow
  -- Equal contents give equal dilations; injectivity of `dilate c` finishes.
  have hdil_eq : Hex.ZPoly.dilate c m₁ = Hex.ZPoly.dilate c m₂ := by
    rw [← hrec₁, ← hrec₂, hKeq]
  exact dilate_injective hc hdil_eq

/-- **Centred-lift divisibility from a recombination candidate.** If a monic
`cl` dilates (by `leadingCoeff core`) to a polynomial whose primitive part is a
primitive, sign-normalized integer factor `candidate` of `core` of positive
degree, then `cl` divides the monic transform `(toMonic core).monic`.

This is the soundness step behind the monic-lattice `RecoveredLift` family: the
selected lifted product's centred lift is exactly the monic correspondent of the
recombination candidate (`monic_eq_of_primitivePart_dilate_eq` pins it against
`exists_monicCorrespondent_of_dvd`'s witness), so the executable exact-division
witness `candidate ∣ core` transports to `cl ∣ (toMonic core).monic`. -/
theorem centeredLift_dvd_toMonic
    {core cl candidate : Hex.ZPoly}
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hcl_monic : Hex.DensePoly.Monic cl)
    (hcand_deg : 1 ≤ candidate.degree?.getD 0)
    (hrecover :
       Hex.ZPoly.primitivePart
         (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl) = candidate)
    (hcand_dvd : candidate ∣ core)
    (hcand_prim : Hex.ZPoly.Primitive candidate)
    (hcand_sign : Hex.normalizeFactorSign candidate = candidate) :
    cl ∣ (Hex.ZPoly.toMonic core).monic := by
  have hcore0 : core ≠ 0 := by
    intro h
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hcore_lc_pos
    exact lt_irrefl 0 hcore_lc_pos
  have hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree := by
    rw [Hex.ZPoly.toMonic_degree core]; omega
  obtain ⟨g, hg_monic, hg_dvd, hg_recover⟩ :=
    exists_monicCorrespondent_of_dvd core candidate hcore0 hcore_lc_pos hdeg
      hcand_deg hcand_dvd hcand_prim hcand_sign
  have hcl_eq_g : cl = g :=
    monic_eq_of_primitivePart_dilate_eq (ne_of_gt hcore_lc_pos) hcl_monic hg_monic
      (hrecover.trans hg_recover.symm)
  rw [hcl_eq_g]; exact hg_dvd

/-- For a monic `cl` and positive scalar `c`, the leading-coefficient dilation
`dilate c cl` has positive leading coefficient `c ^ (cl.size - 1)`, and so does
its primitive part (the content is positive). -/
theorem leadingCoeff_primitivePart_dilate_pos {c : Int} (hc : 0 < c)
    {cl : Hex.ZPoly} (hcl : Hex.DensePoly.Monic cl) :
    0 < Hex.DensePoly.leadingCoeff
      (Hex.ZPoly.primitivePart (Hex.ZPoly.dilate c cl)) := by
  set x := Hex.ZPoly.dilate c cl with hx
  have hc_ne : c ≠ 0 := ne_of_gt hc
  have hx_lead_pos : 0 < Hex.DensePoly.leadingCoeff x := by
    rw [hx, leadingCoeff_dilate_of_monic hc_ne hcl]; exact pow_pos hc _
  have hx0 : x ≠ 0 := by
    intro hz
    rw [hz, Hex.DensePoly.leadingCoeff_zero] at hx_lead_pos
    exact lt_irrefl 0 hx_lead_pos
  set K := Hex.ZPoly.content x with hK
  have hK_ne : K ≠ 0 := HexPolyZMathlib.content_ne_zero _ hx0
  have hK_nonneg : 0 ≤ K := by
    rw [hK]; unfold Hex.ZPoly.content Hex.DensePoly.content; exact Int.natCast_nonneg _
  have hK_pos : 0 < K := lt_of_le_of_ne hK_nonneg (Ne.symm hK_ne)
  have hcmpp : Hex.DensePoly.scale K (Hex.ZPoly.primitivePart x) = x :=
    Hex.ZPoly.content_mul_primitivePart x
  have hlead_eq :
      Hex.DensePoly.leadingCoeff x =
        K * Hex.DensePoly.leadingCoeff (Hex.ZPoly.primitivePart x) := by
    have := Hex.ZPoly.leadingCoeff_scale_of_nonzero K (Hex.ZPoly.primitivePart x) hK_ne
    rw [hcmpp] at this; exact this
  rcases lt_trichotomy (Hex.DensePoly.leadingCoeff (Hex.ZPoly.primitivePart x)) 0 with
    hneg | hzero | hpos
  · exact absurd hx_lead_pos
      (by rw [hlead_eq]; have := mul_neg_of_pos_of_neg hK_pos hneg; linarith)
  · rw [hzero, Int.mul_zero] at hlead_eq
    rw [hlead_eq] at hx_lead_pos; exact absurd hx_lead_pos (lt_irrefl 0)
  · exact hpos

/-- The recombination candidate emitted by `bhksIndicatorCandidate?` over a
positive-leading-coefficient `core` is exactly the primitive part of the
leading-coefficient dilation of the centred selected product: the
`normalizeCandidateFactor`/`normalizeFactorSign` wrappers collapse because that
dilation already has positive leading coefficient. -/
theorem primitivePart_dilate_centeredLift_eq_candidate
    {core : Hex.ZPoly} {d : Hex.LiftData} {indicator : Array Int}
    {candidate quotient : Hex.ZPoly} {selected : Array Hex.ZPoly}
    (h : Hex.bhksIndicatorCandidate? core d indicator = some (candidate, quotient))
    (hselected :
       Hex.bhksIndicatorSelectedFactors d.liftedFactors indicator = some selected)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcl_monic :
       Hex.DensePoly.Monic
         (Hex.centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k))) :
    Hex.ZPoly.primitivePart
        (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
          (Hex.centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k))) = candidate := by
  set cl := Hex.centeredLiftPoly (Array.polyProduct selected) (d.p ^ d.k) with hcl
  set x := Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) cl with hx
  have hpp_lead_pos :
      0 < Hex.DensePoly.leadingCoeff (Hex.ZPoly.primitivePart x) :=
    leadingCoeff_primitivePart_dilate_pos hcore_lc_pos hcl_monic
  have hchar := Hex.bhksIndicatorCandidate?_eq_normalized_dilatedCenteredLift h hselected
  have hcond : ¬ Hex.DensePoly.leadingCoeff (Hex.ZPoly.primitivePart x) < 0 :=
    not_lt.mpr (le_of_lt hpp_lead_pos)
  have hnc : Hex.normalizeCandidateFactor x = Hex.ZPoly.primitivePart x := by
    unfold Hex.normalizeCandidateFactor; simp [hcond]
  have hns :
      Hex.normalizeFactorSign (Hex.ZPoly.primitivePart x) = Hex.ZPoly.primitivePart x := by
    unfold Hex.normalizeFactorSign; simp [hcond]
  rw [hchar, hnc, hns]

/-- **Mod-`p` representation of the monic correspondent (#7381, prereq of #7364).**

For prime data selected by `toMonicPrimeData? core` — that is, `choosePrimeData?`
applied to `M := (toMonic core).monic` — any irreducible integer divisor `g`
of `M` has a representing subset of `M`'s recorded mod-`p` factors. This
discharges the `hrepP` input of `henselLiftData_represents_lifted_of_modP`
(instantiated at `core := M`, `factor := g`) for the monic-correspondent arm
of the `toMonicLiftData` forward transport.

The representation is read off **directly** from the `toMonicPrimeData?`
partition, which already ranges over `M`'s mod-`p` factors via
`modPSubsetPartitionHypotheses_of_choosePrimeData`; it is *not* transported from
a representation of the original-core divisor. The correspondent `g` and its
non-monic preimage differ by a dilation `X ↦ (leadingCoeff core)·X`, and
`monicModPImage` is not dilation-invariant (the transport equality
`monicModPImage (modP p factor) = monicModPImage (modP p g)` was refuted in
\#7366). Consequently `g`'s representing subset is its own, so the sound
conclusion is existential — there is no representation at a subset prescribed
by the preimage. -/
theorem representsModP_correspondent
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    {g : Hex.ZPoly}
    (hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g))
    (hg_dvd : g ∣ (Hex.ZPoly.toMonic core).monic) :
    ∃ S : ModPFactorSubset primeData, RepresentsIntegerFactorModP primeData g S := by
  have hmonic_pos : 0 < (Hex.ZPoly.toMonic core).monic.degree?.getD 0 := by
    rw [Hex.ZPoly.toMonic_monic_degree_eq_of_pos_degree core hcore_lc_pos hcore_pos]
    exact hcore_pos
  exact (modPSubsetPartitionHypotheses_of_modPFactorization
    (Hex.ZPoly.toMonic core).monic primeData hmonic_pos hval).exists_subset
    hg_irr hg_dvd

/-- **Irreducibility iff across the recovery dilation.**

An integer factor `factor` recovered from a monic `g` by
`primitivePart (dilate lc g) = factor` (with `lc ≠ 0`) is irreducible over `ℤ[X]`
exactly when `g` is.  The two differ by the variable dilation `X ↦ lc · X`
followed by taking the primitive part.

Over `ℚ`, composition with `C lc * X` is the algebra automorphism
`algEquivCMulXAddC lc 0`, so it preserves irreducibility; the residual content
scalar is a unit; and Gauss's lemma (`IsPrimitive.Int.irreducible_iff_irreducible_map_cast`)
moves both `g` (monic, hence primitive) and `factor` between `ℤ[X]` and `ℚ[X]`. -/
theorem irreducible_toPolynomial_dilate_iff
    {factor g : Hex.ZPoly} {lc : Int}
    (hlc : lc ≠ 0)
    (hg_monic : Hex.DensePoly.Monic g)
    (hfactor_prim : Hex.ZPoly.Primitive factor)
    (hrecover :
      Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc g) = factor) :
    Irreducible (HexPolyZMathlib.toPolynomial factor) ↔
      Irreducible (HexPolyZMathlib.toPolynomial g) := by
  classical
  set G := HexPolyZMathlib.toPolynomial g with hGdef
  set F := HexPolyZMathlib.toPolynomial factor with hFdef
  have hG_monic : G.Monic :=
    HexHenselMathlib.toPolynomial_monic_of_dense_monic g hg_monic
  have hG_prim : G.IsPrimitive := hG_monic.isPrimitive
  have hF_prim : F.IsPrimitive :=
    HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive factor hfactor_prim
  -- The variable dilation `X ↦ lc · X` embeds to composition with `C lc * X`.
  have hcomp :
      HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc g)
        = G.comp (Polynomial.C lc * Polynomial.X) := by
    rw [hGdef]; exact HexPolyZMathlib.toPolynomial_dilate lc g
  -- The dilation is nonzero, so its content is nonzero.
  have hG0 : G ≠ 0 := hG_monic.ne_zero
  have hDpoly0 : G.comp (Polynomial.C lc * Polynomial.X) ≠ 0 := by
    rw [Ne, Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hlc)]
    exact hG0
  have hD0 : Hex.ZPoly.dilate lc g ≠ 0 := fun hz =>
    hDpoly0 (by rw [← hcomp, hz, HexPolyZMathlib.toPolynomial_zero])
  set c := Hex.ZPoly.content (Hex.ZPoly.dilate lc g) with hcdef
  have hc0 : c ≠ 0 := HexPolyZMathlib.content_ne_zero _ hD0
  -- Content/primitive-part decomposition with `primitivePart (dilate lc g) = factor`.
  have hCF :
      HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc g)
        = Polynomial.C c * F := by
    rw [HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart, hrecover, ← hFdef, ← hcdef]
  have hkey : G.comp (Polynomial.C lc * Polynomial.X) = Polynomial.C c * F :=
    hcomp.symm.trans hCF
  -- Move to `ℚ[X]` via Gauss's lemma.
  rw [Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hF_prim,
    Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast hG_prim]
  set cast := Int.castRingHom ℚ with hcast
  have hkeyQ :
      (G.map cast).comp (Polynomial.C (cast lc) * Polynomial.X)
        = Polynomial.C (cast c) * (F.map cast) := by
    have h := congrArg (Polynomial.map cast) hkey
    rwa [Polynomial.map_comp, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
      Polynomial.map_mul, Polynomial.map_C] at h
  have hca : cast lc ≠ 0 := by rw [eq_intCast cast lc]; exact_mod_cast hlc
  have hcc : cast c ≠ 0 := by rw [eq_intCast cast c]; exact_mod_cast hc0
  letI : Invertible (cast lc) := invertibleOfNonzero hca
  -- Over `ℚ`, composition with `C lc * X` is an algebra automorphism.
  have he : (algEquivCMulXAddC (cast lc) (0 : ℚ)) (G.map cast)
      = (G.map cast).comp (Polynomial.C (cast lc) * Polynomial.X) := by
    rw [algEquivCMulXAddC_apply, ← Polynomial.comp_eq_aeval]; simp
  have hiff := MulEquiv.irreducible_iff (algEquivCMulXAddC (cast lc) (0 : ℚ)) (x := G.map cast)
  rw [he, hkeyQ,
    irreducible_isUnit_mul (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcc))] at hiff
  exact hiff

/-- **Irreducibility of the monic correspondent.**

The monic correspondent `g` of an irreducible primitive integer factor `factor`
is itself irreducible.  The two differ by the variable dilation `X ↦ lc · X`
(with `lc := leadingCoeff core ≠ 0`) followed by taking the primitive part:
`primitivePart (dilate lc g) = factor`. -/
theorem irreducible_toPolynomial_monicCorrespondent
    {factor g : Hex.ZPoly} {lc : Int}
    (hlc : lc ≠ 0)
    (hg_monic : Hex.DensePoly.Monic g)
    (hfactor_prim : Hex.ZPoly.Primitive factor)
    (hfactor_irr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hrecover :
      Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc g) = factor) :
    Irreducible (HexPolyZMathlib.toPolynomial g) :=
  (irreducible_toPolynomial_dilate_iff hlc hg_monic hfactor_prim hrecover).mp hfactor_irr

/-- **Inverse monic correspondent.** For a primitive `core` with positive leading
coefficient and positive degree, every monic irreducible factor `g` of
`(toMonic core).monic` descends to an irreducible, sign-normalized integer factor
`f := primitivePart (dilate (leadingCoeff core) g)` of `core`.  This is the
inverse of `exists_monicCorrespondent_of_dvd`, gating the `cover` field of #7362.

`f ∣ core` is read off the keystone `dilate lc M = scale (lc^(d-1)) core`
(`dilate_monic_toMonic`): writing `g ∣ M` as `M = g * cof` with `cof` monic and
dilating, `scale (lc^(d-1)) core` factors as `scale (cg * ccof) (f * f₂)` over the
primitive parts `f`, `f₂` of the two dilations; stripping the (positive) content
scalars from both sides via Gauss gives `core = f * f₂`.  Irreducibility transfers
through `irreducible_toPolynomial_dilate_iff`; `normalizeFactorSign f = f` from the
positive leading coefficient of the dilation. -/
theorem exists_dvd_core_of_dvd_toMonic
    (core g : Hex.ZPoly)
    (hcore_lc_pos : 0 < Hex.DensePoly.leadingCoeff core) (hcore_pos : 0 < core.degree?.getD 0)
    (hcore_prim : Hex.ZPoly.Primitive core)
    (hg_monic : Hex.DensePoly.Monic g)
    (hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g))
    (hg_dvd : g ∣ (Hex.ZPoly.toMonic core).monic) :
    ∃ f : Hex.ZPoly,
      Irreducible (HexPolyZMathlib.toPolynomial f) ∧ f ∣ core ∧
      Hex.normalizeFactorSign f = f ∧
      Hex.ZPoly.primitivePart (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) g) = f := by
  classical
  set lc := Hex.DensePoly.leadingCoeff core with hlc_def
  have hlc_ne : lc ≠ 0 := ne_of_gt hcore_lc_pos
  set M := (Hex.ZPoly.toMonic core).monic with hMdef
  set d := (Hex.ZPoly.toMonic core).degree with hddef
  have hd_eq : d = core.degree?.getD 0 := by rw [hddef]; exact Hex.ZPoly.toMonic_degree core
  have hdeg : 1 ≤ d := by rw [hd_eq]; omega
  -- content is nonnegative
  have hcontent_nonneg : ∀ x : Hex.ZPoly, 0 ≤ Hex.ZPoly.content x := by
    intro x; unfold Hex.ZPoly.content Hex.DensePoly.content; exact Int.natCast_nonneg _
  -- `primitivePart` strips a positive content scalar from a primitive polynomial
  have hpp_scale : ∀ (s : Int) (p : Hex.ZPoly), 0 < s → Hex.ZPoly.Primitive p →
      Hex.ZPoly.primitivePart (Hex.DensePoly.scale s p) = p := by
    intro s p hs hp
    have hcontent : Hex.ZPoly.content (Hex.DensePoly.scale s p) = s := by
      show Hex.DensePoly.content (Hex.DensePoly.scale s p) = s
      rw [Hex.DensePoly.content_scale_int]
      have hp1 : Hex.DensePoly.content p = 1 := hp
      rw [hp1, Int.mul_one]
      exact Int.natAbs_of_nonneg (le_of_lt hs)
    have hmp := Hex.ZPoly.content_mul_primitivePart (Hex.DensePoly.scale s p)
    rw [hcontent] at hmp
    exact scale_injective (ne_of_gt hs) _ _ hmp
  -- the inverse correspondent `f` and the leading coefficient of its dilation
  have hgsize_pos : 0 < g.size := zpoly_size_pos_of_monic hg_monic
  have hg0 : g ≠ 0 := by
    intro h; rw [h, Hex.DensePoly.size_zero] at hgsize_pos; exact lt_irrefl 0 hgsize_pos
  have hg_lead : g.coeff (g.size - 1) = 1 := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last g hgsize_pos]; exact hg_monic
  have hsize_dil : (Hex.ZPoly.dilate lc g).size = g.size :=
    size_dilate_eq_of_monic_of_ne_zero hlc_ne hg_monic
  have hdil_lead : Hex.DensePoly.leadingCoeff (Hex.ZPoly.dilate lc g) = lc ^ (g.size - 1) := by
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last (Hex.ZPoly.dilate lc g)
        (by rw [hsize_dil]; exact hgsize_pos),
      hsize_dil, Hex.ZPoly.coeff_dilate, hg_lead, Int.mul_one]
  have hdil_lead_pos : 0 < Hex.DensePoly.leadingCoeff (Hex.ZPoly.dilate lc g) := by
    rw [hdil_lead]; exact pow_pos hcore_lc_pos _
  have hdil0 : Hex.ZPoly.dilate lc g ≠ 0 := by
    intro h
    rw [h, Hex.DensePoly.leadingCoeff_zero] at hdil_lead_pos
    exact lt_irrefl 0 hdil_lead_pos
  set cg := Hex.ZPoly.content (Hex.ZPoly.dilate lc g) with hcg_def
  have hcg_ne : cg ≠ 0 := by rw [hcg_def]; exact HexPolyZMathlib.content_ne_zero _ hdil0
  have hcg_pos : 0 < cg := lt_of_le_of_ne (hcontent_nonneg _) (Ne.symm hcg_ne)
  set f := Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc g) with hf
  have hf_prim : Hex.ZPoly.Primitive f := by
    rw [hf]; exact Hex.ZPoly.primitivePart_primitive _ (hcg_def ▸ hcg_ne)
  have hcmpp_g : Hex.DensePoly.scale cg f = Hex.ZPoly.dilate lc g := by
    rw [hcg_def, hf]; exact Hex.ZPoly.content_mul_primitivePart (Hex.ZPoly.dilate lc g)
  have hlc_f :
      Hex.DensePoly.leadingCoeff (Hex.ZPoly.dilate lc g) = cg * Hex.DensePoly.leadingCoeff f := by
    have h := Hex.ZPoly.leadingCoeff_scale_of_nonzero cg f hcg_ne
    rw [hcmpp_g] at h; exact h
  have hprod_pos : 0 < cg * Hex.DensePoly.leadingCoeff f := by rw [← hlc_f]; exact hdil_lead_pos
  have hlcf_pos : 0 < Hex.DensePoly.leadingCoeff f := by
    rcases lt_trichotomy (Hex.DensePoly.leadingCoeff f) 0 with h | h | h
    · exact absurd hprod_pos (by have := mul_neg_of_pos_of_neg hcg_pos h; linarith)
    · rw [h, Int.mul_zero] at hprod_pos; exact absurd hprod_pos (lt_irrefl 0)
    · exact h
  have hsign : Hex.normalizeFactorSign f = f := by
    unfold Hex.normalizeFactorSign
    rw [if_neg (not_lt.mpr (le_of_lt hlcf_pos))]
  have hf_irr : Irreducible (HexPolyZMathlib.toPolynomial f) :=
    (irreducible_toPolynomial_dilate_iff hlc_ne hg_monic hf_prim hf.symm).mpr hg_irr
  refine ⟨f, hf_irr, ?_, hsign, rfl⟩
  -- divisibility `f ∣ core`, via the keystone and the cofactor's dilation
  obtain ⟨cof, hcof⟩ := hg_dvd
  have hM_lead : Hex.DensePoly.leadingCoeff M = 1 := by
    rw [hMdef]; exact Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hcore_lc_pos hcore_pos
  have hM0 : M ≠ 0 := by
    intro h; rw [h, Hex.DensePoly.leadingCoeff_zero] at hM_lead; exact one_ne_zero hM_lead.symm
  have hcof0 : cof ≠ 0 := by
    rintro rfl
    apply hM0
    apply HexPolyZMathlib.equiv.injective
    rw [HexPolyZMathlib.equiv_apply, HexPolyZMathlib.equiv_apply, hcof,
      HexPolyZMathlib.toPolynomial_mul]
    simp
  have hcof_lead : Hex.DensePoly.leadingCoeff cof = 1 := by
    have h := Hex.ZPoly.leadingCoeff_mul_of_nonzero g cof hg0 hcof0
    rw [← hcof, hM_lead] at h
    have hg1 : Hex.DensePoly.leadingCoeff g = 1 := hg_monic
    rw [hg1, Int.one_mul] at h
    exact h.symm
  have hcof_monic : Hex.DensePoly.Monic cof := hcof_lead
  have hcofsize_pos : 0 < cof.size := zpoly_size_pos_of_monic hcof_monic
  have hcof_top : cof.coeff (cof.size - 1) = 1 := by
    rw [← Hex.DensePoly.leadingCoeff_eq_coeff_last cof hcofsize_pos]; exact hcof_monic
  have hsize_dilc : (Hex.ZPoly.dilate lc cof).size = cof.size :=
    size_dilate_eq_of_monic_of_ne_zero hlc_ne hcof_monic
  have hdilc_lead :
      Hex.DensePoly.leadingCoeff (Hex.ZPoly.dilate lc cof) = lc ^ (cof.size - 1) := by
    rw [Hex.DensePoly.leadingCoeff_eq_coeff_last (Hex.ZPoly.dilate lc cof)
        (by rw [hsize_dilc]; exact hcofsize_pos),
      hsize_dilc, Hex.ZPoly.coeff_dilate, hcof_top, Int.mul_one]
  have hdilc0 : Hex.ZPoly.dilate lc cof ≠ 0 := by
    intro h
    have hz : Hex.DensePoly.leadingCoeff (Hex.ZPoly.dilate lc cof) = 0 := by
      rw [h, Hex.DensePoly.leadingCoeff_zero]
    rw [hdilc_lead] at hz
    exact (pow_ne_zero _ hlc_ne) hz
  set ccof := Hex.ZPoly.content (Hex.ZPoly.dilate lc cof) with hccof_def
  have hccof_ne : ccof ≠ 0 := by rw [hccof_def]; exact HexPolyZMathlib.content_ne_zero _ hdilc0
  have hccof_pos : 0 < ccof := lt_of_le_of_ne (hcontent_nonneg _) (Ne.symm hccof_ne)
  set pcof := Hex.ZPoly.primitivePart (Hex.ZPoly.dilate lc cof) with hpcof
  have hpcof_prim : Hex.ZPoly.Primitive pcof := by
    rw [hpcof]; exact Hex.ZPoly.primitivePart_primitive _ (hccof_def ▸ hccof_ne)
  have hcmpp_c : Hex.DensePoly.scale ccof pcof = Hex.ZPoly.dilate lc cof := by
    rw [hccof_def, hpcof]; exact Hex.ZPoly.content_mul_primitivePart (Hex.ZPoly.dilate lc cof)
  have hkey : Hex.ZPoly.dilate lc M = Hex.DensePoly.scale (lc ^ (d - 1)) core := by
    have h := Hex.ZPoly.dilate_monic_toMonic core hdeg
    rw [← hlc_def, ← hMdef, ← hddef, Hex.ZPoly.C_mul_eq_scale] at h
    exact h
  have hdil_M :
      Hex.ZPoly.dilate lc M = Hex.ZPoly.dilate lc g * Hex.ZPoly.dilate lc cof := by
    rw [hcof, HexPolyZMathlib.dilate_mul]
  have heq1 :
      Hex.DensePoly.scale (lc ^ (d - 1)) core = Hex.DensePoly.scale (cg * ccof) (f * pcof) := by
    rw [← hkey, hdil_M, ← hcmpp_g, ← hcmpp_c, scale_mul_scale]
  have hff_prim : Hex.ZPoly.Primitive (f * pcof) :=
    Hex.ZPoly.primitive_mul f pcof hf_prim hpcof_prim
  have hcore_eq : core = f * pcof := by
    rw [← hpp_scale (lc ^ (d - 1)) core (pow_pos hcore_lc_pos _) hcore_prim, heq1,
      hpp_scale (cg * ccof) (f * pcof) (mul_pos hcg_pos hccof_pos) hff_prim]
  exact ⟨pcof, hcore_eq⟩

/-- **Association reflection through the primitive content factor.**

Two primitive integer polynomials whose constant multiples `C a * F`, `C b * G`
(`a, b ≠ 0`) are associated are themselves associated. Each primitive factor
divides its own multiple, hence the other multiple; the spurious content scalar
survives only inside `primPart (C · * ·)`, where `isUnit_primPart_C` strips it
(via `IsPrimitive.dvd_primPart_iff_dvd`), leaving divisibility both ways. -/
private theorem associated_of_C_mul_associated
    {F G : Polynomial ℤ} {a b : ℤ}
    (hF : F.IsPrimitive) (hG : G.IsPrimitive) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : Associated (Polynomial.C a * F) (Polynomial.C b * G)) :
    Associated F G := by
  have hF0 : F ≠ 0 := hF.ne_zero
  have hG0 : G ≠ 0 := hG.ne_zero
  have hCaF0 : Polynomial.C a * F ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr ha) hF0
  have hCbG0 : Polynomial.C b * G ≠ 0 := mul_ne_zero (Polynomial.C_ne_zero.mpr hb) hG0
  have hFG : F ∣ G := by
    have hFdvd : F ∣ Polynomial.C b * G :=
      (dvd_mul_left F (Polynomial.C a)).trans h.dvd
    rw [← hF.dvd_primPart_iff_dvd hG0]
    have hpp := (hF.dvd_primPart_iff_dvd hCbG0).mpr hFdvd
    rw [Polynomial.primPart_mul hCbG0] at hpp
    exact ((Polynomial.isUnit_primPart_C b).dvd_mul_left).mp hpp
  have hGF : G ∣ F := by
    have hGdvd : G ∣ Polynomial.C a * F :=
      (dvd_mul_left G (Polynomial.C b)).trans h.symm.dvd
    rw [← hG.dvd_primPart_iff_dvd hF0]
    have hpp := (hG.dvd_primPart_iff_dvd hCaF0).mpr hGdvd
    rw [Polynomial.primPart_mul hCaF0] at hpp
    exact ((Polynomial.isUnit_primPart_C a).dvd_mul_left).mp hpp
  exact associated_of_dvd_dvd hFG hGF

/-- **Correspondent association reflection.**

If the monic correspondents `gf`, `gg` of two factors have associated integer
images, then so do the factors `f`, `g` recovered from them by the variable
dilation `X ↦ (leadingCoeff core)·X` followed by taking the primitive part.

Used contrapositively for #7362's `pairwise_disjoint`: distinct deterministic
recoveries `¬Associated f g` force the monic correspondents apart
(`¬Associated gf gg`). The dilation embeds (`toPolynomial_dilate`) to
composition with `C lc * X`, a monoid endomorphism that transports the
association; the residual content scalars are stripped by
`associated_of_C_mul_associated`, since each recovered `f`, `g` is the primitive
part of a nonzero dilation, hence primitive. -/
theorem associated_of_associated_monicCorrespondent
    {core f g gf gg : Hex.ZPoly}
    (hlc : Hex.DensePoly.leadingCoeff core ≠ 0)
    (hgf : gf ≠ 0) (hgg : gg ≠ 0)
    (hf : Hex.ZPoly.primitivePart
            (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) gf) = f)
    (hg : Hex.ZPoly.primitivePart
            (Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core) gg) = g)
    (hassoc : Associated (HexPolyZMathlib.toPolynomial gf)
                (HexPolyZMathlib.toPolynomial gg)) :
    Associated (HexPolyZMathlib.toPolynomial f)
      (HexPolyZMathlib.toPolynomial g) := by
  classical
  set lc := Hex.DensePoly.leadingCoeff core with hlcdef
  -- The dilation `X ↦ lc·X` reflects nonvanishing through its nonzero-divisor
  -- leading factor, so both dilations are nonzero.
  have hdilate0 : ∀ {p : Hex.ZPoly}, p ≠ 0 → Hex.ZPoly.dilate lc p ≠ 0 := by
    intro p hp hz
    apply hp
    have h1 : (HexPolyZMathlib.toPolynomial p).comp
                (Polynomial.C lc * Polynomial.X) = 0 := by
      rw [← HexPolyZMathlib.toPolynomial_dilate, hz, HexPolyZMathlib.toPolynomial_zero]
    rw [Polynomial.comp_C_mul_X_eq_zero_iff (mem_nonZeroDivisors_of_ne_zero hlc)] at h1
    rw [← HexPolyZMathlib.ofPolynomial_toPolynomial p, h1, HexPolyZMathlib.ofPolynomial_zero]
  have hdf0 : Hex.ZPoly.dilate lc gf ≠ 0 := hdilate0 hgf
  have hdg0 : Hex.ZPoly.dilate lc gg ≠ 0 := hdilate0 hgg
  -- `f`, `g` are primitive parts of nonzero dilations, hence primitive.
  have hFprim : (HexPolyZMathlib.toPolynomial f).IsPrimitive := by
    rw [← hf]
    exact HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive _
      (Hex.ZPoly.primitivePart_primitive _ (HexPolyZMathlib.content_ne_zero _ hdf0))
  have hGprim : (HexPolyZMathlib.toPolynomial g).IsPrimitive := by
    rw [← hg]
    exact HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive _
      (Hex.ZPoly.primitivePart_primitive _ (HexPolyZMathlib.content_ne_zero _ hdg0))
  -- Content/primitive-part decomposition of each dilation.
  have hCF : HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc gf)
      = Polynomial.C (Hex.ZPoly.content (Hex.ZPoly.dilate lc gf)) *
          HexPolyZMathlib.toPolynomial f := by
    rw [HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart, hf]
  have hCG : HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc gg)
      = Polynomial.C (Hex.ZPoly.content (Hex.ZPoly.dilate lc gg)) *
          HexPolyZMathlib.toPolynomial g := by
    rw [HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart, hg]
  -- The dilation transports the association (composition is a monoid hom).
  have hassocComp :
      Associated ((HexPolyZMathlib.toPolynomial gf).comp (Polynomial.C lc * Polynomial.X))
        ((HexPolyZMathlib.toPolynomial gg).comp (Polynomial.C lc * Polynomial.X)) := by
    have hm := hassoc.map (Polynomial.compRingHom (Polynomial.C lc * Polynomial.X))
    rwa [Polynomial.coe_compRingHom_apply, Polynomial.coe_compRingHom_apply] at hm
  have hassocD :
      Associated (HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc gf))
        (HexPolyZMathlib.toPolynomial (Hex.ZPoly.dilate lc gg)) := by
    rw [HexPolyZMathlib.toPolynomial_dilate, HexPolyZMathlib.toPolynomial_dilate]
    exact hassocComp
  rw [hCF, hCG] at hassocD
  exact associated_of_C_mul_associated hFprim hGprim
    (HexPolyZMathlib.content_ne_zero _ hdf0) (HexPolyZMathlib.content_ne_zero _ hdg0) hassocD

/-- **Existential lifted representation producer for `toMonicLiftData`.**

From a `toMonicPrimeData?` selection witness and core/factor side conditions,
produce a lifted subset of `Hex.ZPoly.toMonicLiftData core B primeData` whose
`RepresentsIntegerFactorAtLift` records the original non-monic `factor` — with
no caller-supplied fixed mod-`p` subset.

The route is: build the monic correspondent `g` of `factor`
(`exists_monicCorrespondent_of_dvd`), transport its irreducibility
(`irreducible_toPolynomial_monicCorrespondent`), read off `g`'s mod-`p`
representation (`representsModP_correspondent`), lift it to the monic coordinate
(`toMonicLiftData_represents_lifted_monicCorrespondent`, #7453), then transfer
back to `factor` over the original `core`
(`representsIntegerFactorAtLift_of_monicCorrespondent`, #7452). -/
theorem toMonicLiftData_represents_lifted_of_modP
    (core : Hex.ZPoly) (B : Nat) (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization (Hex.ZPoly.toMonic core).monic primeData)
    (hcore0 : core ≠ 0)
    (hlc : 0 < Hex.DensePoly.leadingCoeff core)
    (hdeg : 1 ≤ (Hex.ZPoly.toMonic core).degree)
    (hB_ne_zero : B ≠ 0)
    {factor : Hex.ZPoly}
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hprim : Hex.ZPoly.Primitive factor)
    (hsign : Hex.normalizeFactorSign factor = factor)
    (hfdeg : 1 ≤ factor.degree?.getD 0)
    (hdvd : factor ∣ core) :
    ∃ S_lifted,
      RepresentsIntegerFactorAtLift core
        (Hex.ZPoly.toMonicLiftData core B primeData) factor S_lifted := by
  classical
  obtain ⟨g, hg_monic, hg_dvd, hrecover⟩ :=
    exists_monicCorrespondent_of_dvd core factor hcore0 hlc hdeg hfdeg hdvd hprim hsign
  have hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g) :=
    irreducible_toPolynomial_monicCorrespondent (ne_of_gt hlc) hg_monic hprim hirr hrecover
  obtain ⟨S_modP, hS_modP⟩ :=
    representsModP_correspondent core primeData hlc hdeg hval hg_irr hg_dvd
  have hcore_deg_pos : 0 < core.degree?.getD 0 := by
    have hd := Hex.ZPoly.toMonic_degree core
    omega
  have hlift :=
    toMonicLiftData_represents_lifted_monicCorrespondent core B primeData hlc
      hcore_deg_pos hval hB_ne_zero hg_monic hg_irr hg_dvd hS_modP
  exact ⟨_, representsIntegerFactorAtLift_of_monicCorrespondent rfl
    (Hex.ZPoly.toMonic_monic_isMonic_of_pos_degree core hlc hcore_deg_pos) hlift hrecover⟩

end

end HexBerlekampZassenhausMathlib
