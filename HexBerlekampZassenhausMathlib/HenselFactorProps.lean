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

public import HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects the monic-primitive helpers, `henselLiftData` properties, and Berlekamp-form `factorsModP`.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Monic integer polynomials have positive stored size. -/
private theorem zpoly_size_pos_of_monic {f : Hex.ZPoly}
    (h : Hex.DensePoly.Monic f) : 0 < f.size := by
  have hlead : Hex.DensePoly.leadingCoeff f = (1 : Int) := h
  rcases Nat.eq_zero_or_pos f.coeffs.size with hcs_zero | hcs_pos
  · exfalso
    have hlc_zero : Hex.DensePoly.leadingCoeff f = (0 : Int) := by
      simp [Hex.DensePoly.leadingCoeff, hcs_zero, Array.getD] <;> rfl
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
In the monic-core regime the centered/dilated recovered product equals the
represented integer factor with no primitive-part correction.

The carrier's `dilate_eq` field only exposes
`primitivePart (dilate (lc core) monicFactor) = factor`, but when `core` is
monic the dilation collapses (`leadingCoeff core = 1`) and `monicFactor` is a
divisor of the monic core, hence primitive, so the `primitivePart` is the
identity.  The congruence field plus the Mignotte bound then identify the
centered selected product with `monicFactor`.  This is exactly the
recovered-equality input consumed by `BHKS.recoveredLiftOfSubset`, and unlike
`RecoveredAtLift.candidate_eq_of_monic_dvd` it is stated without the
`primitivePart`/`normalizeFactorSign` corrections that the `RecoveredLift`
package omits.
-/
theorem dilate_centeredLift_eq_factor_of_represents_monic
    {core factor : Hex.ZPoly} {d : Hex.LiftData} {S : LiftedFactorSubset d}
    (hcore_monic : Hex.DensePoly.Monic core)
    (hrep : RepresentsIntegerFactorAtLift core d factor S)
    (hprecision :
      2 * Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic <
        d.p ^ d.k) :
    Hex.ZPoly.dilate (Hex.DensePoly.leadingCoeff core)
        (Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k)) =
      factor := by
  classical
  obtain ⟨R⟩ := hrep
  have hlc : Hex.DensePoly.leadingCoeff core = (1 : Int) := hcore_monic
  have htoMonic : (Hex.ZPoly.toMonic core).monic = core :=
    Hex.ZPoly.toMonic_monic_eq_core_of_leadingCoeff_eq_one core hlc
  have hcore_prim : Hex.ZPoly.Primitive core := zpoly_primitive_of_monic hcore_monic
  have hcore_ne : core ≠ 0 := by
    intro h
    have hc : Hex.ZPoly.content core = 1 := hcore_prim
    rw [h] at hc
    simp [Hex.ZPoly.content] at hc
  -- `monicFactor` divides the monic core, hence is primitive.
  have hdvd : R.monicFactor ∣ core := by
    have h := R.monic_dvd
    rw [htoMonic] at h
    exact h
  have hcore_poly_prim : (HexPolyZMathlib.toPolynomial core).IsPrimitive :=
    HexPolyZMathlib.isPrimitive_toPolynomial_of_primitive core hcore_prim
  have hmf_dvd_poly :
      HexPolyZMathlib.toPolynomial R.monicFactor ∣
        HexPolyZMathlib.toPolynomial core :=
    HexPolyMathlib.toPolynomial_dvd hdvd
  have hmf_prim_poly : (HexPolyZMathlib.toPolynomial R.monicFactor).IsPrimitive :=
    isPrimitive_of_dvd hcore_poly_prim hmf_dvd_poly
  have hmf_prim : Hex.ZPoly.Primitive R.monicFactor := by
    have := Polynomial.isPrimitive_iff_content_eq_one.mp hmf_prim_poly
    rwa [HexPolyZMathlib.toPolynomial_content] at this
  have hprim_self : Hex.ZPoly.primitivePart R.monicFactor = R.monicFactor :=
    Hex.ZPoly.primitivePart_eq_self_of_primitive R.monicFactor hmf_prim
  -- `dilate_eq` collapses to `monicFactor = factor`.
  have hmf_eq : R.monicFactor = factor := by
    have h := R.dilate_eq
    rw [hlc, Hex.ZPoly.dilate_one, hprim_self] at h
    exact h
  -- The Mignotte bound and the congruence field recover `monicFactor`.
  have hmonic_ne : (Hex.ZPoly.toMonic core).monic ≠ 0 := by rw [htoMonic]; exact hcore_ne
  have hbound : ∀ i, (R.monicFactor.coeff i).natAbs ≤
      Hex.ZPoly.defaultFactorCoeffBound (Hex.ZPoly.toMonic core).monic := fun i =>
    defaultFactorCoeffBound_valid (Hex.ZPoly.toMonic core).monic hmonic_ne
      R.monicFactor R.monic_dvd i
  have hcl :
      Hex.centeredLiftPoly (liftedFactorProduct d S) (d.p ^ d.k) = R.monicFactor := by
    rw [← centeredLiftPoly_reduceModPow_eq (liftedFactorProduct d S) d.p d.k d.p_pos,
      R.congr]
    exact Hex.centeredLiftPoly_reduceModPow_eq_of_coeff_natAbs_le
      R.monicFactor d.p d.k _ hbound hprecision
  rw [hlc, Hex.ZPoly.dilate_one, hcl, hmf_eq]

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
(in `HexBerlekampZassenhaus`) packages the per-factor monicness,
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
  rfl

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

/-- Under the `factorsModPBerlekampForm` invariant and a good prime, a positive-
degree input polynomial has a positive-degree monic modular image.  `isGoodPrime`'s
leading-coefficient admissibility preserves the degree through `modP`, and the
monic rescale is by a nonzero unit, so it preserves size.  This is the positivity
guard consumed by the per-modular-factor Mathlib irreducibility bridge. -/
theorem monicModularImage_modP_degree?_pos_of_factorsModPBerlekampForm
    (f : Hex.ZPoly) (data : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm f data)
    (hgood :
      letI := data.bounds
      Hex.isGoodPrime f data.p = true)
    (hf_pos : 0 < f.degree?.getD 0) :
    letI := data.bounds
    0 < (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).degree?.getD 0 := by
  letI : Hex.ZMod64.Bounds data.p := data.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  letI : Hex.ZMod64.PrimeModulus data.p := Hex.ZMod64.primeModulusOfPrime hprime
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
  unfold Hex.DensePoly.degree?
  have hne : (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).size ≠ 0 := by omega
  simp [hne]; omega

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
  -- Step A: 0 < (monicModularImage (modP data.p f)).degree?.getD 0
  have hmonicImage_pos :
      0 < (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).degree?.getD 0 :=
    monicModularImage_modP_degree?_pos_of_factorsModPBerlekampForm f data hform hgood hf_pos
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield := @Hex.zmod64FieldOfPrime data.p data.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI : Hex.ZMod64.PrimeModulus data.p := Hex.ZMod64.primeModulusOfPrime hprime
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

/-- Form-only product congruence at the monic modular image: the product of
`core`'s lifted Berlekamp factors is congruent modulo `p` to
`liftToZ (monicModularImage (modP p core))`.  Depends only on the Berlekamp form;
this is `_of_primitive_pos_lc_core` with the (unused) primitivity / leading-
coefficient / good-prime premises dropped. -/
theorem factorsModP_polyProduct_congr_monicImage_of_factorsModPBerlekampForm
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm core primeData) :
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
  have hmonicImage_monic :
      Hex.DensePoly.Monic (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) :=
    Hex.monicModularImage_monic hprime (Hex.ZPoly.modP primeData.p core) hzero
  let raw :=
      (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
        (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
        hmonicImage_monic hfield).factors
  have hprod_eq_raw :
      Hex.Berlekamp.factorProduct raw =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    show Hex.Berlekamp.factorProduct
        (@Hex.Berlekamp.berlekampFactor primeData.p primeData.bounds
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
          hmonicImage_monic hfield).factors = _
    rw [Hex.Berlekamp.factorProduct_berlekampFactor]
  have hraw_ne : ∀ g ∈ raw, g ≠ 0 :=
    Hex.Berlekamp.berlekampFactor_factors_ne_zero
      (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core))
      hmonicImage_monic
  have hmonicImage_idem :
      Hex.monicModularImage (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) :=
    Hex.monicModularImage_eq_self_of_monic hprime _ hmonicImage_monic
  have hprod_eq_mapped :
      Hex.Berlekamp.factorProduct (raw.map Hex.monicModularImage) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    rw [Hex.factorProduct_map_monicModularImage_eq_monicModularImage_factorProduct
        hprime raw hraw_ne, hprod_eq_raw, hmonicImage_idem]
  have hbridge :=
    polyProduct_map_liftToZ_congr_factorProduct (p := primeData.p)
      (raw.map Hex.monicModularImage)
  rw [hprod_eq_mapped] at hbridge
  rw [heq, List.map_toArray]
  exact hbridge

/--
**`monicTarget` factor-product congruence** (M1 Hensel lift invariant boundary).

The product of `core`'s lifted modular factors is congruent to the `monicTarget`
modulo `p`.  Derived from `core`'s Berlekamp form (which lands the product at the
monic modular image of `modP p core`) plus the bridge
`monicModularImage_modP_eq_modP_monicTarget`. -/
theorem factorsModP_polyProduct_congr_monicTarget
    (core : Hex.ZPoly) (k : Nat) (primeData : Hex.PrimeChoiceData)
    (hpk : 1 < primeData.p ^ k) (hk : 0 < k)
    (hgcd : Int.gcd (Hex.DensePoly.leadingCoeff core)
      (Int.ofNat (primeData.p ^ k)) = 1)
    (hform : Hex.factorsModPBerlekampForm core primeData)
    (hgood :
      letI := primeData.bounds
      Hex.isGoodPrime core primeData.p = true) :
    letI := primeData.bounds
    Hex.ZPoly.congr
      (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
      (Hex.ZPoly.monicTarget core primeData.p k) primeData.p := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hz, he⟩ := hform
  have h1 :
      Hex.ZPoly.congr
        (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ))
        (Hex.FpPoly.liftToZ
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)))
        primeData.p :=
    factorsModP_polyProduct_congr_monicImage_of_factorsModPBerlekampForm
      core primeData ⟨hprime, hz, he⟩
  have hbridge :
      Hex.ZPoly.congr
        (Hex.FpPoly.liftToZ
          (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)))
        (Hex.ZPoly.monicTarget core primeData.p k) primeData.p := by
    rw [monicModularImage_modP_eq_modP_monicTarget core primeData.p k hprime hpk hk hgcd hgood]
    exact Hex.FpPoly.congr_liftToZ_modP (Hex.ZPoly.monicTarget core primeData.p k)
  exact Hex.ZPoly.congr_trans _ _ _ _ h1 hbridge

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
              rw [hmodP_g, hmodP_tail, hrawGcd_def, Hex.DensePoly.gcd_eq_xgcd_gcd]
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
of `gcd_monicModularImage_derivative_isUnit_local`, instantiated through
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

/- Square-freeness of a nonzero `FpPoly` transfers to its monic representative.

Local copy of the IntReductionMod helper of the same name (the canonical
version lives at `HexBerlekampZassenhausMathlib/IntReductionMod.lean:307`).
Duplicated here because `IntReductionMod` imports `Basic`; the proof routes
through `IsCoprime` in `Polynomial (ZMod p)` using
`toMathlibPolynomial_squareFree_coprime` and the `toMathlibPolynomial_scale`
identification for the unit scalar `(leadingCoeff f)⁻¹`. -/
/-- A bridged executable polynomial that transports to a unit has executable
size one, hence passes the `gcdIsUnit` size check when used as a gcd. -/
private theorem size_eq_one_of_toMathlibPolynomial_isUnit_local
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    {g : Hex.FpPoly p}
    (h : IsUnit (HexBerlekampMathlib.toMathlibPolynomial g)) :
    g.size = 1 := by
  rcases Nat.lt_or_ge g.size 1 with hlt | hge
  · exfalso
    have hsize_zero : g.size = 0 := by omega
    have hzero : HexBerlekampMathlib.toMathlibPolynomial g = 0 := by
      apply Polynomial.ext
      intro n
      rw [Polynomial.coeff_zero, HexBerlekampMathlib.coeff_toMathlibPolynomial,
        Hex.DensePoly.coeff_eq_zero_of_size_le _ (show g.size ≤ n by omega)]
      exact HexModArithMathlib.ZMod64.toZMod_zero
    exact not_isUnit_zero (hzero ▸ h)
  · by_contra hne
    have hpos : 0 < g.size := by omega
    have hge2 : 2 ≤ g.size := by omega
    have hcoeff_ne : g.coeff (g.size - 1) ≠ 0 :=
      Hex.DensePoly.coeff_last_ne_zero_of_pos_size g hpos
    have hcoeff_zmod_ne :
        HexModArithMathlib.ZMod64.toZMod (g.coeff (g.size - 1)) ≠ 0 := by
      intro hzero
      apply hcoeff_ne
      have hinj := (HexModArithMathlib.ZMod64.equiv (p := p)).injective
      apply hinj
      simpa using hzero.trans HexModArithMathlib.ZMod64.toZMod_zero.symm
    have hcoeff_poly_ne :
        (HexBerlekampMathlib.toMathlibPolynomial g).coeff (g.size - 1) ≠ 0 := by
      rw [HexBerlekampMathlib.coeff_toMathlibPolynomial]
      exact hcoeff_zmod_ne
    have hpos_natDeg :
        0 < (HexBerlekampMathlib.toMathlibPolynomial g).natDegree := by
      have hle := Polynomial.le_natDegree_of_ne_zero hcoeff_poly_ne
      omega
    exact Polynomial.not_isUnit_of_natDegree_pos _ hpos_natDeg h

/-- The Zassenhaus `gcdIsUnit` size check implies Berlekamp's nonzero-constant
unit-polynomial predicate. -/
private theorem isUnitPolynomial_of_gcdIsUnit_local
    {p : Nat} [Hex.ZMod64.Bounds p] {g : Hex.FpPoly p}
    (h : Hex.gcdIsUnit g = true) :
    Hex.Berlekamp.isUnitPolynomial g = true := by
  unfold Hex.gcdIsUnit at h
  change (g.size == 1) = true at h
  have hsize : g.size = 1 := beq_iff_eq.mp h
  unfold Hex.Berlekamp.isUnitPolynomial
  have hpos : 0 < g.size := by omega
  rw [Hex.DensePoly.degree?_eq_some_of_pos_size g hpos, hsize]
  rfl

private theorem gcd_monicModularImage_derivative_isUnit_local
    {p : Nat} [Hex.ZMod64.Bounds p] [Fact (Nat.Prime p)]
    (f : Hex.FpPoly p) (hzero : f.isZero = false)
    (hsquareFree :
      Hex.gcdIsUnit (Hex.DensePoly.gcd f (Hex.DensePoly.derivative f)) = true) :
    Hex.gcdIsUnit
      (Hex.DensePoly.gcd (Hex.monicModularImage f)
        (Hex.DensePoly.derivative (Hex.monicModularImage f))) = true := by
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
      HexBerlekampMathlib.toMathlibPolynomial_squareFree_coprime f
        (isUnitPolynomial_of_gcdIsUnit_local hsquareFree)
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
        show (Hex.DensePoly.leadingCoeff f)⁻¹ * Hex.DensePoly.leadingCoeff f = (1 : Hex.ZMod64 p)
        exact Hex.ZMod64.inv_mul_eq_one_of_prime hp_hex hlead_ne
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
    rw [hmonic_eq, toMathlibPolynomial_scale, Polynomial.derivative_C_mul]
    exact (isCoprime_mul_unit_left hC_unit
      (HexBerlekampMathlib.toMathlibPolynomial f)
      (Polynomial.derivative (HexBerlekampMathlib.toMathlibPolynomial f))).mpr hcop_f
  let g : Hex.FpPoly p :=
    Hex.DensePoly.gcd (Hex.monicModularImage f)
      (Hex.DensePoly.derivative (Hex.monicModularImage f))
  have hunit_math :
      IsUnit
        (gcd
          (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f))
          (Polynomial.derivative
            (HexBerlekampMathlib.toMathlibPolynomial (Hex.monicModularImage f)))) :=
    gcd_isUnit_iff_isRelPrime.mpr hcop.isRelPrime
  have hunit_transport :
      IsUnit (HexBerlekampMathlib.toMathlibPolynomial g) := by
    rw [← HexBerlekampMathlib.toMathlibPolynomial_derivative] at hunit_math
    exact
      (HexBerlekampMathlib.toMathlibPolynomial_gcd_associated
        (Hex.monicModularImage f)
        (Hex.DensePoly.derivative (Hex.monicModularImage f))).symm.isUnit
        hunit_math
  have hg_size : g.size = 1 :=
    size_eq_one_of_toMathlibPolynomial_isUnit_local hunit_transport
  unfold Hex.gcdIsUnit
  change (g.size == 1) = true
  exact beq_iff_eq.mpr hg_size

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
discharged via `gcd_monicModularImage_derivative_isUnit_local` applied to
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
      Hex.isGoodPrime core primeData.p = true)
    (hcore_pos : 0 < core.degree?.getD 0) :
    ∀ i : ModPFactorIndex primeData,
      Irreducible
        (@HexBerlekampMathlib.toMathlibPolynomial primeData.p primeData.bounds
          (modPFactor primeData i)) := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  have hmonicImage_pos :
      0 < (Hex.monicModularImage (Hex.ZPoly.modP primeData.p core)).degree?.getD 0 :=
    monicModularImage_modP_degree?_pos_of_factorsModPBerlekampForm
      core primeData hform hgood hcore_pos
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
      hmonicImage_monic hmonicImage_pos hsf_common_monic
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
    (hselected : Hex.choosePrimeData? core = some primeData)
    (hcore_pos : 0 < core.degree?.getD 0) :
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
  exact factors_irreducible_of_factorsModPBerlekampForm core primeData hform hgood hcore_pos

end

end HexBerlekampZassenhausMathlib
