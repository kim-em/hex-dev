/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhaus
public import HexBerlekampMathlib.Irreducibility
public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexHenselMathlib.HenselLemmas
public import HexPolyZMathlib.PolynomialEquivalence
public import HexPolyZMathlib.Mignotte
public import Mathlib.RingTheory.Coprime.Lemmas
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.PrincipalIdealDomain

public import HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.ModularPolynomial
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate

public section
set_option backward.proofsInPublic true

/-!
Monic, primitive, and congruence properties of Hensel-lifted factors.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Monic integer polynomials have positive stored size. -/
theorem zpoly_size_pos_of_monic {f : Hex.ZPoly}
    (h : Hex.DensePoly.Monic f) : 0 < f.size := by
  have hlead : Hex.DensePoly.leadingCoeff f = (1 : Int) := h
  rcases Nat.eq_zero_or_pos f.coeffs.size with hcs_zero | hcs_pos
  · exfalso
    have hlc_zero : Hex.DensePoly.leadingCoeff f = (0 : Int) := by
      simp [Hex.DensePoly.leadingCoeff, hcs_zero, Array.getD]; rfl
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

The recursive coverage proof for `Hex.recombinationSearchModAux` uses this
after obtaining a monic integer divisor of the current target. Together with
the Hensel-lift partition, this helper discharges the primitive and
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

/-- Multifactor Hensel lifting preserves the number of selected modular factors. -/
theorem MonicLift.factorCount_eq
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
every output index given monicness of the input polynomial and the quadratic
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

The proof uses `Hex.ZPoly.multifactorLiftQuadratic_each_congr_mod_base`:
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

end

end HexBerlekampZassenhausMathlib
