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

public import HexBerlekampZassenhausMathlib.HenselFactorProps
import all HexBerlekampZassenhausMathlib.PublicSurface
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate
import all HexBerlekampZassenhausMathlib.HenselFactorProps

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
This module collects `choosePrimeData` degree/injectivity plus subset/complement coprimality.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- Composed convenience wrapper: combines
`Hex.ZPoly.QuadraticMultifactorLiftInvariant_of_choosePrimeData` with
`henselLiftData_liftedFactor_injective` so that a Mathlib-side caller can
discharge `Function.Injective (liftedFactor (henselLiftData core B primeData))`
from the `choosePrimeData` boundary facts plus `factorsModP.toList.Nodup`,
without having to construct the internal `QuadraticMultifactorLiftInvariant`
themselves.

Consumed by
`recombinationSearchModAux_some_factor_associated_of_liftedFactorSubsetPartition`
(via `LiftedFactorListMatches.nodup_of_injOn`).

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
      show Hex.ZPoly.modP primeData.p
          (liftedFactor d (liftedIndexOfModPIndex primeData d hsize i)) =
        modPFactor primeData i
      exact hfactor_modP
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
Multiplicative closure of the recovered/monic-coordinate representation carrier
`RecoveredAtLift` along a disjoint decomposition `S ∪ T`. If `S` recovers the
integer factor `f` and `T` (disjoint from `S`) recovers `g`, then `S ∪ T`
recovers `f * g`.

Unlike the compatibility wrapper
`representsIntegerFactorAtLift_mul_of_monic_core`, this holds for an
*arbitrary* core: the carrier already separates the mod-`p^k` congruence (on
the unscaled `liftedFactorProduct`) from the dilation by `leadingCoeff core`, so
no monicity hypothesis is needed. The witness monic coordinate is the product of
the two witnesses; the `congr` field combines
`liftedFactorProduct_union_of_disjoint` with `Hex.ZPoly.congr_mul`, and the
`dilate_eq` field combines `HexPolyZMathlib.dilate_mul` (dilation is
multiplicative) with `Hex.ZPoly.primitivePart_mul` (Gauss's lemma).

The `monic_dvd` field is **not** closed under the helper unconditionally: the
two component divisibilities `hf.monicFactor ∣ (toMonic core).monic` and
`hg.monicFactor ∣ (toMonic core).monic` do not give
`hf.monicFactor * hg.monicFactor ∣ (toMonic core).monic` without coprimality of
the two coordinates.  The product divisibility is therefore taken as an explicit
premise `hmul_dvd`, supplied by the squarefree-lift context where it genuinely
holds. -/
def RecoveredAtLift.mul
    {core f g : Hex.ZPoly} {d : Hex.LiftData}
    {S T : LiftedFactorSubset d}
    (hdisj : Disjoint S T)
    (hf : RecoveredAtLift core d f S)
    (hg : RecoveredAtLift core d g T)
    (hmul_dvd :
      hf.monicFactor * hg.monicFactor ∣ (Hex.ZPoly.toMonic core).monic) :
    RecoveredAtLift core d (f * g) (S ∪ T) where
  monicFactor := hf.monicFactor * hg.monicFactor
  congr := by
    have hpk_pos : 0 < d.p ^ d.k := Nat.pow_pos d.p_pos
    have hcongr_f :
        Hex.ZPoly.congr (liftedFactorProduct d S) hf.monicFactor (d.p ^ d.k) :=
      congr_of_reduceModPow_eq _ _ _ _ hpk_pos hf.congr
    have hcongr_g :
        Hex.ZPoly.congr (liftedFactorProduct d T) hg.monicFactor (d.p ^ d.k) :=
      congr_of_reduceModPow_eq _ _ _ _ hpk_pos hg.congr
    have hcongr_mul :
        Hex.ZPoly.congr (liftedFactorProduct d S * liftedFactorProduct d T)
          (hf.monicFactor * hg.monicFactor) (d.p ^ d.k) :=
      Hex.ZPoly.congr_mul _ _ _ _ _ hcongr_f hcongr_g
    rw [liftedFactorProduct_union_of_disjoint hdisj]
    exact Hex.ZPoly.reduceModPow_eq_of_congr _ _ _ _ hcongr_mul
  dilate_eq := by
    rw [HexPolyZMathlib.dilate_mul, Hex.ZPoly.primitivePart_mul,
      hf.dilate_eq, hg.dilate_eq]
  monic_dvd := hmul_dvd

/--
Multiplicative closure of `RepresentsIntegerFactorAtLift` along a disjoint
decomposition `S ∪ T`, packaged from the recovered carriers.  Thin wrapper over
`RecoveredAtLift.mul` returning the public predicate.

Inputs are the data-bearing `RecoveredAtLift` carriers (not the
`Nonempty`-erased predicate) because the product-divisibility premise `hmul_dvd`
the carrier's `monic_dvd` field now demands must reference the component monic
coordinates, which are not nameable through the erased predicate.  The
monic-core hypothesis is retained for signature compatibility with the prior
wrapper.
-/
theorem representsIntegerFactorAtLift_mul_of_monic_core
    {core f g : Hex.ZPoly} {d : Hex.LiftData}
    {S T : LiftedFactorSubset d}
    (_hcore_monic : Hex.DensePoly.Monic core)
    (hdisj : Disjoint S T)
    (hf : RecoveredAtLift core d f S)
    (hg : RecoveredAtLift core d g T)
    (hmul_dvd :
      hf.monicFactor * hg.monicFactor ∣ (Hex.ZPoly.toMonic core).monic) :
    RepresentsIntegerFactorAtLift core d (f * g) (S ∪ T) :=
  RepresentsIntegerFactorAtLift.ofRecovered (RecoveredAtLift.mul hdisj hf hg hmul_dvd)

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

end

end HexBerlekampZassenhausMathlib
