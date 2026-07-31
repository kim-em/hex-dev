/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.UFDPartition
public import HexBerlekampZassenhausMathlib.ModPFactorization
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

import all HexBerlekampZassenhausMathlib.ModularPolynomial
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.SubsetCoprimality

public section
set_option backward.proofsInPublic true

/-!
# Modular support partitions

Existence, uniqueness, and cover for the subsets of the selected finite-field
factorization that represent irreducible integer factors.  Finite-field
factors are normalized to monic form here; Hensel lifting and integer recovery
remain in the original coordinates.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

/-- `factorsModP.toList` mapped to Mathlib polynomials has product equal to the
Mathlib transport of `monicModularImage (modP p core)`. The proof uses the
semantic bundle: its
`product` congruence over `ℤ` descends to an `FpPoly` product equality via
`modP_eq_of_congr` and the `modP`/`liftToZ` roundtrip, and the monic-image
layer collapses on the monic lift target. -/
private lemma toMathlibPolynomial_factorsModP_product_eq_monicModularImage
    {core : Hex.ZPoly} {primeData : Hex.PrimeChoiceData}
    (hval : ModPFactorization core primeData) :
    letI := primeData.bounds
    ((primeData.factorsModP.toList : Multiset _).map
        HexBerlekampMathlib.toMathlibPolynomial).prod =
      HexBerlekampMathlib.toMathlibPolynomial
        (Hex.monicModularImage
          (@Hex.ZPoly.modP primeData.p primeData.bounds core)) := by
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p := hval.prime
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hp : 1 < primeData.p := by have := hprime.two_le; omega
  -- Descend the bundle's `ℤ` congruence to an `FpPoly` product equality;
  -- the `modP`/`liftToZ` roundtrip collapses the right-hand side.
  have hmod :
      Hex.ZPoly.modP primeData.p
          (Array.polyProduct (primeData.factorsModP.map Hex.FpPoly.liftToZ)) =
        Hex.monicModularImage (Hex.ZPoly.modP primeData.p core) := by
    have h := Hex.ZPoly.modP_eq_of_congr primeData.p _ _ hval.product
    rwa [Hex.FpPoly.modP_liftToZ] at h
  rw [← hmod]
  have hbridge :
      (primeData.factorsModP.toList.map
          HexBerlekampMathlib.toMathlibPolynomial).prod =
        HexBerlekampMathlib.toMathlibPolynomial
          (Hex.ZPoly.modP primeData.p
            (Array.polyProduct
              (primeData.factorsModP.map Hex.FpPoly.liftToZ))) := by
    rw [modP_polyProduct_map_liftToZ, toMathlibPolynomial_listFoldlMul_one]
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

/-- For every indexed modular factor selected by a successful
`choosePrimeData?` run, recover an irreducible integer divisor whose monic
mod-`p` image is divisible by that indexed factor. -/
theorem exists_factor_of_modPIndex
    (core : Hex.ZPoly) (hcore_ne : core ≠ 0)
    (_hcore_pos : 0 < core.degree?.getD 0)
    (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization core primeData)
    (i : ModPFactorIndex primeData) :
    letI := primeData.bounds
    ∃ g : Hex.ZPoly,
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ core ∧
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i) ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (monicModPImage (Hex.ZPoly.modP primeData.p g)) := by
  classical
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p := hval.prime
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hprime_root : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime_root⟩
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    hval.good
  have hcore_modP_iszero :
      (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  let hfield := @Hex.zmod64FieldOfPrime primeData.p primeData.bounds
    (Hex.ZMod64.primeModulusOfPrime hprime)
  letI := hfield
  set f : ModPFactorIndex primeData → Polynomial (ZMod primeData.p) :=
      fun i => HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)
      with hf_def
  have hirr_i : Irreducible (f i) := by
    rw [hf_def]
    exact hval.irreducible i
  have hprime_i : Prime (f i) :=
    UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr_i
  have hfi_dvd_monic_core :
      f i ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage
            (@Hex.ZPoly.modP primeData.p primeData.bounds core)) := by
    rw [← toMathlibPolynomial_factorsModP_product_eq_monicModularImage hval,
      ← univ_val_map_modPFactor_eq_factorsModP_map primeData]
    exact Multiset.dvd_prod (by
      rw [Multiset.mem_map]
      exact ⟨i, by simp, rfl⟩)
  have hmonic_core_dvd_core :
      HexBerlekampMathlib.toMathlibPolynomial
          (Hex.monicModularImage
            (@Hex.ZPoly.modP primeData.p primeData.bounds core)) ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (@Hex.ZPoly.modP primeData.p primeData.bounds core) :=
    toMathlibPolynomial_dvd
      (monicModularImage_dvd_self_of_isZero_false hprime hcore_modP_iszero)
  have hfi_dvd_map_core :
      f i ∣ (HexPolyZMathlib.toPolynomial core).map
        (Int.castRingHom (ZMod primeData.p)) := by
    rw [← toMathlibPolynomial_modP_eq_map_intCast_zmod]
    exact hfi_dvd_monic_core.trans hmonic_core_dvd_core
  set corePoly : Polynomial ℤ := HexPolyZMathlib.toPolynomial core with hcorePoly_def
  have hcorePoly_ne : corePoly ≠ 0 := by
    intro hzero
    apply hcore_ne
    apply HexPolyZMathlib.equiv.injective
    simpa [hcorePoly_def] using hzero
  have hfi_dvd_map_norm :
      f i ∣ (normalize corePoly).map (Int.castRingHom (ZMod primeData.p)) := by
    have hcore_dvd_norm : corePoly ∣ normalize corePoly :=
      (associated_normalize corePoly).dvd
    have hmap_core_dvd_norm :
        corePoly.map (Int.castRingHom (ZMod primeData.p)) ∣
          (normalize corePoly).map (Int.castRingHom (ZMod primeData.p)) :=
      Polynomial.map_dvd _ hcore_dvd_norm
    have hfi_dvd_map_core' :
        f i ∣ corePoly.map (Int.castRingHom (ZMod primeData.p)) := by
      simpa [hcorePoly_def] using hfi_dvd_map_core
    exact hfi_dvd_map_core'.trans hmap_core_dvd_norm
  set qList : List (Polynomial ℤ) :=
    (UniqueFactorizationMonoid.normalizedFactors corePoly).toList with hqList_def
  have hmap_list_prod (xs : List (Polynomial ℤ)) :
      (xs.map
          (fun q : Polynomial ℤ =>
            q.map (Int.castRingHom (ZMod primeData.p)))).prod =
        xs.prod.map (Int.castRingHom (ZMod primeData.p)) := by
    induction xs with
    | nil =>
        simp
    | cons q qs ih =>
        simp [ih, Polynomial.map_mul]
  have hmap_prod :
      (qList.map
          (fun q : Polynomial ℤ =>
            q.map (Int.castRingHom (ZMod primeData.p)))).prod =
        (normalize corePoly).map (Int.castRingHom (ZMod primeData.p)) := by
    have hnorm_prod_list : qList.prod = normalize corePoly := by
      rw [hqList_def]
      simpa [Multiset.prod_coe] using
        UniqueFactorizationMonoid.prod_normalizedFactors_eq hcorePoly_ne
    rw [hmap_list_prod, hnorm_prod_list]
  have hfi_dvd_normprod :
      f i ∣
        (qList.map
          (fun q : Polynomial ℤ =>
            q.map (Int.castRingHom (ZMod primeData.p)))).prod := by
    rw [hmap_prod]
    exact hfi_dvd_map_norm
  obtain ⟨qMap, hqMap_mem, hfi_dvd_qMap⟩ :=
    (Prime.dvd_prod_iff hprime_i).mp hfi_dvd_normprod
  rcases List.mem_map.mp hqMap_mem with ⟨q, hq_mem_list, hqMap_eq⟩
  have hq_mem : q ∈ UniqueFactorizationMonoid.normalizedFactors corePoly := by
    rw [← Multiset.mem_toList, ← hqList_def]
    exact hq_mem_list
  subst qMap
  set g : Hex.ZPoly := HexPolyZMathlib.ofPolynomial q with hg_def
  have hg_toPoly : HexPolyZMathlib.toPolynomial g = q := by
    simp [hg_def]
  have hg_irr : Irreducible (HexPolyZMathlib.toPolynomial g) := by
    rw [hg_toPoly]
    exact UniqueFactorizationMonoid.irreducible_of_normalized_factor q hq_mem
  have hg_dvd : g ∣ core := by
    have hq_dvd : q ∣ corePoly :=
      UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hq_mem
    rcases hq_dvd with ⟨r, hr⟩
    refine ⟨HexPolyZMathlib.ofPolynomial r, ?_⟩
    apply HexPolyZMathlib.equiv.injective
    show HexPolyZMathlib.toPolynomial core =
      HexPolyZMathlib.toPolynomial (g * HexPolyZMathlib.ofPolynomial r)
    rw [HexPolyZMathlib.toPolynomial_mul, hg_toPoly,
      HexPolyZMathlib.toPolynomial_ofPolynomial, ← hcorePoly_def]
    exact hr
  have hfi_dvd_modP_g :
      f i ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (@Hex.ZPoly.modP primeData.p primeData.bounds g) := by
    rw [toMathlibPolynomial_modP_eq_map_intCast_zmod, hg_toPoly]
    exact hfi_dvd_qMap
  have hfi_dvd_monic_g :
      f i ∣
        HexBerlekampMathlib.toMathlibPolynomial
          (@monicModPImage primeData.p primeData.bounds
            (@Hex.ZPoly.modP primeData.p primeData.bounds g)) := by
    by_cases hzero :
        (@Hex.ZPoly.modP primeData.p primeData.bounds g).isZero = true
    · have hmonic_zero :
          @monicModPImage primeData.p primeData.bounds
              (@Hex.ZPoly.modP primeData.p primeData.bounds g) = 0 := by
        unfold monicModPImage
        rw [if_pos hzero]
      rw [hmonic_zero]
      have hz : HexBerlekampMathlib.toMathlibPolynomial
          (0 : Hex.FpPoly primeData.p) = 0 := by
        apply Polynomial.ext
        intro n
        rw [Polynomial.coeff_zero, HexBerlekampMathlib.coeff_toMathlibPolynomial,
          Hex.DensePoly.coeff_eq_zero_of_size_le _
            (show (0 : Hex.FpPoly primeData.p).size ≤ n by simp)]
        exact HexModArithMathlib.ZMod64.toZMod_zero
      rw [hz]
      exact dvd_zero (f i)
    · have hnz :
          (@Hex.ZPoly.modP primeData.p primeData.bounds g).isZero = false := by
        cases h :
            (@Hex.ZPoly.modP primeData.p primeData.bounds g).isZero <;>
          simp_all
      exact hfi_dvd_modP_g.trans
        (toMathlibPolynomial_dvd (self_dvd_monicModPImage hnz))
  refine ⟨g, hg_irr, hg_dvd, ?_⟩
  simpa [hf_def] using hfi_dvd_monic_g

/-- Final assembly: the analyzable `choosePrimeData? core = some primeData`
branch of the integer-irreducible → mod-`p` representing-subset existence
and uniqueness statement. -/
theorem existsUnique_modPFactorSubset_of_choosePrimeData_of_some
    (core : Hex.ZPoly) {factor : Hex.ZPoly}
    (_hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hcore_ne : core ≠ 0)
    (_hcore_pos : 0 < core.degree?.getD 0)
    (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization core primeData) :
    ∃! S : ModPFactorSubset primeData,
      RepresentsIntegerFactorModP primeData factor S := by
  classical
  letI := primeData.bounds
  have hprime : Hex.Nat.Prime primeData.p := hval.prime
  letI : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  have hprime_root : _root_.Nat.Prime primeData.p := by
    refine _root_.Nat.prime_def_lt.mpr ⟨hprime.two_le, ?_⟩
    intro m hmlt hmdvd
    rcases hprime.right m hmdvd with h | h
    · exact h
    · exact absurd h (Nat.ne_of_lt hmlt)
  haveI : Fact (_root_.Nat.Prime primeData.p) := ⟨hprime_root⟩
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    hval.good
  have hzero : (@Hex.ZPoly.modP primeData.p primeData.bounds core).isZero = false :=
    Hex.isGoodPrime_modP_isZero_false core primeData.p hgood
  have hnodup : primeData.factorsModP.toList.Nodup := hval.nodup
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
    exact hval.irreducible _
  -- Each q in factorsM is monic, hence normalize-fixed.
  have hmonic_each : ∀ q ∈ factorsM, q.Monic := by
    intro q hq
    rw [hfactorsM_def, Multiset.mem_map] at hq
    obtain ⟨g, hg_mem, hg_eq⟩ := hq
    rw [Multiset.mem_coe] at hg_mem
    have hg_monic : Hex.DensePoly.Monic g :=
      hval.monic g (Array.mem_toList_iff.mp hg_mem)
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
    monicModPImage_dvd_monicModularImage_of_dvd_of_goodPrime
      hdvd hcore_ne hprime hgood
  have hmathD_dvd : mathD ∣ factorsM.prod := by
    rw [hfactorsM_def, toMathlibPolynomial_factorsModP_product_eq_monicModularImage hval,
      hmathD_def]
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
theorem existsUnique_modPFactorSubset_of_modPFactorization
    (core : Hex.ZPoly) {factor : Hex.ZPoly}
    (primeData : Hex.PrimeChoiceData)
    (hirr : Irreducible (HexPolyZMathlib.toPolynomial factor))
    (hdvd : factor ∣ core)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization core primeData) :
    ∃! S : ModPFactorSubset primeData,
      RepresentsIntegerFactorModP primeData factor S := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  -- `core ≠ 0` from `isGoodPrime` (which forces `(modP p core).isZero = false`).
  have hcore_ne : core ≠ 0 := by
    intro hcore_zero
    have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
      hval.good
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
    hirr hdvd hcore_ne hcore_pos primeData hval

/-- Construct `ModPSubsetPartitionHypotheses` at the executable
`Hex.choosePrimeData` boundary.

Composes:

* `Hex.choosePrimeData?_fModP_eq` for `fModP_eq`;
* `trivial` for the `True` `admissible_prime` / `square_free_reduction` hooks;
* `factors_irreducible_of_choosePrimeData_of_some` for the per-factor
  irreducibility component;
* `existsUnique_modPFactorSubset_of_choosePrimeData` for both the
  existence and uniqueness components.

The `hchoose` hypothesis is an explicit `choosePrimeData? = some` witness,
so the `none` branch (where the mod-`p` factorisation invariant is
unavailable) is excluded; downstream callers discharge it from the same
`choosePrimeData?` chain that supplies the other partition fields. -/
theorem modPSubsetPartitionHypotheses_of_modPFactorization
    (core : Hex.ZPoly)
    (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization core primeData) :
    ModPSubsetPartitionHypotheses core primeData True True := by
  refine
    { fModP_eq := ?_
      admissible_prime := trivial
      square_free_reduction := trivial
      factors_irreducible := ?_
      exists_subset := ?_
      unique_subset := ?_ }
  · exact hval.fModP_eq
  · exact hval.irreducible
  · intro factor hirr hdvd
    exact (existsUnique_modPFactorSubset_of_modPFactorization core primeData hirr hdvd hcore_pos hval).exists
  · intro factor S T hirr hdvd hS hT
    rcases existsUnique_modPFactorSubset_of_modPFactorization core primeData hirr hdvd hcore_pos hval with
      ⟨_, _, huniq⟩
    exact (huniq S hS).trans (huniq T hT).symm

/-- A successful `choosePrimeData?` run forces a nonzero square-free part: the selected
prime is `isGoodPrime`, which keeps `(modP p core)` nonzero, whereas
`modP p 0 = 0`. -/
theorem core_ne_zero_of_modPFactorization
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization core primeData) :
    core ≠ 0 := by
  letI : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  intro hcore_zero
  have hgood : @Hex.isGoodPrime core primeData.p primeData.bounds = true :=
    hval.good
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

/-- The Mathlib images of the selected modular factors are distinct: `choosePrimeData?`
guarantees `factorsModP.toList.Nodup`, and `toMathlibPolynomial` is injective. -/
theorem toMathlibPolynomial_modPFactor_injective_of_modPFactorization
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization core primeData) :
    letI := primeData.bounds
    Function.Injective (fun i : ModPFactorIndex primeData =>
      HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)) := by
  letI := primeData.bounds
  have hnodup : primeData.factorsModP.toList.Nodup := hval.nodup
  have hinjPoly : Function.Injective
      (HexBerlekampMathlib.toMathlibPolynomial : Hex.FpPoly primeData.p → _) :=
    HexBerlekampMathlib.fpPolyEquiv.injective
  intro i j hij
  by_contra hne
  exact modPFactor_ne_of_ne hnodup hne (hinjPoly hij)

/-- The Mathlib images of the selected modular factors are monic: `choosePrimeData?`
guarantees each `factorsModP` entry is monic, preserved by `toMathlibPolynomial`. -/
theorem toMathlibPolynomial_modPFactor_monic_of_modPFactorization
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hval : ModPFactorization core primeData) :
    letI := primeData.bounds
    ∀ i : ModPFactorIndex primeData,
      (HexBerlekampMathlib.toMathlibPolynomial (modPFactor primeData i)).Monic := by
  letI := primeData.bounds
  have hmonic := hval.monic
  intro i
  exact HexBerlekampMathlib.toMathlibPolynomial_monic _ (hmonic _ (Array.getElem_mem _))

/-- **modP cover.** Every selected modular factor index lies in the
representing subset of some irreducible integer divisor of `core`.

Assembled from `exists_factor_of_modPIndex` (recover an irreducible divisor `g`
whose monic mod-`p` image the indexed factor divides), the subset-partition
existence projection (a representing subset `S` for `g`), and
`mem_modPSubset_of_dvd` (the divisibility forces `i ∈ S`). -/
theorem modPFactor_index_cover
    (core : Hex.ZPoly) (primeData : Hex.PrimeChoiceData)
    (hcore_pos : 0 < core.degree?.getD 0)
    (hval : ModPFactorization core primeData)
    (i : ModPFactorIndex primeData) :
    ∃ (g : Hex.ZPoly) (S : ModPFactorSubset primeData),
      Irreducible (HexPolyZMathlib.toPolynomial g) ∧
      g ∣ core ∧
      i ∈ S ∧
      RepresentsIntegerFactorModP primeData g S := by
  letI := primeData.bounds
  have hcore_ne : core ≠ 0 := core_ne_zero_of_modPFactorization core primeData hval
  obtain ⟨g, hirr, hdvd, hfi_dvd⟩ :=
    exists_factor_of_modPIndex core hcore_ne hcore_pos primeData hval i
  have hpart : ModPSubsetPartitionHypotheses core primeData True True :=
    modPSubsetPartitionHypotheses_of_modPFactorization core primeData hcore_pos hval
  obtain ⟨S, hS⟩ :=
    exists_modPFactorSubset_of_modPSubsetPartition hpart hirr hdvd
  have hprime : _root_.Nat.Prime primeData.p :=
    natPrime_of_hexNatPrime hval.prime
  have hf_inj :=
    toMathlibPolynomial_modPFactor_injective_of_modPFactorization core primeData hval
  have hmonic :=
    toMathlibPolynomial_modPFactor_monic_of_modPFactorization core primeData hval
  have hiS : i ∈ S := mem_modPSubset_of_dvd hprime hpart hf_inj hmonic hS hfi_dvd
  exact ⟨g, S, hirr, hdvd, hiS, hS⟩

end

end HexBerlekampZassenhausMathlib
