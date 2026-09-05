/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexBerlekampZassenhausMathlib.Hensel.LiftedFactors
import all HexBerlekampZassenhausMathlib.ModularPolynomial
import all HexBerlekampZassenhausMathlib.ModPFactor
import all HexBerlekampZassenhausMathlib.LiftedFactor
import all HexBerlekampZassenhausMathlib.M1Recovery
import all HexBerlekampZassenhausMathlib.RecombinationSplit
import all HexBerlekampZassenhausMathlib.RecombinationCandidate

public section
set_option backward.proofsInPublic true

/-!
Square-freeness, degree, monicity, and product congruences for modular factors.
-/

namespace HexBerlekampZassenhausMathlib

noncomputable section

open Polynomial

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
  let := primeData.bounds
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

/-- Square-free reduction forbids a positive-degree common divisor of the image and its derivative. -/
theorem squareFree_common_of_squareFreeModP
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
  let : Hex.ZMod64.Bounds data.p := data.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield : Hex.ZMod64.PrimeModulus data.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  let : Hex.ZMod64.PrimeModulus data.p := Hex.ZMod64.primeModulusOfPrime hprime
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
        push Not at h
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
guard consumed by the per-modular-factor Mathlib irreducibility correspondence. -/
theorem monicModularImage_modP_degree?_pos_of_factorsModPBerlekampForm
    (f : Hex.ZPoly) (data : Hex.PrimeChoiceData)
    (hform : Hex.factorsModPBerlekampForm f data)
    (hgood :
      letI := data.bounds
      Hex.isGoodPrime f data.p = true)
    (hf_pos : 0 < f.degree?.getD 0) :
    letI := data.bounds
    0 < (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).degree?.getD 0 := by
  let : Hex.ZMod64.Bounds data.p := data.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let : Hex.ZMod64.PrimeModulus data.p := Hex.ZMod64.primeModulusOfPrime hprime
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
    unfold Hex.ZPoly.modP
    simpa using Hex.DensePoly.size_ofList_le
      ((List.range f.size).map fun i =>
        Hex.ZMod64.ofNat data.p (Hex.ZPoly.intModNat (f.coeff i) data.p))
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
with the input's positive degree. The deduction from `0 < g.degree?.getD 0` on each
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
  let : Hex.ZMod64.Bounds data.p := data.bounds
  -- Step A: 0 < (monicModularImage (modP data.p f)).degree?.getD 0
  have hmonicImage_pos :
      0 < (Hex.monicModularImage (Hex.ZPoly.modP data.p f)).degree?.getD 0 :=
    monicModularImage_modP_degree?_pos_of_factorsModPBerlekampForm f data hform hgood hf_pos
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield : Hex.ZMod64.PrimeModulus data.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  let : Hex.ZMod64.PrimeModulus data.p := Hex.ZMod64.primeModulusOfPrime hprime
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
    simpa using Hex.DensePoly.size_ofList_le
      ((List.range g.size).map fun i => Int.ofNat (g.coeff i).toNat)
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
theorem monicModularImage_modP_eq_of_monic
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
    unfold Hex.ZPoly.modP
    simpa using Hex.DensePoly.size_ofList_le
      ((List.range core.size).map fun i =>
        Hex.ZMod64.ofNat p (Hex.ZPoly.intModNat (core.coeff i) p))
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
theorem modP_polyProduct_liftToZ_eq_factorProduct
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
  let : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  let : Hex.ZMod64.PrimeModulus primeData.p :=
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
  -- no `hcore_monic` needed here; the monic premise of `factorProduct_berlekampFactor`
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
  let : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
  let : Hex.ZMod64.PrimeModulus primeData.p :=
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
  let : Hex.ZMod64.Bounds primeData.p := primeData.bounds
  obtain ⟨hprime, hzero, heq⟩ := hform
  let hfield : Hex.ZMod64.PrimeModulus primeData.p :=
    Hex.ZMod64.primeModulusOfPrime hprime
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
end

end HexBerlekampZassenhausMathlib
