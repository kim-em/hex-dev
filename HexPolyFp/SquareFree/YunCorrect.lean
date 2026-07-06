/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public meta import HexPolyFp.Degree
public meta import HexModArith.Ring
public import HexModArith.Prime
public import HexPolyFp.Degree
public import HexPolyFp.SquareFree.YunMeasure
import all HexPolyFp.SquareFree.Algebra
import all HexPolyFp.SquareFree.YunContribution
import all HexPolyFp.SquareFree.YunReduce
import all HexPolyFp.SquareFree.YunMeasure

public section
set_option backward.proofsInPublic true

/-!
Terminal Yun-engine correctness: the contribution pow obligations,
pairwise-coprimality of the produced factors, and `factors_squareFree`.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]
/--
Remaining assembly obligation for the derivative-active branch: the level-form
Yun invariant identifies the local contribution and residual product, while
the recursive IH closes the nontrivial repeated tail.
-/
private theorem squareFreeAuxRevContribution_derivative_active_pow_obligation
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (_hreachable : squareFreeContributionReachable f)
    (_hresidual : squareFreeAuxRevResidualSatisfied f multiplicity (fuel + 1))
    (hrawState : YunDerivativeActiveRawStateProvider hp)
    (ih :
      ∀ (f : FpPoly p) (multiplicity : Nat),
        0 < multiplicity →
          f.size < fuel →
            f.isZero = false →
              squareFreeContributionReachable f →
                squareFreeAuxRevResidualSatisfied f multiplicity fuel →
                  squareFreeAuxRevContribution f multiplicity fuel =
                    pow f multiplicity) :
    squareFreeAuxRevContribution f multiplicity (fuel + 1) = pow f multiplicity := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
  have hlevelState : YunDerivativeActiveLevelStateProvider hp :=
    YunDerivativeActiveRawStateProvider.levelState hp hrawState
  have hrawTail : YunDerivativeActiveRawTailProvider hp :=
    YunDerivativeActiveRawStateProvider.rawTail hp hrawState
  have hpow_contribution :
      contribution.1 * pow contribution.2 multiplicity = pow f multiplicity := by
    simpa [c, g, contribution] using
      yunFactorsContributionWithLevel_raw_pow_invariant
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf hlevelState
  have _hpow_normalized :
      contribution.1 *
          (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
            pow (normalizeMonic contribution.2).2 multiplicity) =
        pow f multiplicity := by
    simpa [c, g, contribution] using
      yunFactorsContributionWithLevel_normalized_pow_invariant
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf
        (yunFactorsDerivativeActiveReachable_normalized_stateProvider hp) (by
          simpa [c, g, contribution] using hpow_contribution)
  have hresidual_unpacked :
      let loop := yunFactorsWithLevel c g multiplicity 1 fuel []
      ((isOne loop.2 = true) ∨ (DensePoly.derivative loop.2).isZero = true) ∧
        ((isOne loop.2 = false) →
          squareFreeAuxRevResidualSatisfied
            (pthRoot loop.2) (multiplicity * p) fuel) := by
    have h := _hresidual
    simp only [squareFreeAuxRevResidualSatisfied] at h
    rw [if_neg (by simp [hzero]), if_neg (by simp [hdf])] at h
    simpa [c, g, Nat.mul_one] using h
  have hloop_eq :
      (yunFactorsWithLevel c g multiplicity 1 fuel []).2 = contribution.2 := by
    have hrec :=
      yunFactorsWithLevel_reconstruction_invariant c g multiplicity 1 fuel []
    simpa [contribution] using hrec.1
  simp only [squareFreeAuxRevContribution]
  rw [if_neg (by simp [hzero]), if_neg (by simp [hdf])]
  by_cases hone : isOne contribution.2 = true
  · have hcontribution_eq_one : contribution.2 = 1 :=
      eq_one_of_isOne_true contribution.2 hone
    rw [hcontribution_eq_one, isOne_one]
    simp [c, g, contribution, hcontribution_eq_one, pow_one_base] at hpow_contribution ⊢
    exact hpow_contribution
  · have hone_false : isOne contribution.2 = false := by
      cases h : isOne contribution.2
      · rfl
      · exact False.elim (hone h)
    rw [hone_false]
    have hloop_one_false :
        isOne (yunFactorsWithLevel c g multiplicity 1 fuel []).2 = false := by
      rw [hloop_eq]
      exact hone_false
    have htail_residual :
        squareFreeAuxRevResidualSatisfied
          (pthRoot contribution.2) (multiplicity * p) fuel := by
      have h := hresidual_unpacked.2 hloop_one_false
      simpa [hloop_eq] using h
    have htail_derivative :
        (DensePoly.derivative contribution.2).isZero = true := by
      rcases hresidual_unpacked.1 with hloop_one | hloop_derivative
      · rw [hloop_eq] at hloop_one
        rw [hloop_one] at hone_false
        cases hone_false
      · simpa [hloop_eq] using hloop_derivative
    have hinitial_reachable :
        yunFactorsDerivativeActiveReachable hp f c g fuel := by
      have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
        intro htrue
        rw [htrue] at hdf
        cases hdf
      simpa [c, g] using
        yunFactorsDerivativeActiveReachable_of_derivative_split hp f fuel hdf_ne_true
    have htail_fuel : contribution.2.size < fuel + 1 := by
      have hloop_dvd_g :
          (yunFactorsWithLevel c g multiplicity 1 fuel []).2 ∣ g := by
        exact yunFactorsWithLevel_repeated_dvd_repeated c g multiplicity 1 fuel
      have hg_dvd_f : g ∣ f := by
        simpa [g] using monicGcd_dvd_left hp f (DensePoly.derivative f)
      have hcontribution_dvd_f : contribution.2 ∣ f := by
        rw [← hloop_eq]
        exact dvd_trans_poly hloop_dvd_g hg_dvd_f
      have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
      have hsize_le : contribution.2.size ≤ f.size :=
        size_le_of_dvd_of_ne_zero hcontribution_dvd_f hf_ne
      omega
    have htail_raw_valid :=
      hrawTail f c g multiplicity 1 fuel hinitial_reachable
    have htail_nonzero : contribution.2.isZero = false :=
      htail_raw_valid.2.1
    have htail_valid :=
      htail_raw_valid.2.2 htail_fuel hone_false htail_derivative
    have htail_normalized_nontrivial :
        isOne (normalizeMonic contribution.2).2 = false :=
      normalizeMonic_isOne_false_of_isOne_false
        hp contribution.2 htail_nonzero htail_raw_valid.1 hone_false
    have htail_normalized_valid :=
      yunFactorsContributionWithLevel_normalized_pthRoot_tail_valid
        hp f c g multiplicity 1 fuel
        (yunFactorsDerivativeActiveReachable_normalized_stateProvider hp)
        hinitial_reachable htail_fuel htail_normalized_nontrivial htail_derivative
    have hmultiplicity_tail : 0 < multiplicity * p := by
      have hp_pos : 0 < p := by
        have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
        omega
      exact Nat.mul_pos hmultiplicity hp_pos
    have htail_normalized_residual :
        squareFreeAuxRevResidualSatisfied
          (pthRoot (normalizeMonic contribution.2).2) (multiplicity * p) fuel :=
      squareFreeAuxRevResidualSatisfied_of_size_lt hp
        (pthRoot (normalizeMonic contribution.2).2) (multiplicity * p) fuel
        htail_normalized_valid.2.2
    have htail_normalized_correct :
        squareFreeAuxRevContribution (pthRoot (normalizeMonic contribution.2).2)
            (multiplicity * p) fuel =
          pow (pthRoot (normalizeMonic contribution.2).2) (multiplicity * p) :=
      ih (pthRoot (normalizeMonic contribution.2).2) (multiplicity * p)
        hmultiplicity_tail htail_normalized_valid.2.2 htail_normalized_valid.2.1
        htail_normalized_valid.1 htail_normalized_residual
    exact
      derivative_active_raw_tail_weighted_product_bridge_via_normalized
        hp f contribution.2 contribution.1 multiplicity fuel hmultiplicity
        htail_nonzero htail_derivative htail_valid.1 htail_valid.2.1
        htail_valid.2.2 htail_residual ih htail_normalized_correct hpow_contribution

private theorem squareFreeAuxRevContribution_correct_pow_of_nonzero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel)
    (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f)
    (hresidual : squareFreeAuxRevResidualSatisfied f multiplicity fuel)
    (hrawState : YunDerivativeActiveRawStateProvider hp) :
    squareFreeAuxRevContribution f multiplicity fuel = pow f multiplicity := by
  induction fuel generalizing f multiplicity with
  | zero =>
      omega
  | succ fuel ih =>
      simp only [squareFreeAuxRevContribution]
      simp [hzero]
      by_cases hdf : (DensePoly.derivative f).isZero
      · simpa [hdf] using
          squareFreeAuxRevContribution_derivative_zero_correct
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf (by
              have hmultiplicity_root : 0 < multiplicity * p := by
                have hp_pos : 0 < p := by
                  have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
                  omega
                exact Nat.mul_pos hmultiplicity hp_pos
              by_cases hconstant : f.size = 1
              · have hf_one : f = 1 := hreachable hconstant
                subst f
                exact squareFreeAuxRevContribution_pthRoot_constant_correct
                  hp (multiplicity * p) fuel
              · have hnonconstant : 1 < f.size := by
                  have hpos := size_pos_of_isZero_false f hzero
                  omega
                have hroot_fuel : (pthRoot f).size < fuel :=
                  pthRoot_fuel_decrease_of_derivative_zero_nonconstant
                    hp f hfuel hnonconstant
                have hroot_zero : (pthRoot f).isZero = false :=
                  pthRoot_nonzero_of_derivative_zero_nonconstant
                    hp f hzero hdf hnonconstant
                have hroot_reachable : squareFreeContributionReachable (pthRoot f) :=
                  pthRoot_reachable_of_derivative_zero
                    hp f hzero hdf hreachable
                have hroot_residual :
                    squareFreeAuxRevResidualSatisfied (pthRoot f) (multiplicity * p) fuel := by
                  have h := hresidual
                  simp only [squareFreeAuxRevResidualSatisfied] at h
                  rw [if_neg (by simp [hzero]), if_pos hdf] at h
                  exact h
                exact ih (pthRoot f) (multiplicity * p)
                  hmultiplicity_root hroot_fuel hroot_zero hroot_reachable hroot_residual)
      · have hdf_false : (DensePoly.derivative f).isZero = false := by
          cases h : (DensePoly.derivative f).isZero <;> simp [h] at hdf ⊢
        simpa [squareFreeAuxRevContribution, hzero, hdf_false] using
          squareFreeAuxRevContribution_derivative_active_pow_obligation
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf_false hreachable hresidual
            hrawState ih

private theorem yunFactorsWithLevel_factor_mem_acc_or_dvd_current
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (accRev : List (SquareFreeFactor p)) :
    ∀ sf ∈ (yunFactorsWithLevel c w base level fuel accRev).1,
      sf ∈ accRev ∨ sf.factor ∣ c := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  induction fuel generalizing c w level accRev with
  | zero =>
      intro sf hsf
      exact Or.inl hsf
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
        intro sf hsf
        exact Or.inl hsf
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        have hy_dvd_c : y ∣ c := by
          simpa [y] using monicGcd_dvd_left hp c w
        have hz_dvd_c : z ∣ c := by
          refine ⟨y, ?_⟩
          simpa [y, z] using (div_monicGcd_mul_reconstruct hp c w).symm
        by_cases hz : isOne z
        · intro sf hsf
          have htail :=
            ih y (w / y) (level + 1) accRev sf (by
              simpa [y, z, hz] using hsf)
          rcases htail with hacc | hsf_y
          · exact Or.inl hacc
          · exact Or.inr (dvd_trans_poly hsf_y hy_dvd_c)
        · let current : SquareFreeFactor p :=
            { factor := z, multiplicity := base * level }
          intro sf hsf
          have htail :=
            ih y (w / y) (level + 1) (current :: accRev) sf (by
              simpa [y, z, hz, current] using hsf)
          rcases htail with hacc | hsf_y
          · simp only [List.mem_cons] at hacc
            rcases hacc with hcurrent | haccRev
            · subst sf
              exact Or.inr hz_dvd_c
            · exact Or.inl haccRev
          · exact Or.inr (dvd_trans_poly hsf_y hy_dvd_c)

private theorem yunFactorsWithLevel_factor_dvd_current
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat) :
    ∀ sf ∈ (yunFactorsWithLevel c w base level fuel []).1.reverse,
      sf.factor ∣ c := by
  intro sf hsf
  have hsf' : sf ∈ (yunFactorsWithLevel c w base level fuel []).1 :=
    List.mem_reverse.mp hsf
  have h := yunFactorsWithLevel_factor_mem_acc_or_dvd_current
    c w base level fuel [] sf hsf'
  simpa using h

private theorem yunStep_quotient_factor_coprime_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (z y factor : FpPoly p) (multiplicity tailMultiplicity : Nat)
    (hfactor_dvd_y : factor ∣ y)
    (hcommon :
      ∀ d : FpPoly p, d ∣ z → d ∣ y → d ∣ (1 : FpPoly p)) :
    squareFreeFactorCoprimeRel
      { factor := z, multiplicity := multiplicity }
      { factor := factor, multiplicity := tailMultiplicity } := by
  have hgcd_dvd_one :
      DensePoly.gcd z factor ∣ (1 : FpPoly p) :=
    hcommon (DensePoly.gcd z factor)
      (DensePoly.gcd_dvd_left z factor)
      (dvd_trans_poly (DensePoly.gcd_dvd_right z factor) hfactor_dvd_y)
  have hnormalized := normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one
  simpa [squareFreeFactorCoprimeRel] using hnormalized

private theorem yunStep_quotient_right_factor_coprime_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w factor : FpPoly p) (multiplicity tailMultiplicity : Nat)
    (hfactor_dvd_w : factor ∣ w)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / monicGcd c w →
          d ∣ monicGcd c w →
            d ∣ (1 : FpPoly p)) :
    squareFreeFactorCoprimeRel
      { factor := c / monicGcd c w, multiplicity := multiplicity }
      { factor := factor, multiplicity := tailMultiplicity } := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  let z := c / monicGcd c w
  let y := monicGcd c w
  have hz_dvd_c : z ∣ c := by
    refine ⟨y, ?_⟩
    simpa [z, y] using (div_monicGcd_mul_reconstruct hp c w).symm
  have hgcd_dvd_y :
      DensePoly.gcd z factor ∣ y := by
    apply dvd_monicGcd hp
    · exact dvd_trans_poly (DensePoly.gcd_dvd_left z factor) hz_dvd_c
    · exact dvd_trans_poly (DensePoly.gcd_dvd_right z factor) hfactor_dvd_w
  have hgcd_dvd_one :
      DensePoly.gcd z factor ∣ (1 : FpPoly p) :=
    hcommon (DensePoly.gcd z factor)
      (DensePoly.gcd_dvd_left z factor)
      (by simpa [z, y] using hgcd_dvd_y)
  have hnormalized := normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one
  simpa [squareFreeFactorCoprimeRel, z, y] using hnormalized

private theorem yunFactorsWithLevel_current_tail_coprime_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / monicGcd c w →
          d ∣ monicGcd c w →
            d ∣ (1 : FpPoly p)) :
    yunFactorsCurrentTailCoprime c w base level fuel := by
  intro sf hsf
  have hsf_dvd_current :
      sf.factor ∣ monicGcd c w := by
    exact yunFactorsWithLevel_factor_dvd_current
      (monicGcd c w) (w / monicGcd c w) base (level + 1) fuel sf hsf
  exact
    yunStep_quotient_factor_coprime_of_common_dvd_one
      (c / monicGcd c w) (monicGcd c w) sf.factor (base * level) sf.multiplicity
      hsf_dvd_current
      hcommon

private theorem yunFactorsWithLevel_current_repeated_coprime_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / monicGcd c w →
          d ∣ monicGcd c w →
            d ∣ (1 : FpPoly p)) :
    let tail :=
      yunFactorsWithLevel
        (monicGcd c w)
        (w / monicGcd c w)
        base
        (level + 1)
        fuel
        []
    squareFreeFactorCoprimeRel
      { factor := c / monicGcd c w, multiplicity := base * level }
      { factor := tail.2, multiplicity := base * level * p } := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  dsimp
  have htail_dvd :
      (yunFactorsWithLevel
        (monicGcd c w)
        (w / monicGcd c w)
        base
        (level + 1)
        fuel
        []).2 ∣ w / monicGcd c w := by
    exact yunFactorsWithLevel_repeated_dvd_repeated
      (monicGcd c w)
      (w / monicGcd c w)
      base
      (level + 1)
      fuel
  have hright_dvd : w / monicGcd c w ∣ w := by
    exact ⟨monicGcd c w, (div_monicGcd_right_mul_reconstruct hp c w).symm⟩
  exact
    yunStep_quotient_right_factor_coprime_of_common_dvd_one
      c w
      (yunFactorsWithLevel
        (monicGcd c w)
        (w / monicGcd c w)
        base
        (level + 1)
        fuel
        []).2
      (base * level)
      (base * level * p)
      (dvd_trans_poly htail_dvd hright_dvd)
      hcommon

set_option maxHeartbeats 800000 in
private theorem yunFactorsWithLevel_factors_coprime_repeated_of_reachable
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel) :
    let loop := yunFactorsWithLevel c w base level fuel []
    ∀ a ∈ loop.1.reverse,
      squareFreeFactorCoprimeRel
        a { factor := loop.2, multiplicity := base * level * p } := by
  induction fuel generalizing c w level with
  | zero =>
      simp [yunFactorsWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
        let tail := yunFactorsWithLevel y (w / y) base (level + 1) fuel []
        have htail_reachable :
            yunFactorsPairwiseReachable y (w / y) fuel := by
          simpa [y] using yunFactorsPairwiseReachable_step c w fuel hreachable
        have htail_cross :
            ∀ a ∈ tail.1.reverse,
              squareFreeFactorCoprimeRel
                a { factor := tail.2, multiplicity := base * (level + 1) * p } := by
          simpa [tail] using ih y (w / y) (level + 1) htail_reachable
        by_cases hz : isOne z
        · simpa [y, z, tail, hz, squareFreeFactorCoprimeRel] using htail_cross
        · have hrev :
              (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).1.reverse =
                [sf] ++ tail.1.reverse := by
            simpa [sf, tail] using
              yunFactorsWithLevel_reverse_append y (w / y) base (level + 1) fuel [sf]
          have hrepeated :
              (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).2 = tail.2 := by
            simpa [sf, tail] using
              yunFactorsWithLevel_repeated_eq_nil y (w / y) base (level + 1) fuel [sf]
          have hsf_cross :
              squareFreeFactorCoprimeRel
                sf { factor := tail.2, multiplicity := base * level * p } := by
            simpa [y, z, sf, tail] using
              yunFactorsWithLevel_current_repeated_coprime_of_common_dvd_one
                c w base level fuel
                (yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable)
          intro a ha
          have ha_rev :
              a ∈ (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).1.reverse := by
            apply List.mem_reverse.mpr
            simpa [y, z, sf, hz] using ha
          rw [hrev] at ha_rev
          rcases List.mem_append.mp ha_rev with ha | ha
          · simp only [List.mem_singleton] at ha
            subst a
            simpa [y, z, sf, hz, hrepeated] using hsf_cross
          · have htail_a := htail_cross a ha
            simpa [y, z, sf, hz, hrepeated, squareFreeFactorCoprimeRel] using htail_a

private theorem yunFactorsPairwiseReady_succ_of_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (htail :
      yunFactorsPairwiseReady
        (monicGcd c w)
        (w / monicGcd c w)
        base
        (level + 1)
        fuel)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / monicGcd c w →
          d ∣ monicGcd c w →
            d ∣ (1 : FpPoly p)) :
    yunFactorsPairwiseReady c w base level (fuel + 1) := by
  apply yunFactorsPairwiseReady_succ_of_current_tail c w base level fuel htail
  intro _hc _hz
  exact yunFactorsWithLevel_current_tail_coprime_of_common_dvd_one
    c w base level fuel hcommon

private theorem yunFactorsPairwiseReady_of_reachable_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hcommon :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsPairwiseReachable c w (fuel + 1) →
          ∀ d : FpPoly p,
            d ∣ c / monicGcd c w →
              d ∣ monicGcd c w →
                d ∣ (1 : FpPoly p)) :
    yunFactorsPairwiseReady c w base level fuel := by
  induction fuel generalizing c w level with
  | zero =>
      simp [yunFactorsPairwiseReady]
  | succ fuel ih =>
      have htail :
          yunFactorsPairwiseReady
            (monicGcd c w)
            (w / monicGcd c w)
            base
            (level + 1)
            fuel := by
        exact ih
          (monicGcd c w)
          (w / monicGcd c w)
          (level + 1)
          (yunFactorsPairwiseReachable_step c w fuel hreachable)
      exact
        yunFactorsPairwiseReady_succ_of_common_dvd_one
          c w base level fuel htail
          (hcommon c w fuel hreachable)

private theorem yunFactorsPairwiseReady_of_derivative_split_common_dvd_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hcommon :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsPairwiseReachable c w (fuel + 1) →
          ∀ d : FpPoly p,
            d ∣ c / monicGcd c w →
              d ∣ monicGcd c w →
                d ∣ (1 : FpPoly p)) :
    yunFactorsPairwiseReady
      (f / monicGcd f (DensePoly.derivative f))
      (monicGcd f (DensePoly.derivative f))
      base
      level
      fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact
    yunFactorsPairwiseReady_of_reachable_common_dvd_one
      (f / monicGcd f (DensePoly.derivative f))
      (monicGcd f (DensePoly.derivative f))
      base level fuel
      (yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf)
      hcommon

private theorem yunFactorsPairwiseInvariant_of_derivative_split_common_dvd_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hcommon :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsPairwiseReachable c w (fuel + 1) →
          ∀ d : FpPoly p,
            d ∣ c / monicGcd c w →
              d ∣ monicGcd c w →
                d ∣ (1 : FpPoly p)) :
    yunFactorsPairwiseInvariant
      (f / monicGcd f (DensePoly.derivative f))
      (monicGcd f (DensePoly.derivative f))
      base
      level
      fuel where
  reachable := yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf
  ready :=
    yunFactorsPairwiseReady_of_derivative_split_common_dvd_one
      hp f base level fuel hdf hcommon

private theorem yunFactorsPairwiseInvariant_of_derivative_split_reachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsPairwiseInvariant
      (f / monicGcd f (DensePoly.derivative f))
      (monicGcd f (DensePoly.derivative f))
      base
      level
      fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact
    yunFactorsPairwiseInvariant_of_derivative_split_common_dvd_one
      hp f base level fuel hdf
      (fun c w fuel hreachable =>
        yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable)

private theorem squareFreeAuxRev_reverse_append
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (squareFreeAuxRev f multiplicity fuel accRev).reverse =
      accRev.reverse ++ (squareFreeAuxRev f multiplicity fuel []).reverse := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simp [squareFreeAuxRev]
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simp [hzero]
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev
        · simp [hdf]
          let g := monicGcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          let loopNil := yunFactorsWithLevel c g multiplicity 1 fuel []
          have hloop_rev :
              loop.1.reverse = accRev.reverse ++ loopNil.1.reverse := by
            simpa [loop, loopNil] using
              yunFactorsWithLevel_reverse_append c g multiplicity 1 fuel accRev
          have hloop_repeated : loop.2 = loopNil.2 := by
            simpa [loop, loopNil] using
              yunFactorsWithLevel_repeated_eq_nil c g multiplicity 1 fuel accRev
          by_cases hrepeated : isOne loop.2
          · have hrepeated_nil : isOne loopNil.2 := by
              simpa [hloop_repeated] using hrepeated
            simpa [g, c, loop, loopNil, hrepeated, hrepeated_nil] using hloop_rev
          · have hrepeated_nil : isOne loopNil.2 = false := by
              cases h : isOne loopNil.2
              · exact rfl
              · exfalso
                apply hrepeated
                simpa [hloop_repeated] using h
            have hrec_loop :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  loop.1.reverse ++
                    (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse := by
              exact ih (pthRoot loop.2) (multiplicity * p) loop.1
            have hrec_nil :
                (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel loopNil.1).reverse =
                  loopNil.1.reverse ++
                    (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse := by
              exact ih (pthRoot loopNil.2) (multiplicity * p) loopNil.1
            have htail :
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse =
                  (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse := by
              rw [hloop_repeated]
            simpa [g, c, loop, loopNil, hrepeated, hrepeated_nil] using
              (calc
                (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse
                    = loop.1.reverse ++
                        (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse :=
                      hrec_loop
                _ = (accRev.reverse ++ loopNil.1.reverse) ++
                        (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse := by
                      rw [hloop_rev]
                _ = accRev.reverse ++
                      (loopNil.1.reverse ++
                        (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel []).reverse) := by
                      rw [htail]
                      simp [List.append_assoc]
                _ = accRev.reverse ++
                      (squareFreeAuxRev (pthRoot loopNil.2) (multiplicity * p) fuel loopNil.1).reverse := by
                      rw [hrec_nil])

/--
Under the recursive residual derivative-zero invariant, every output factor
of `squareFreeAuxRev g m fuel []` divides `g`. The proof tracks the loop
through both the `pthRoot`-direct branch and the Yun-then-`pthRoot` branch,
relying on `pthRoot_dvd_self_of_derivative_zero` for the `pthRoot` steps and
on `yunFactorsWithLevel_factor_dvd_current` /
`yunFactorsWithLevel_repeated_dvd_repeated` for the Yun steps.
-/
private theorem squareFreeAuxRev_factor_dvd_input
    (hp : Hex.Nat.Prime p) (g : FpPoly p) (m fuel : Nat)
    (hresidual : squareFreeAuxRevResidualSatisfied g m fuel) :
    ∀ b ∈ (squareFreeAuxRev g m fuel []).reverse, b.factor ∣ g := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction fuel generalizing g m with
  | zero =>
      intro b hb
      simp [squareFreeAuxRev] at hb
  | succ fuel ih =>
      intro b hb
      simp only [squareFreeAuxRev] at hb
      by_cases hzero : g.isZero = true
      · simp [hzero] at hb
      · have hzero_false : g.isZero = false := by
          cases h : g.isZero
          · rfl
          · exact False.elim (hzero h)
        rw [if_neg (by simp [hzero_false])] at hb
        by_cases hdf : (DensePoly.derivative g).isZero = true
        · rw [if_pos hdf] at hb
          have hres_pth :
              squareFreeAuxRevResidualSatisfied (pthRoot g) (m * p) fuel := by
            have h := hresidual
            simp only [squareFreeAuxRevResidualSatisfied] at h
            rw [if_neg (by simp [hzero_false]), if_pos hdf] at h
            exact h
          have hb_pth : b.factor ∣ pthRoot g :=
            ih (pthRoot g) (m * p) hres_pth b hb
          have hpth_dvd_g : pthRoot g ∣ g :=
            pthRoot_dvd_self_of_derivative_zero hp g hzero_false hdf
          exact dvd_trans_poly hb_pth hpth_dvd_g
        · have hdf_false : (DensePoly.derivative g).isZero = false := by
            cases h : (DensePoly.derivative g).isZero
            · rfl
            · exact False.elim (hdf h)
          rw [if_neg (by simp [hdf_false])] at hb
          let g_inner := monicGcd g (DensePoly.derivative g)
          let c_inner := g / g_inner
          let loop := yunFactorsWithLevel c_inner g_inner m 1 fuel []
          have hres_unpack :
              ((isOne loop.2 = true) ∨ (DensePoly.derivative loop.2).isZero = true) ∧
                ((isOne loop.2 = false) →
                  squareFreeAuxRevResidualSatisfied
                    (pthRoot loop.2) (m * p) fuel) := by
            have h := hresidual
            simp only [squareFreeAuxRevResidualSatisfied] at h
            rw [if_neg (by simp [hzero_false]), if_neg (by simp [hdf_false])] at h
            exact h
          have hg_inner_dvd_g : g_inner ∣ g :=
            monicGcd_dvd_left hp g (DensePoly.derivative g)
          have hloop_dvd_g_inner : loop.2 ∣ g_inner := by
            simpa [loop] using
              yunFactorsWithLevel_repeated_dvd_repeated c_inner g_inner m 1 fuel
          have hloop_dvd_g : loop.2 ∣ g :=
            dvd_trans_poly hloop_dvd_g_inner hg_inner_dvd_g
          have hc_inner_dvd_g : c_inner ∣ g := by
            refine ⟨g_inner, ?_⟩
            simpa [c_inner, g_inner] using
              (div_monicGcd_mul_reconstruct hp g (DensePoly.derivative g)).symm
          have hg_inner_ne : g_inner.isZero = false :=
            monicGcd_isZero_false_of_gcd_nonzero g (DensePoly.derivative g)
              (gcd_isZero_false_of_right_isZero_false g
                (DensePoly.derivative g) hdf_false)
          have hloop_ne : loop.2.isZero = false := by
            cases hl : loop.2.isZero
            · rfl
            · exfalso
              have hloop_zero : loop.2 = 0 :=
                eq_zero_of_isZero_true loop.2 hl
              rcases hloop_dvd_g_inner with ⟨q, hq⟩
              have hg_inner_zero : g_inner = 0 := by
                rw [hq, hloop_zero, zero_mul]
              have hg_inner_isZero : g_inner.isZero = true := by
                rw [hg_inner_zero]; rfl
              rw [hg_inner_isZero] at hg_inner_ne
              cases hg_inner_ne
          by_cases hrep : isOne loop.2 = true
          · have hb_loop : b ∈ loop.1.reverse := by
              simpa [g_inner, c_inner, loop, hrep] using hb
            have hb_dvd_c : b.factor ∣ c_inner :=
              yunFactorsWithLevel_factor_dvd_current
                c_inner g_inner m 1 fuel b hb_loop
            exact dvd_trans_poly hb_dvd_c hc_inner_dvd_g
          · have hrep_false : isOne loop.2 = false := by
              cases h : isOne loop.2
              · rfl
              · exact False.elim (hrep h)
            have hres_inner :
                squareFreeAuxRevResidualSatisfied
                  (pthRoot loop.2) (m * p) fuel := hres_unpack.2 hrep_false
            have hb' :
                b ∈ (squareFreeAuxRev (pthRoot loop.2) (m * p) fuel loop.1).reverse := by
              simpa [g_inner, c_inner, loop, hrep_false] using hb
            rw [squareFreeAuxRev_reverse_append] at hb'
            rcases List.mem_append.mp hb' with hb_loop | hb_rec
            · have hb_dvd_c : b.factor ∣ c_inner :=
                yunFactorsWithLevel_factor_dvd_current
                  c_inner g_inner m 1 fuel b hb_loop
              exact dvd_trans_poly hb_dvd_c hc_inner_dvd_g
            · have hb_pth : b.factor ∣ pthRoot loop.2 :=
                ih (pthRoot loop.2) (m * p) hres_inner b hb_rec
              have hdf_loop : (DensePoly.derivative loop.2).isZero = true := by
                rcases hres_unpack.1 with h | h
                · rw [h] at hrep_false; cases hrep_false
                · exact h
              have hpth_dvd_loop : pthRoot loop.2 ∣ loop.2 :=
                pthRoot_dvd_self_of_derivative_zero hp loop.2 hloop_ne hdf_loop
              exact dvd_trans_poly hb_pth (dvd_trans_poly hpth_dvd_loop hloop_dvd_g)

private theorem yunFactorsWithLevel_pairwise_coprime_nil_of_ready
    (c w : FpPoly p) (base level fuel : Nat)
    (hready : yunFactorsPairwiseReady c w base level fuel) :
    (yunFactorsWithLevel c w base level fuel []).1.reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  induction fuel generalizing c w level with
  | zero =>
      simp [yunFactorsWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        have hc_false : isOne c = false := by
          cases h : isOne c with
          | false => rfl
          | true => exact False.elim (hc h)
        let y := monicGcd c w
        let z := c / y
        have hready_unpack :
            yunFactorsPairwiseReady y (w / y) base (level + 1) fuel ∧
              (isOne c = false →
                isOne z = false →
                  yunFactorsCurrentTailCoprime c w base level fuel) := by
          simpa [yunFactorsPairwiseReady, y, z] using hready
        have htail :
            (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse.Pairwise
              squareFreeFactorCoprimeRel :=
          ih y (w / y) (level + 1) hready_unpack.1
        by_cases hz : isOne z
        · simpa [y, z, hz] using htail
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
          have hz_false : isOne z = false := by
            cases h : isOne z with
            | false => rfl
            | true => exact False.elim (hz h)
          have hcross :
              ∀ tailSf ∈
                  (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse,
                squareFreeFactorCoprimeRel sf tailSf := by
            simpa [yunFactorsCurrentTailCoprime, y, z, sf] using
              hready_unpack.2 hc_false hz_false
          have hsingle :
              [sf].Pairwise squareFreeFactorCoprimeRel := by
            simp
          have hcombined :
              ([sf] ++
                  (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse).Pairwise
                squareFreeFactorCoprimeRel := by
            apply pairwise_append_of_cross squareFreeFactorCoprimeRel hsingle htail
            intro headSf hhead tailSf htailSf
            simp only [List.mem_singleton] at hhead
            subst headSf
            exact hcross tailSf htailSf
          have hrev :
              (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).1.reverse =
                [sf] ++
                  (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse := by
            simpa [sf] using
              yunFactorsWithLevel_reverse_append y (w / y) base (level + 1) fuel [sf]
          simpa [y, z, hz, sf, hrev] using hcombined

private theorem yunFactorsWithLevel_pairwise_coprime_nil_of_invariant
    (c w : FpPoly p) (base level fuel : Nat)
    (hinv : yunFactorsPairwiseInvariant c w base level fuel) :
    (yunFactorsWithLevel c w base level fuel []).1.reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact yunFactorsWithLevel_pairwise_coprime_nil_of_ready c w base level fuel hinv.ready

private theorem yunFactorsWithLevel_pairwise_coprime_nil
    (c w : FpPoly p) (base level fuel : Nat)
    (hinv : yunFactorsPairwiseInvariant c w base level fuel) :
    (yunFactorsWithLevel c w base level fuel []).1.reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact yunFactorsWithLevel_pairwise_coprime_nil_of_invariant c w base level fuel hinv

/--
The residual invariant holds trivially on the unit polynomial: every recursive
step descends through the derivative-zero branch (since `derivative 1 = 0`)
into `pthRoot 1 = 1`, so the predicate is preserved until fuel runs out.
-/
private theorem squareFreeAuxRevResidualSatisfied_one
    (hp : Hex.Nat.Prime p) (m fuel : Nat) :
    squareFreeAuxRevResidualSatisfied (1 : FpPoly p) m fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction fuel generalizing m with
  | zero => trivial
  | succ fuel ih =>
      simp only [squareFreeAuxRevResidualSatisfied]
      have hone_ne : (1 : FpPoly p).isZero = false := by
        have hcoeffs : (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        simp [DensePoly.isZero, hcoeffs]
      have hdf_one : (DensePoly.derivative (1 : FpPoly p)).isZero = true := by
        have hcoeffs : (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        have hsize : (1 : FpPoly p).size = 1 := by
          simpa [DensePoly.size] using congrArg Array.size hcoeffs
        rw [DensePoly.isZero_eq_true_iff]
        have h := DensePoly.size_derivative_le (1 : FpPoly p)
        omega
      rw [if_neg (by simp [hone_ne]), if_pos hdf_one, pthRoot_one hp]
      exact ih (m * p)

private theorem yunFactorsWithLevel_squareFreeAuxRev_tail_cross_coprime
    (hp : Hex.Nat.Prime p)
    (c w : FpPoly p) (base level fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hresidual :
      ((isOne (yunFactorsWithLevel c w base level fuel []).2 = true) ∨
        (DensePoly.derivative
            (yunFactorsWithLevel c w base level fuel []).2).isZero = true) ∧
        ((isOne (yunFactorsWithLevel c w base level fuel []).2 = false) →
          squareFreeAuxRevResidualSatisfied
            (pthRoot (yunFactorsWithLevel c w base level fuel []).2)
            (base * level * p) fuel)) :
    ∀ a ∈ (yunFactorsWithLevel c w base level fuel []).1.reverse,
      ∀ b ∈ (squareFreeAuxRev
              (pthRoot (yunFactorsWithLevel c w base level fuel []).2)
              (base * level * p) fuel []).reverse,
        squareFreeFactorCoprimeRel a b := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro a ha b hb
  have ha_coprime :
      squareFreeFactorCoprimeRel
        a { factor := (yunFactorsWithLevel c w base level fuel []).2,
            multiplicity := base * level * p } :=
    yunFactorsWithLevel_factors_coprime_repeated_of_reachable
      c w base level fuel hreachable a ha
  have ha_gcd_dvd_one :
      DensePoly.gcd a.factor (yunFactorsWithLevel c w base level fuel []).2
        ∣ (1 : FpPoly p) := by
    apply dvd_one_of_normalizeMonic_eq_one
    simpa [squareFreeFactorCoprimeRel] using ha_coprime
  have hb_dvd_loop :
      b.factor ∣ (yunFactorsWithLevel c w base level fuel []).2 := by
    by_cases hone :
        isOne (yunFactorsWithLevel c w base level fuel []).2 = true
    · have hloop_eq_one :
          (yunFactorsWithLevel c w base level fuel []).2 = 1 :=
        eq_one_of_isOne_true _ hone
      have hres_one :
          squareFreeAuxRevResidualSatisfied
            (pthRoot (yunFactorsWithLevel c w base level fuel []).2)
            (base * level * p) fuel := by
        rw [hloop_eq_one, pthRoot_one hp]
        exact squareFreeAuxRevResidualSatisfied_one hp (base * level * p) fuel
      have hb_dvd_pth :
          b.factor ∣ pthRoot (yunFactorsWithLevel c w base level fuel []).2 :=
        squareFreeAuxRev_factor_dvd_input hp _ _ _ hres_one b hb
      rw [hloop_eq_one] at hb_dvd_pth
      rw [pthRoot_one hp] at hb_dvd_pth
      rw [hloop_eq_one]
      exact hb_dvd_pth
    · have hone_false :
          isOne (yunFactorsWithLevel c w base level fuel []).2 = false := by
        cases h : isOne (yunFactorsWithLevel c w base level fuel []).2 with
        | false => rfl
        | true => exact False.elim (hone h)
      have hres_satisfied :
          squareFreeAuxRevResidualSatisfied
            (pthRoot (yunFactorsWithLevel c w base level fuel []).2)
            (base * level * p) fuel := hresidual.2 hone_false
      have hloop_deriv_zero :
          (DensePoly.derivative
            (yunFactorsWithLevel c w base level fuel []).2).isZero = true := by
        rcases hresidual.1 with h | h
        · rw [h] at hone_false; cases hone_false
        · exact h
      have hb_dvd_pth :
          b.factor ∣ pthRoot (yunFactorsWithLevel c w base level fuel []).2 :=
        squareFreeAuxRev_factor_dvd_input hp _ _ _ hres_satisfied b hb
      have hpth_dvd_loop :
          pthRoot (yunFactorsWithLevel c w base level fuel []).2
            ∣ (yunFactorsWithLevel c w base level fuel []).2 := by
        by_cases hloop_zero :
            (yunFactorsWithLevel c w base level fuel []).2.isZero = true
        · have hloop_eq_zero :
              (yunFactorsWithLevel c w base level fuel []).2 = 0 :=
            eq_zero_of_isZero_true _ hloop_zero
          rw [hloop_eq_zero]
          refine ⟨0, ?_⟩
          rw [mul_zero]
        · have hloop_ne :
              (yunFactorsWithLevel c w base level fuel []).2.isZero = false := by
            cases h : (yunFactorsWithLevel c w base level fuel []).2.isZero with
            | false => rfl
            | true => exact False.elim (hloop_zero h)
          exact pthRoot_dvd_self_of_derivative_zero hp _ hloop_ne hloop_deriv_zero
      exact dvd_trans_poly hb_dvd_pth hpth_dvd_loop
  have hgcd_dvd :
      DensePoly.gcd a.factor b.factor
        ∣ DensePoly.gcd a.factor (yunFactorsWithLevel c w base level fuel []).2 := by
    apply DensePoly.dvd_gcd
    · exact DensePoly.gcd_dvd_left a.factor b.factor
    · exact dvd_trans_poly (DensePoly.gcd_dvd_right a.factor b.factor) hb_dvd_loop
  have hgcd_dvd_one :
      DensePoly.gcd a.factor b.factor ∣ (1 : FpPoly p) :=
    dvd_trans_poly hgcd_dvd ha_gcd_dvd_one
  have hnormalized := normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one
  simpa [squareFreeFactorCoprimeRel] using hnormalized

/-- A size-`≤ 1` input produces no factors: it is a nonzero constant (or zero),
so the loop only ever descends through the derivative-zero `pthRoot` branch,
which keeps the size `≤ 1` and never conses a factor. -/
private theorem squareFreeAuxRev_eq_nil_of_size_le_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hsize : f.size ≤ 1) :
    squareFreeAuxRev f multiplicity fuel [] = [] := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction fuel generalizing f multiplicity with
  | zero => rfl
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simp [hzero]
      · have hzero_false : f.isZero = false := by
          cases h : f.isZero
          · rfl
          · exact False.elim (hzero h)
        have hsize_one : f.size = 1 := by
          have hpos := size_pos_of_isZero_false f hzero_false
          omega
        have hdf : (DensePoly.derivative f).isZero = true :=
          derivative_isZero_true_of_size_one f hsize_one
        simp only [hzero, Bool.false_eq_true, if_false, hdf, if_true]
        apply ih
        have h := pthRoot_size_of_derivative_zero hp f hzero_false hdf
        rw [hsize_one, Nat.sub_self, Nat.zero_div] at h
        omega

private theorem squareFreeAuxRev_pairwise_coprime_nil_core_of_yun_invariant
    (hp : Hex.Nat.Prime p)
    (yunInvariant :
      ∀ f : FpPoly p, ∀ base fuel : Nat,
        (DensePoly.derivative f).isZero = false →
          yunFactorsPairwiseInvariant
            (f / monicGcd f (DensePoly.derivative f))
            (monicGcd f (DensePoly.derivative f))
            base
            1
            fuel)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  suffices h : ∀ fuel (f : FpPoly p) (multiplicity : Nat), f.size < fuel →
      (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
        squareFreeFactorCoprimeRel from
    h fuel f multiplicity hfuel
  clear hfuel multiplicity f fuel
  intro fuel
  induction fuel with
  | zero =>
      intro f multiplicity hfuel
      exact absurd hfuel (by omega)
  | succ fuel ih =>
      intro f multiplicity hfuel
      by_cases hsize1 : f.size ≤ 1
      · rw [squareFreeAuxRev_eq_nil_of_size_le_one hp f multiplicity (fuel + 1) hsize1]
        simp
      · have hnonconst : 1 < f.size := by omega
        simp only [squareFreeAuxRev]
        by_cases hzero : f.isZero
        · simp [hzero]
        · simp [hzero]
          have hzero_false : f.isZero = false := by
            cases h : f.isZero
            · rfl
            · exact False.elim (hzero h)
          by_cases hdf : (DensePoly.derivative f).isZero
          · have hroot : (pthRoot f).size < fuel :=
              pthRoot_fuel_decrease_of_derivative_zero_nonconstant hp f hfuel hnonconst
            simpa [hdf] using ih (pthRoot f) (multiplicity * p) hroot
          · simp [hdf]
            let g := monicGcd f (DensePoly.derivative f)
            let c := f / g
            let loop := yunFactorsWithLevel c g multiplicity 1 fuel []
            have hdf_false : (DensePoly.derivative f).isZero = false := by
              cases h : (DensePoly.derivative f).isZero
              · rfl
              · exact False.elim (hdf h)
            have hreachable : yunFactorsDerivativeActiveReachable hp f c g fuel :=
              yunFactorsDerivativeActiveReachable.derivativeSplit fuel (by simp [hdf_false])
            have hstate : ∀ c w : FpPoly p, ∀ fuel : Nat,
                yunFactorsDerivativeActiveReachable hp f c w fuel →
                  squareFreeContributionReachable c ∧ c.isZero = false ∧
                    squareFreeContributionReachable w ∧ w.isZero = false :=
              fun c w fuel' hr =>
                yunDerivativeActiveRawStateProvider_holds hp f c w fuel' hr
            have hinv :
                yunFactorsPairwiseInvariant c g multiplicity 1 fuel := by
              simpa [c, g] using yunInvariant f multiplicity fuel hdf_false
            have hres_unfolded :
                ((isOne (yunFactorsWithLevel c g multiplicity 1 fuel []).2 = true) ∨
                  (DensePoly.derivative
                    (yunFactorsWithLevel c g multiplicity 1 fuel []).2).isZero = true) ∧
                  ((isOne (yunFactorsWithLevel c g multiplicity 1 fuel []).2 = false) →
                    squareFreeAuxRevResidualSatisfied
                      (pthRoot (yunFactorsWithLevel c g multiplicity 1 fuel []).2)
                      (multiplicity * 1 * p) fuel) := by
              have hres_full :
                  squareFreeAuxRevResidualSatisfied f multiplicity (fuel + 1) :=
                squareFreeAuxRevResidualSatisfied_of_size_lt hp f multiplicity (fuel + 1) hfuel
              simp only [squareFreeAuxRevResidualSatisfied] at hres_full
              rw [if_neg (by simp [hzero_false]),
                  if_neg (by simp [hdf_false])] at hres_full
              refine ⟨?_, ?_⟩
              · simpa [c, g, Nat.mul_one] using hres_full.1
              · intro hone_false
                simpa [c, g, Nat.mul_one] using hres_full.2 hone_false
            by_cases hrepeated : isOne loop.2
            · simpa [g, c, loop, hrepeated] using
                yunFactorsWithLevel_pairwise_coprime_nil c g multiplicity 1 fuel hinv
            · have hrepeated_false : isOne loop.2 = false := by
                cases h : isOne loop.2
                · rfl
                · exact False.elim (hrepeated h)
              have hloop_deriv :
                  (DensePoly.derivative
                    (yunFactorsWithLevel c g multiplicity 1 fuel []).2).isZero = true := by
                rcases hres_unfolded.1 with h | h
                · rw [hrepeated_false] at h; exact absurd h (by simp)
                · exact h
              have hloop_dvd_f :
                  (yunFactorsWithLevel c g multiplicity 1 fuel []).2 ∣ f :=
                dvd_trans_poly
                  (yunFactorsWithLevel_repeated_dvd_repeated c g multiplicity 1 fuel)
                  (by simpa [g] using monicGcd_dvd_left hp f (DensePoly.derivative f))
              have hloop_bound :
                  (yunFactorsWithLevel c g multiplicity 1 fuel []).2.size < fuel + 1 := by
                have := size_le_of_dvd_of_ne_zero hloop_dvd_f (ne_zero_of_isZero_false hzero_false)
                omega
              have hroot_tail :
                  (pthRoot (yunFactorsWithLevel c g multiplicity 1 fuel []).2).size < fuel :=
                yunFactorsWithLevel_pthRoot_tail_fuel_bound hp f c g multiplicity 1 fuel
                  hstate hreachable hloop_bound hrepeated_false hloop_deriv
              have hloop :
                  loop.1.reverse.Pairwise squareFreeFactorCoprimeRel := by
                simpa [loop] using
                  yunFactorsWithLevel_pairwise_coprime_nil c g multiplicity 1 fuel hinv
              have htail :
                  (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse.Pairwise
                    squareFreeFactorCoprimeRel :=
                ih (pthRoot loop.2) (multiplicity * p)
                  (by simpa [loop] using hroot_tail)
              have hcross :
                  ∀ a ∈ loop.1.reverse,
                    ∀ b ∈
                        (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse,
                      squareFreeFactorCoprimeRel a b := by
                have h :=
                  yunFactorsWithLevel_squareFreeAuxRev_tail_cross_coprime
                    hp c g multiplicity 1 fuel hinv.reachable hres_unfolded
                simpa [loop, Nat.mul_one] using h
              have hcombined :
                  (loop.1.reverse ++
                      (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse).Pairwise
                    squareFreeFactorCoprimeRel := by
                exact pairwise_append_of_cross
                  squareFreeFactorCoprimeRel hloop htail hcross
              have hrev :
                  (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                    loop.1.reverse ++
                      (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel []).reverse := by
                exact squareFreeAuxRev_reverse_append (pthRoot loop.2) (multiplicity * p) fuel loop.1
              simpa [g, c, loop, hrepeated, hrev] using hcombined

private theorem squareFreeAuxRev_pairwise_coprime_nil_core
    (hp : Hex.Nat.Prime p)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel)
    (_hreachable : squareFreeContributionReachable f) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact squareFreeAuxRev_pairwise_coprime_nil_core_of_yun_invariant
    hp
    (fun f' base fuel' hdf =>
      yunFactorsPairwiseInvariant_of_derivative_split_reachable
        hp f' base 1 fuel'
        (by intro htrue; rw [htrue] at hdf; cases hdf))
    f multiplicity fuel hfuel

private theorem squareFreeAuxRev_pairwise_coprime_core
    (hp : Hex.Nat.Prime p)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel)
    (hreachable : squareFreeContributionReachable f)
    (accRev : List (SquareFreeFactor p)) :
    accRev.reverse.Pairwise squareFreeFactorCoprimeRel →
    (∀ a ∈ accRev.reverse,
      ∀ b ∈ (squareFreeAuxRev f multiplicity fuel []).reverse,
        squareFreeFactorCoprimeRel a b) →
    (squareFreeAuxRev f multiplicity fuel accRev).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  intro hacc hcross
  rw [squareFreeAuxRev_reverse_append f multiplicity fuel accRev]
  apply pairwise_append_of_cross
  · exact hacc
  · exact squareFreeAuxRev_pairwise_coprime_nil_core hp
      f multiplicity fuel hfuel hreachable
  · exact hcross

private theorem squareFreeAuxRev_pairwise_coprime_of_acc
    (hp : Hex.Nat.Prime p)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel)
    (hreachable : squareFreeContributionReachable f)
    (accRev : List (SquareFreeFactor p)) :
    accRev.reverse.Pairwise squareFreeFactorCoprimeRel →
    (∀ a ∈ accRev.reverse,
      ∀ b ∈ (squareFreeAuxRev f multiplicity fuel []).reverse,
        squareFreeFactorCoprimeRel a b) →
    (squareFreeAuxRev f multiplicity fuel accRev).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  exact squareFreeAuxRev_pairwise_coprime_core hp
    f multiplicity fuel hfuel hreachable accRev

private theorem squareFreeAuxRev_pairwise_coprime_nil
    (hp : Hex.Nat.Prime p)
    (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel)
    (hreachable : squareFreeContributionReachable f) :
    (squareFreeAuxRev f multiplicity fuel []).reverse.Pairwise
      squareFreeFactorCoprimeRel := by
  apply squareFreeAuxRev_pairwise_coprime_of_acc hp
    f multiplicity fuel hfuel hreachable
  · simp
  · intro a ha
    simp at ha

private def yunFactorsStepsSquareFree (c w : FpPoly p) : Nat → Prop
  | 0 => True
  | fuel + 1 =>
      if isOne c then
        True
      else
        let y := monicGcd c w
        let z := c / y
        (if isOne z then
          True
        else
          (normalizeMonic (DensePoly.gcd z (DensePoly.derivative z))).2 = 1) ∧
          yunFactorsStepsSquareFree y (w / y) fuel

private theorem yunFactorsStepsSquareFree_of_reachable
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel) :
    yunFactorsStepsSquareFree c w fuel := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  induction fuel generalizing c w with
  | zero =>
      simp [yunFactorsStepsSquareFree]
  | succ fuel ih =>
      by_cases hc : isOne c
      · simp [yunFactorsStepsSquareFree, hc]
      · let y := monicGcd c w
        let z := c / y
        have hcurrent :
            ∀ d : FpPoly p,
              d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p) :=
          yunFactorsPairwiseReachable_current_squarefree c w (fuel + 1) hreachable
        have hz_dvd_c : z ∣ c := by
          refine ⟨y, ?_⟩
          simpa [z, y] using (div_monicGcd_mul_reconstruct hp c w).symm
        have hz_squarefree :
            ∀ d : FpPoly p,
              d ∣ z → d ∣ DensePoly.derivative z → d ∣ (1 : FpPoly p) :=
          squarefree_factor_of_squarefree hz_dvd_c hcurrent
        have hgcd_dvd_one :
            DensePoly.gcd z (DensePoly.derivative z) ∣ (1 : FpPoly p) :=
          hz_squarefree (DensePoly.gcd z (DensePoly.derivative z))
            (DensePoly.gcd_dvd_left z (DensePoly.derivative z))
            (DensePoly.gcd_dvd_right z (DensePoly.derivative z))
        have hnormalized :
            (normalizeMonic (DensePoly.gcd z (DensePoly.derivative z))).2 = 1 :=
          normalizeMonic_eq_one_of_dvd_one hgcd_dvd_one
        have htail_reachable :
            yunFactorsPairwiseReachable y (w / y) fuel := by
          simpa [y] using yunFactorsPairwiseReachable_step c w fuel hreachable
        have htail : yunFactorsStepsSquareFree y (w / y) fuel :=
          ih y (w / y) htail_reachable
        by_cases hz : isOne z
        · simpa [yunFactorsStepsSquareFree, hc, y, z, hz] using htail
        · simpa [yunFactorsStepsSquareFree, hc, y, z, hz] using
            And.intro hnormalized htail

private theorem yunFactorsStepsSquareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsStepsSquareFree
      (f / monicGcd f (DensePoly.derivative f))
      (monicGcd f (DensePoly.derivative f))
      fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact yunFactorsStepsSquareFree_of_reachable
    (f / monicGcd f (DensePoly.derivative f))
    (monicGcd f (DensePoly.derivative f))
    fuel
    (yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf)

private theorem yunFactorsWithLevel_factors_squareFree_of_steps
    (c w : FpPoly p) (base level fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hsteps : yunFactorsStepsSquareFree c w fuel)
    (hacc : ∀ sf ∈ accRev.reverse, squareFreeFactorSquareFreeRel sf) :
    ∀ sf ∈ (yunFactorsWithLevel c w base level fuel accRev).1.reverse,
      squareFreeFactorSquareFreeRel sf := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simpa [yunFactorsWithLevel] using hacc
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simpa [hc] using hacc
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        have hsteps_nonone :
            (if isOne z then
              True
            else
              (normalizeMonic (DensePoly.gcd z (DensePoly.derivative z))).2 = 1) ∧
              yunFactorsStepsSquareFree y (w / y) fuel := by
          simpa [yunFactorsStepsSquareFree, hc, y, z] using hsteps
        have hsteps_tail : yunFactorsStepsSquareFree y (w / y) fuel := by
          exact hsteps_nonone.2
        by_cases hz : isOne z
        · simpa [y, z, hz] using
            ih y (w / y) (level + 1) accRev hsteps_tail hacc
        · have hacc' :
              ∀ sf ∈ ({ factor := z, multiplicity := base * level } :: accRev).reverse,
                squareFreeFactorSquareFreeRel sf := by
            intro sf hsf
            rw [List.reverse_cons] at hsf
            rcases List.mem_append.mp hsf with hsf | hsf
            · exact hacc sf hsf
            · simp only [List.mem_singleton] at hsf
              subst sf
              have hstep :
                  (normalizeMonic (DensePoly.gcd z (DensePoly.derivative z))).2 = 1 := by
                simpa [hz] using hsteps_nonone.1
              simpa [squareFreeFactorSquareFreeRel, z, y] using hstep
          simpa [y, z, hz] using
            ih y (w / y) (level + 1)
              ({ factor := z, multiplicity := base * level } :: accRev) hsteps_tail hacc'

private theorem yunFactorsWithLevel_factors_squareFree_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hdf : (DensePoly.derivative f).isZero ≠ true)
    (hacc : ∀ sf ∈ accRev.reverse, squareFreeFactorSquareFreeRel sf) :
    ∀ sf ∈
        (yunFactorsWithLevel (f / monicGcd f (DensePoly.derivative f))
          (monicGcd f (DensePoly.derivative f)) base level fuel accRev).1.reverse,
      squareFreeFactorSquareFreeRel sf := by
  apply yunFactorsWithLevel_factors_squareFree_of_steps
  · exact yunFactorsStepsSquareFree_of_derivative_split hp f fuel hdf
  · exact hacc

private theorem squareFreeAuxRev_factors_squareFree
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (accRev : List (SquareFreeFactor p))
    (hacc : ∀ sf ∈ accRev.reverse, squareFreeFactorSquareFreeRel sf) :
    ∀ sf ∈ (squareFreeAuxRev f multiplicity fuel accRev).reverse,
      squareFreeFactorSquareFreeRel sf := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simpa [squareFreeAuxRev] using hacc
  | succ fuel ih =>
      simp only [squareFreeAuxRev]
      by_cases hzero : f.isZero
      · simpa [hzero] using hacc
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev hacc
        · simp [hdf]
          let g := monicGcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          have hloop :
              ∀ sf ∈ loop.1.reverse,
                squareFreeFactorSquareFreeRel sf := by
            simpa [loop, c, g] using
              yunFactorsWithLevel_factors_squareFree_of_derivative_split hp f multiplicity 1 fuel
                accRev hdf hacc
          by_cases hrepeated : isOne loop.2
          · simpa [loop, c, g, hrepeated] using hloop
          · simpa [loop, c, g, hrepeated] using
              ih (pthRoot loop.2) (multiplicity * p) loop.1 hloop

private theorem squareFreeAuxRevContribution_correct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f)
    (hresidual : squareFreeAuxRevResidualSatisfied f 1 (f.size + 1))
    (hrawState : YunDerivativeActiveRawStateProvider hp) :
    squareFreeAuxRevContribution f 1 (f.size + 1) = f := by
  rw [squareFreeAuxRevContribution_correct_pow_of_nonzero hp f 1 (f.size + 1)
    (by omega) (by omega) hzero hreachable hresidual hrawState]
  exact pow_one f

private theorem squareFreeAux_zero_weightedProduct
    (f : FpPoly p) (hzero : f.isZero = true) :
    weightedProduct (squareFreeAux f 1 (f.size + 1)) = 1 := by
  unfold squareFreeAux
  simp [squareFreeAuxRev, hzero, weightedProduct_nil]


end FpPoly
end Hex
