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
public import HexPolyFp.SquareFree.YunReduce
import all HexPolyFp.SquareFree.Algebra
import all HexPolyFp.SquareFree.YunContribution
import all HexPolyFp.SquareFree.YunReduce

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Derivative-active reachability, the level-measure decrease lemmas, and
`yunFactorsLevelCompletes` completion proofs.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]
private abbrev YunDerivativeActiveNormalizedStateProvider
    (hp : Hex.Nat.Prime p) : Prop :=
  ∀ f' c w : FpPoly p, ∀ fuel : Nat,
    yunFactorsDerivativeActiveReachable hp f' c w fuel →
      squareFreeContributionReachable (normalizeMonic c).2 ∧
        (normalizeMonic c).2.isZero = false ∧
          squareFreeContributionReachable (normalizeMonic w).2 ∧
            (normalizeMonic w).2.isZero = false

private abbrev YunDerivativeActiveLevelStateProvider
    (hp : Hex.Nat.Prime p) : Prop :=
  ∀ f' c w : FpPoly p, ∀ fuel : Nat,
    yunFactorsDerivativeActiveReachable hp f' c w fuel →
      squareFreeContributionReachable c ∧
        c.isZero = false ∧
          w.isZero = false

private abbrev YunDerivativeActiveRawStateProvider
    (hp : Hex.Nat.Prime p) : Prop :=
  ∀ f' c w : FpPoly p, ∀ fuel : Nat,
    yunFactorsDerivativeActiveReachable hp f' c w fuel →
      squareFreeContributionReachable c ∧
        c.isZero = false ∧
          squareFreeContributionReachable w ∧
            w.isZero = false

private abbrev YunDerivativeActiveRawTailProvider
    (hp : Hex.Nat.Prime p) : Prop :=
  ∀ f' c w : FpPoly p, ∀ base level fuel : Nat,
    yunFactorsDerivativeActiveReachable hp f' c w fuel →
      let contribution := yunFactorsContributionWithLevel c w base level fuel
      squareFreeContributionReachable contribution.2 ∧
        contribution.2.isZero = false ∧
          ((contribution.2.size < fuel + 1) →
            (isOne contribution.2 = false) →
              ((DensePoly.derivative contribution.2).isZero = true) →
                squareFreeContributionReachable (pthRoot contribution.2) ∧
                  (pthRoot contribution.2).isZero = false ∧
                    (pthRoot contribution.2).size < fuel)

private theorem YunDerivativeActiveRawStateProvider.levelState
    (hp : Hex.Nat.Prime p)
    (hstate : YunDerivativeActiveRawStateProvider hp) :
    YunDerivativeActiveLevelStateProvider hp := by
  intro f' c w fuel hreachable
  have hcurrent := hstate f' c w fuel hreachable
  exact ⟨hcurrent.1, hcurrent.2.1, hcurrent.2.2.2⟩

private theorem yunLevel_measure_lt_of_reachable_gcd_nonconstant
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hreachable : squareFreeContributionReachable c)
    (hc : isOne c = false)
    (hc_zero : c.isZero = false)
    (hw_zero : w.isZero = false)
    (_hy_nonconstant : 1 < (monicGcd c w).size) :
    (monicGcd c w).size + (w / monicGcd c w).size <
      c.size + w.size := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  have hc_size : 1 < c.size :=
    one_lt_size_of_isOne_false_of_reachable c hc_zero hc hreachable
  have hw_ne : w ≠ 0 := by
    intro hw_eq
    rw [hw_eq] at hw_zero
    exact (Bool.eq_not_self _).mp hw_zero.symm
  have hsize :=
    size_div_add_size_eq_size_add_one_of_dvd
      (monicGcd_dvd_right hp c w) hw_ne
  omega

private theorem normalizeMonic_eq_one_of_dvd_one
    [ZMod64.PrimeModulus p] {g : FpPoly p}
    (hdiv : g ∣ (1 : FpPoly p)) :
    (normalizeMonic g).2 = 1 := by
  have hg_nonzero : g.isZero = false := by
    cases hzero : g.isZero with
    | false => rfl
    | true =>
        exfalso
        rcases hdiv with ⟨u, hu⟩
        have hone_ne : (1 : FpPoly p) ≠ 0 := by
          intro h
          have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
          change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
          change (DensePoly.C (1 : ZMod64 p)).coeff 0 =
            (0 : FpPoly p).coeff 0 at hcoeff
          rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
          exact zmod64_one_ne_zero_of_prime
            (ZMod64.PrimeModulus.prime (p := p)) hcoeff
        apply hone_ne
        rw [hu, eq_zero_of_isZero_true g hzero, zero_mul]
  apply eq_one_of_monic_dvd_one
  · exact normalizeMonic_nonzero_monic g hg_nonzero
  · have hnorm_dvd_g : (normalizeMonic g).2 ∣ g := by
      refine ⟨DensePoly.C (normalizeMonic g).1, ?_⟩
      calc
        g = DensePoly.C (normalizeMonic g).1 * (normalizeMonic g).2 := by
          exact (normalizeMonic_reconstruct
            (ZMod64.PrimeModulus.prime (p := p)) g).symm
        _ = (normalizeMonic g).2 * DensePoly.C (normalizeMonic g).1 := by
          exact DensePoly.mul_comm_poly _ _
    exact dvd_trans_poly hnorm_dvd_g hdiv

private theorem dvd_one_of_normalizeMonic_eq_one
    [ZMod64.PrimeModulus p] (g : FpPoly p)
    (hnorm : (normalizeMonic g).2 = 1) :
    g ∣ (1 : FpPoly p) := by
  by_cases hzero : g.isZero = true
  · exfalso
    rw [normalizeMonic_zero g hzero] at hnorm
    have hone_ne : (1 : FpPoly p) ≠ 0 := by
      intro h
      have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) h
      change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
      change (DensePoly.C (1 : ZMod64 p)).coeff 0 =
        (0 : FpPoly p).coeff 0 at hcoeff
      rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
      exact zmod64_one_ne_zero_of_prime
        (ZMod64.PrimeModulus.prime (p := p)) hcoeff
    exact hone_ne hnorm.symm
  · have hzero_false : g.isZero = false := by
      cases h : g.isZero with
      | false => rfl
      | true => exact False.elim (hzero h)
    have hnonzero := normalizeMonic_nonzero g hzero_false
    have h_scale :
        DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g = 1 := by
      have heq :
          (normalizeMonic g).2 = DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g := by
        rw [hnonzero]
      rw [← heq]
      exact hnorm
    refine ⟨DensePoly.C (DensePoly.leadingCoeff g)⁻¹, ?_⟩
    calc (1 : FpPoly p)
        = DensePoly.scale (DensePoly.leadingCoeff g)⁻¹ g := h_scale.symm
      _ = DensePoly.C (DensePoly.leadingCoeff g)⁻¹ * g :=
          (C_mul_eq_scale _ _).symm
      _ = g * DensePoly.C (DensePoly.leadingCoeff g)⁻¹ :=
          DensePoly.mul_comm_poly _ _

private theorem yunStep_tail_common_dvd_one_of_gcd_normalized_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hnormalized : (normalizeMonic (DensePoly.gcd c w)).2 = 1) :
    ∀ d : FpPoly p,
      d ∣ monicGcd c w →
        d ∣ w / monicGcd c w →
          d ∣ (1 : FpPoly p) := by
  intro d hdy _hdv
  have hg_one : monicGcd c w = 1 := by rw [monicGcd_def]; exact hnormalized
  rw [hg_one] at hdy
  exact hdy

private theorem constant_nonzero_dvd
    [ZMod64.PrimeModulus p] {g f : FpPoly p}
    (hg_zero : g.isZero = false)
    (hg_const : ¬ 1 < g.size) :
    g ∣ f := by
  have hg_pos : 0 < g.size := size_pos_of_isZero_false g hg_zero
  have hg_size : g.size = 1 := by omega
  let unit := DensePoly.leadingCoeff g
  have hunit_ne : unit ≠ 0 := fpPoly_leadingCoeff_ne_zero_of_isZero_false g hg_zero
  have hg_eq_C : g = DensePoly.C unit := by
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        have hlead : unit = g.coeff 0 := by
          have hlead_last : DensePoly.leadingCoeff g = g.coeff (g.size - 1) := by
            simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
          simpa [unit, hg_size] using hlead_last
        rw [← hlead]
        exact (DensePoly.coeff_C unit 0).symm
    | succ n =>
        have hg_coeff_zero : g.coeff (n + 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le g (by omega)
        rw [hg_coeff_zero]
        exact (DensePoly.coeff_C unit (n + 1)).symm
  refine ⟨DensePoly.scale unit⁻¹ f, ?_⟩
  rw [hg_eq_C, C_mul_eq_scale, scale_scale,
    zmod64_mul_inv_eq_one_of_prime_ne_zero (ZMod64.PrimeModulus.prime (p := p)) hunit_ne]
  exact (scale_one_left f).symm

private theorem yunStep_gcd_nonzero_of_left_nonzero
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hc_zero : c.isZero = false) :
    (monicGcd c w).isZero = false := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  cases hy_zero : (monicGcd c w).isZero with
  | false => rfl
  | true =>
      exfalso
      have hy_eq_zero : monicGcd c w = 0 :=
        eq_zero_of_isZero_true (monicGcd c w) hy_zero
      rcases monicGcd_dvd_left hp c w with ⟨q, hq⟩
      have hc_eq_zero : c = 0 := by
        rw [hy_eq_zero, zero_mul] at hq
        exact hq
      rw [hc_eq_zero] at hc_zero
      cases hc_zero

private theorem yunStep_gcd_dvd_one_of_constant_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hc_zero : c.isZero = false)
    (hy_constant : ¬ 1 < (monicGcd c w).size)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / monicGcd c w →
          d ∣ monicGcd c w →
            d ∣ (1 : FpPoly p)) :
    monicGcd c w ∣ (1 : FpPoly p) := by
  have hy_zero : (monicGcd c w).isZero = false :=
    yunStep_gcd_nonzero_of_left_nonzero c w hc_zero
  apply hcommon (monicGcd c w)
  · exact constant_nonzero_dvd hy_zero hy_constant
  · exact DensePoly.dvd_refl_poly (monicGcd c w)

private theorem yunStep_gcd_normalized_one_of_constant_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hc_zero : c.isZero = false)
    (hy_constant : ¬ 1 < (monicGcd c w).size)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / monicGcd c w →
          d ∣ monicGcd c w →
            d ∣ (1 : FpPoly p)) :
    (normalizeMonic (DensePoly.gcd c w)).2 = 1 := by
  have hgcd_ne : (DensePoly.gcd c w).isZero = false := by
    cases hg : (DensePoly.gcd c w).isZero with
    | false => rfl
    | true =>
        exfalso
        have hg_zero : DensePoly.gcd c w = 0 :=
          eq_zero_of_isZero_true (DensePoly.gcd c w) hg
        rcases DensePoly.gcd_dvd_left c w with ⟨q, hq⟩
        have hc_eq_zero : c = 0 := by rw [hq, hg_zero, zero_mul]
        rw [hc_eq_zero] at hc_zero
        cases hc_zero
  have hdvd : monicGcd c w ∣ (1 : FpPoly p) :=
    yunStep_gcd_dvd_one_of_constant_common_dvd_one
      c w hc_zero hy_constant hcommon
  have hone : monicGcd c w = 1 :=
    eq_one_of_monic_dvd_one (monicGcd_monic_of_gcd_nonzero c w hgcd_ne) hdvd
  rw [← monicGcd_def]
  exact hone

private theorem yunStep_tail_common_dvd_one_of_constant_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hc_zero : c.isZero = false)
    (hy_constant : ¬ 1 < (monicGcd c w).size)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / monicGcd c w →
          d ∣ monicGcd c w →
            d ∣ (1 : FpPoly p)) :
    ∀ d : FpPoly p,
      d ∣ monicGcd c w →
        d ∣ w / monicGcd c w →
          d ∣ (1 : FpPoly p) := by
  exact yunStep_tail_common_dvd_one_of_gcd_normalized_one c w
    (yunStep_gcd_normalized_one_of_constant_common_dvd_one
      c w hc_zero hy_constant hcommon)

private theorem yunLevel_measure_lt_of_reachable_gcd_constant
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p)
    (hreachable : squareFreeContributionReachable c)
    (hc : isOne c = false)
    (hc_zero : c.isZero = false)
    (hw_zero : w.isZero = false)
    (hy_constant : ¬ 1 < (monicGcd c w).size)
    (hcommon :
      ∀ d : FpPoly p,
        d ∣ c / monicGcd c w →
          d ∣ monicGcd c w →
            d ∣ (1 : FpPoly p)) :
    (monicGcd c w).size + (w / monicGcd c w).size <
      c.size + w.size := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  have _htail_common :
      ∀ d : FpPoly p,
        d ∣ monicGcd c w →
          d ∣ w / monicGcd c w →
            d ∣ (1 : FpPoly p) :=
    yunStep_tail_common_dvd_one_of_constant_common_dvd_one
      c w hc_zero hy_constant hcommon
  have hc_size : 1 < c.size :=
    one_lt_size_of_isOne_false_of_reachable c hc_zero hc hreachable
  have hy_zero : (monicGcd c w).isZero = false :=
    yunStep_gcd_nonzero_of_left_nonzero c w hc_zero
  have hy_size : (monicGcd c w).size = 1 := by
    have hy_pos : 0 < (monicGcd c w).size :=
      size_pos_of_isZero_false (monicGcd c w) hy_zero
    omega
  have hw_ne : w ≠ 0 := by
    intro hw_eq
    rw [hw_eq] at hw_zero
    exact (Bool.eq_not_self _).mp hw_zero.symm
  have hsize :
      (w / monicGcd c w).size + (monicGcd c w).size =
        w.size + 1 :=
    size_div_add_size_eq_size_add_one_of_dvd
      (monicGcd_dvd_right hp c w) hw_ne
  omega

private theorem yunLevel_measure_lt_of_reachable_step
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hstate :
      squareFreeContributionReachable c ∧
        c.isZero = false ∧
          w.isZero = false)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1))
    (hc : isOne c = false) :
    (monicGcd c w).size + (w / monicGcd c w).size <
      c.size + w.size := by
  rcases hstate with ⟨hcontribution_reachable, hc_zero, hw_zero⟩
  by_cases hy_nonconstant : 1 < (monicGcd c w).size
  · exact
      yunLevel_measure_lt_of_reachable_gcd_nonconstant
        c w hcontribution_reachable hc hc_zero hw_zero hy_nonconstant
  · exact
      yunLevel_measure_lt_of_reachable_gcd_constant
        c w hcontribution_reachable hc hc_zero hw_zero hy_nonconstant
        (yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable)

private theorem yunLevel_measure_lt_of_nonconstant_step
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hc_size : 1 < c.size)
    (hc_zero : c.isZero = false)
    (hw_zero : w.isZero = false)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1)) :
    (monicGcd c w).size + (w / monicGcd c w).size <
      c.size + w.size := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  by_cases hy_nonconstant : 1 < (monicGcd c w).size
  · have hw_ne : w ≠ 0 := by
      intro hw_eq
      rw [hw_eq] at hw_zero
      exact (Bool.eq_not_self _).mp hw_zero.symm
    have hsize :=
      size_div_add_size_eq_size_add_one_of_dvd
        (monicGcd_dvd_right hp c w) hw_ne
    omega
  · have hcommon :
        ∀ d : FpPoly p,
          d ∣ c / monicGcd c w →
            d ∣ monicGcd c w →
              d ∣ (1 : FpPoly p) :=
      yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable
    have _htail_common :
        ∀ d : FpPoly p,
          d ∣ monicGcd c w →
            d ∣ w / monicGcd c w →
              d ∣ (1 : FpPoly p) :=
      yunStep_tail_common_dvd_one_of_constant_common_dvd_one
        c w hc_zero hy_nonconstant hcommon
    have hy_zero : (monicGcd c w).isZero = false :=
      yunStep_gcd_nonzero_of_left_nonzero c w hc_zero
    have hy_size : (monicGcd c w).size = 1 := by
      have hy_pos : 0 < (monicGcd c w).size :=
        size_pos_of_isZero_false (monicGcd c w) hy_zero
      omega
    have hw_ne : w ≠ 0 := by
      intro hw_eq
      rw [hw_eq] at hw_zero
      exact (Bool.eq_not_self _).mp hw_zero.symm
    have hsize :
        (w / monicGcd c w).size + (monicGcd c w).size =
          w.size + 1 :=
      size_div_add_size_eq_size_add_one_of_dvd
        (monicGcd_dvd_right hp c w) hw_ne
    omega

private theorem yunFactorsDerivativeActiveReachable_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsDerivativeActiveReachable hp f
      (f / monicGcd f (DensePoly.derivative f))
      (monicGcd f (DensePoly.derivative f))
      fuel :=
  yunFactorsDerivativeActiveReachable.derivativeSplit fuel hdf

private theorem yunFactorsDerivativeActiveReachable_step
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w (fuel + 1)) :
    yunFactorsDerivativeActiveReachable hp f
      (monicGcd c w)
      (w / monicGcd c w)
      fuel :=
  yunFactorsDerivativeActiveReachable.step c w fuel hreachable

private theorem yunFactorsContributionWithLevel_tail_valid_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              squareFreeContributionReachable w ∧
                w.isZero = false)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    squareFreeContributionReachable contribution.2 ∧
      contribution.2.isZero = false := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate c w 0 hreachable
      simpa [yunFactorsContributionWithLevel] using
        And.intro hcurrent.2.2.1 hcurrent.2.2.2
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · have hcurrent := hstate c w (fuel + 1) hreachable
        simpa [yunFactorsContributionWithLevel, hc] using
          And.intro hcurrent.2.2.1 hcurrent.2.2.2
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (monicGcd c w)
              (w / monicGcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        simpa [yunFactorsContributionWithLevel, hc_false] using
          ih (monicGcd c w) (w / monicGcd c w) (level + 1)
            htail_reachable

private theorem yunFactorsContributionWithLevel_pthRoot_tail_valid
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              squareFreeContributionReachable w ∧
                w.isZero = false)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (htail_fuel :
      (yunFactorsContributionWithLevel c w base level fuel).2.size < fuel + 1)
    (htail_nontrivial :
      isOne (yunFactorsContributionWithLevel c w base level fuel).2 = false)
    (htail_derivative_zero :
      (DensePoly.derivative
        (yunFactorsContributionWithLevel c w base level fuel).2).isZero = true) :
    squareFreeContributionReachable
        (pthRoot (yunFactorsContributionWithLevel c w base level fuel).2) ∧
      (pthRoot (yunFactorsContributionWithLevel c w base level fuel).2).isZero = false ∧
        (pthRoot (yunFactorsContributionWithLevel c w base level fuel).2).size < fuel := by
  have htail_valid :=
    yunFactorsContributionWithLevel_tail_valid_of_derivative_active_reachable
      hp f c w base level fuel hstate hreachable
  exact
    pthRoot_valid_of_derivative_zero_nontrivial hp
      (yunFactorsContributionWithLevel c w base level fuel).2
      htail_fuel htail_valid.2 htail_nontrivial htail_derivative_zero htail_valid.1

private theorem yunFactorsWithLevel_pthRoot_tail_fuel_bound
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              squareFreeContributionReachable w ∧
                w.isZero = false)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (htail_fuel : (yunFactorsWithLevel c w base level fuel []).2.size < fuel + 1)
    (htail_nontrivial : isOne (yunFactorsWithLevel c w base level fuel []).2 = false)
    (htail_derivative_zero :
      (DensePoly.derivative (yunFactorsWithLevel c w base level fuel []).2).isZero = true) :
    (pthRoot (yunFactorsWithLevel c w base level fuel []).2).size < fuel := by
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  let loop := yunFactorsWithLevel c w base level fuel []
  have hloop_eq : loop.2 = contribution.2 := by
    have hrec := yunFactorsWithLevel_reconstruction_invariant c w base level fuel []
    simpa [loop, contribution] using hrec.1
  have hvalid :=
    yunFactorsContributionWithLevel_pthRoot_tail_valid
      hp f c w base level fuel hstate hreachable
      (by simpa [loop, contribution, hloop_eq] using htail_fuel)
      (by simpa [loop, contribution, hloop_eq] using htail_nontrivial)
      (by simpa [loop, contribution, hloop_eq] using htail_derivative_zero)
  simpa [loop, contribution, hloop_eq] using hvalid.2.2

private theorem YunDerivativeActiveRawStateProvider.rawTail
    (hp : Hex.Nat.Prime p)
    (hstate : YunDerivativeActiveRawStateProvider hp) :
    YunDerivativeActiveRawTailProvider hp := by
  intro f' c w base level fuel hreachable
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  have htail_valid :
      squareFreeContributionReachable contribution.2 ∧
        contribution.2.isZero = false := by
    simpa [contribution] using
      yunFactorsContributionWithLevel_tail_valid_of_derivative_active_reachable
        hp f' c w base level fuel
        (fun c w fuel hreachable => hstate f' c w fuel hreachable)
        hreachable
  refine ⟨htail_valid.1, htail_valid.2, ?_⟩
  intro htail_fuel htail_nontrivial htail_derivative_zero
  simpa [contribution] using
    yunFactorsContributionWithLevel_pthRoot_tail_valid
      hp f' c w base level fuel
      (fun c w fuel hreachable => hstate f' c w fuel hreachable)
      hreachable htail_fuel
      htail_nontrivial htail_derivative_zero

private theorem yunFactorsPairwiseReachable_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    yunFactorsPairwiseReachable c w fuel := by
  induction hreachable with
  | derivativeSplit fuel hdf =>
      exact yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf
  | step c w fuel _ ih =>
      exact yunFactorsPairwiseReachable_step c w fuel ih

private theorem yunFactorsDerivativeActiveReachable_nonzero
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    c.isZero = false ∧ w.isZero = false := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction hreachable with
  | derivativeSplit fuel hdf =>
      let g := monicGcd f (DensePoly.derivative f)
      let c := f / g
      have hdf_false : (DensePoly.derivative f).isZero = false := by
        cases h : (DensePoly.derivative f).isZero
        · rfl
        · exact False.elim (hdf h)
      have hf_ne : f ≠ 0 := by
        intro hf
        apply hdf
        rw [hf, DensePoly.derivative_zero]
        rfl
      have hg_nonzero : g.isZero = false := by
        simpa [g] using
          monicGcd_isZero_false_of_gcd_nonzero f (DensePoly.derivative f)
            (gcd_isZero_false_of_right_isZero_false f (DensePoly.derivative f) hdf_false)
      have hc_nonzero : c.isZero = false := by
        cases hc : c.isZero
        · rfl
        · have hc_zero : c = 0 := eq_zero_of_isZero_true c hc
          have hprod : c * g = f := by
            simpa [c, g] using div_monicGcd_mul_reconstruct hp f (DensePoly.derivative f)
          apply False.elim
          apply hf_ne
          rw [← hprod, hc_zero, zero_mul]
      simpa [c, g] using And.intro hc_nonzero hg_nonzero
  | step c w fuel _ ih =>
      let y := monicGcd c w
      let z := w / y
      have hy_nonzero : y.isZero = false := by
        simpa [y] using
          monicGcd_isZero_false_of_gcd_nonzero c w
            (gcd_isZero_false_of_right_isZero_false c w ih.2)
      have hz_nonzero : z.isZero = false := by
        cases hz : z.isZero
        · rfl
        · have hz_zero : z = 0 := eq_zero_of_isZero_true z hz
          have hprod : z * y = w := by
            simpa [z, y] using div_monicGcd_right_mul_reconstruct hp c w
          have hw_zero : w = 0 := by
            rw [← hprod, hz_zero, zero_mul]
          rw [hw_zero] at ih
          cases ih.2
      simpa [y, z] using And.intro hy_nonzero hz_nonzero

/-- Every node reachable in the derivative-active Yun recursion has a monic
residual `w`, and both `c` and `w` are nonzero and square-free-contribution
reachable. The monic residual is the load-bearing invariant: `w` starts monic
(a `monicGcd`) and each `step` keeps it monic, while `c` is either a `monicGcd`
(monic) or the derivative-split quotient (whose `squareFreeContributionReachable`
is the vacuous size-one case). This is what discharges the former
`YunDerivativeActiveRawStateProvider` hypothesis. -/
private theorem yunFactorsDerivativeActiveReachable_state
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (fuel : Nat)
    (hr : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    DensePoly.Monic w ∧
      squareFreeContributionReachable c ∧ c.isZero = false ∧
        squareFreeContributionReachable w ∧ w.isZero = false := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction hr with
  | derivativeSplit fuel hdf =>
      have hdf_false : (DensePoly.derivative f).isZero = false := by
        cases h : (DensePoly.derivative f).isZero
        · rfl
        · exact False.elim (hdf h)
      have hgcd_ne : (DensePoly.gcd f (DensePoly.derivative f)).isZero = false :=
        gcd_isZero_false_of_right_isZero_false f (DensePoly.derivative f) hdf_false
      have hw_monic : DensePoly.Monic (monicGcd f (DensePoly.derivative f)) :=
        monicGcd_monic_of_gcd_nonzero f (DensePoly.derivative f) hgcd_ne
      have hnonzero := yunFactorsDerivativeActiveReachable_nonzero hp f
        (f / monicGcd f (DensePoly.derivative f))
        (monicGcd f (DensePoly.derivative f)) fuel
        (yunFactorsDerivativeActiveReachable.derivativeSplit fuel hdf)
      refine ⟨hw_monic, ?_, hnonzero.1, ?_, hnonzero.2⟩
      · exact derivativeSplit_quotient_size_one_eq_one hp f hdf
      · exact squareFreeContributionReachable_of_monic _ hw_monic
  | step c w fuel _hr_prev ih =>
      obtain ⟨hw_monic, _, _, _, hw_zero⟩ := ih
      have hgcd_ne : (DensePoly.gcd c w).isZero = false :=
        gcd_isZero_false_of_right_isZero_false c w hw_zero
      have hy_monic : DensePoly.Monic (monicGcd c w) :=
        monicGcd_monic_of_gcd_nonzero c w hgcd_ne
      have hw'_monic : DensePoly.Monic (w / monicGcd c w) :=
        monic_div_monicGcd_right_of_monic hp c w hw_monic hy_monic
      have hnonzero := yunFactorsDerivativeActiveReachable_nonzero hp f
        (monicGcd c w) (w / monicGcd c w) fuel
        (yunFactorsDerivativeActiveReachable.step c w fuel _hr_prev)
      refine ⟨hw'_monic, ?_, hnonzero.1, ?_, hnonzero.2⟩
      · exact squareFreeContributionReachable_of_monic _ hy_monic
      · exact squareFreeContributionReachable_of_monic _ hw'_monic

/-- The derivative-active raw state provider is unconditionally true: it is just
the `c`/`w` projection of `yunFactorsDerivativeActiveReachable_state`. This
discharges the former `hrawState` hypothesis threaded through the contribution
correctness chain. -/
private theorem yunDerivativeActiveRawStateProvider_holds
    (hp : Hex.Nat.Prime p) :
    YunDerivativeActiveRawStateProvider hp := by
  intro f c w fuel hr
  obtain ⟨_, hc_reach, hc_zero, hw_reach, hw_zero⟩ :=
    yunFactorsDerivativeActiveReachable_state hp f c w fuel hr
  exact ⟨hc_reach, hc_zero, hw_reach, hw_zero⟩

private theorem yunFactorsContributionWithLevel_tail_nonzero_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    (yunFactorsContributionWithLevel c w base level fuel).2.isZero = false := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent :=
        yunFactorsDerivativeActiveReachable_nonzero hp f c w 0 hreachable
      simpa [yunFactorsContributionWithLevel] using hcurrent.2
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · have hcurrent :=
          yunFactorsDerivativeActiveReachable_nonzero hp f c w (fuel + 1) hreachable
        simpa [yunFactorsContributionWithLevel, hc] using hcurrent.2
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (monicGcd c w)
              (w / monicGcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        simpa [yunFactorsContributionWithLevel, hc_false] using
          ih (monicGcd c w) (w / monicGcd c w) (level + 1)
            htail_reachable

private theorem yunFactorsContributionWithLevel_normalized_tail_valid_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    squareFreeContributionReachable (normalizeMonic contribution.2).2 ∧
      (normalizeMonic contribution.2).2.isZero = false := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate f c w 0 hreachable
      simpa [yunFactorsContributionWithLevel] using
        And.intro hcurrent.2.2.1 hcurrent.2.2.2
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · have hcurrent := hstate f c w (fuel + 1) hreachable
        simpa [yunFactorsContributionWithLevel, hc] using
          And.intro hcurrent.2.2.1 hcurrent.2.2.2
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (monicGcd c w)
              (w / monicGcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        simpa [yunFactorsContributionWithLevel, hc_false] using
          ih (monicGcd c w) (w / monicGcd c w) (level + 1)
            htail_reachable

private theorem yunFactorsContributionWithLevel_normalized_pthRoot_tail_valid
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p) (base level fuel : Nat)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (htail_fuel :
      (yunFactorsContributionWithLevel c w base level fuel).2.size < fuel + 1)
    (htail_nontrivial :
      isOne (normalizeMonic
        (yunFactorsContributionWithLevel c w base level fuel).2).2 = false)
    (htail_derivative_zero :
      (DensePoly.derivative
        (yunFactorsContributionWithLevel c w base level fuel).2).isZero = true) :
    squareFreeContributionReachable
        (pthRoot (normalizeMonic
          (yunFactorsContributionWithLevel c w base level fuel).2).2) ∧
      (pthRoot (normalizeMonic
        (yunFactorsContributionWithLevel c w base level fuel).2).2).isZero = false ∧
        (pthRoot (normalizeMonic
          (yunFactorsContributionWithLevel c w base level fuel).2).2).size < fuel := by
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  have htail_valid :=
    yunFactorsContributionWithLevel_normalized_tail_valid_of_derivative_active_reachable
      hp f c w base level fuel hstate hreachable
  have htail_raw_nonzero : contribution.2.isZero = false := by
    simpa [contribution] using
      yunFactorsContributionWithLevel_tail_nonzero_of_derivative_active_reachable
        hp f c w base level fuel hreachable
  have hnorm_derivative_zero :
      (DensePoly.derivative (normalizeMonic contribution.2).2).isZero = true :=
    normalizeMonic_derivative_zero_of_derivative_zero
      contribution.2 htail_raw_nonzero (by
        simpa [contribution] using htail_derivative_zero)
  have hnorm_fuel : (normalizeMonic contribution.2).2.size < fuel + 1 := by
    have hsize :=
      normalizeMonic_nonzero_size_eq hp contribution.2 htail_raw_nonzero
    rw [hsize]
    simpa [contribution] using htail_fuel
  exact
    pthRoot_valid_of_derivative_zero_nontrivial hp
      (normalizeMonic contribution.2).2 hnorm_fuel htail_valid.2
      (by simpa [contribution] using htail_nontrivial)
      hnorm_derivative_zero htail_valid.1

private theorem yunFactorsDerivativeActiveReachable_normalized_stateProvider
    (hp : Hex.Nat.Prime p) :
    YunDerivativeActiveNormalizedStateProvider hp := by
  intro f' c w fuel hreachable
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hnonzero := yunFactorsDerivativeActiveReachable_nonzero hp f' c w fuel hreachable
  have hc := normalizeMonic_squareFreeContributionPayload hp c hnonzero.1
  have hw := normalizeMonic_squareFreeContributionPayload hp w hnonzero.2
  exact ⟨hc.1, hc.2, hw.1, hw.2⟩

private theorem yunFactorsNormalizedLevelCompletes_of_size_bound_derivative_active
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) (f c w : FpPoly p)
    (base level fuel : Nat)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (hbound : (normalizeMonic c).2.size + (normalizeMonic w).2.size ≤ fuel + 1) :
    yunFactorsNormalizedLevelCompletes c w base level fuel := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate f c w 0 hreachable
      have hc_pos : 0 < (normalizeMonic c).2.size :=
        size_pos_of_isZero_false (normalizeMonic c).2 hcurrent.2.1
      have hw_pos : 0 < (normalizeMonic w).2.size :=
        size_pos_of_isZero_false (normalizeMonic w).2 hcurrent.2.2.2
      exfalso
      omega
  | succ fuel ih =>
      by_cases hc_norm : isOne (normalizeMonic c).2 = true
      · exact Or.inl hc_norm
      · have hc_norm_false : isOne (normalizeMonic c).2 = false := by
          cases h : isOne (normalizeMonic c).2
          · rfl
          · exact False.elim (hc_norm h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (monicGcd c w)
              (w / monicGcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        have hpairwise :
            yunFactorsPairwiseReachable c w (fuel + 1) :=
          yunFactorsPairwiseReachable_of_derivative_active_reachable
            hp f c w (fuel + 1) hreachable
        have hcurrent := hstate f c w (fuel + 1) hreachable
        have hraw_nonzero :=
          yunFactorsDerivativeActiveReachable_nonzero hp f c w (fuel + 1) hreachable
        have hnorm_c_size : 1 < (normalizeMonic c).2.size :=
          one_lt_size_of_isOne_false_of_reachable
            (normalizeMonic c).2 hcurrent.2.1 hc_norm_false hcurrent.1
        have hc_size : 1 < c.size := by
          have hsize := normalizeMonic_nonzero_size_eq hp c hraw_nonzero.1
          omega
        have hmeasure :
            (monicGcd c w).size + (w / monicGcd c w).size <
              c.size + w.size :=
          yunLevel_measure_lt_of_nonconstant_step
            c w fuel hc_size hraw_nonzero.1 hraw_nonzero.2 hpairwise
        have htail_nonzero :=
          yunFactorsDerivativeActiveReachable_nonzero hp f
            (monicGcd c w) (w / monicGcd c w) fuel htail_reachable
        have hcurrent_c_size :
            (normalizeMonic c).2.size = c.size :=
          normalizeMonic_nonzero_size_eq hp c hraw_nonzero.1
        have hcurrent_w_size :
            (normalizeMonic w).2.size = w.size :=
          normalizeMonic_nonzero_size_eq hp w hraw_nonzero.2
        have htail_g_size :
            (normalizeMonic (monicGcd c w)).2.size =
              (monicGcd c w).size :=
          normalizeMonic_nonzero_size_eq hp (monicGcd c w) htail_nonzero.1
        have htail_w_size :
            (normalizeMonic (w / monicGcd c w)).2.size =
              (w / monicGcd c w).size :=
          normalizeMonic_nonzero_size_eq hp
            (w / monicGcd c w) htail_nonzero.2
        have htail_bound :
            (normalizeMonic (monicGcd c w)).2.size +
                (normalizeMonic (w / monicGcd c w)).2.size ≤ fuel + 1 := by
          omega
        exact Or.inr
          (ih (monicGcd c w) (w / monicGcd c w) (level + 1)
            htail_reachable htail_bound)

private theorem yunFactorsLevelCompletes_of_size_bound_derivative_active
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p) (f c w : FpPoly p)
    (base level fuel : Nat)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false)
    (hreachable : yunFactorsDerivativeActiveReachable hp f c w fuel)
    (hbound : c.size + w.size ≤ fuel + 1) :
    yunFactorsLevelCompletes c w base level fuel := by
  induction fuel generalizing c w level with
  | zero =>
      have hcurrent := hstate c w 0 hreachable
      have hc_pos : 0 < c.size :=
        size_pos_of_isZero_false c hcurrent.2.1
      have hw_pos : 0 < w.size :=
        size_pos_of_isZero_false w hcurrent.2.2
      exfalso
      omega
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · exact Or.inl hc
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_reachable :
            yunFactorsDerivativeActiveReachable hp f
              (monicGcd c w)
              (w / monicGcd c w)
              fuel :=
          yunFactorsDerivativeActiveReachable_step hp f c w fuel hreachable
        have hpairwise :
            yunFactorsPairwiseReachable c w (fuel + 1) :=
          yunFactorsPairwiseReachable_of_derivative_active_reachable
            hp f c w (fuel + 1) hreachable
        have hmeasure :
            (monicGcd c w).size + (w / monicGcd c w).size <
              c.size + w.size :=
          yunLevel_measure_lt_of_reachable_step
            c w fuel (hstate c w (fuel + 1) hreachable) hpairwise hc_false
        have htail_bound :
            (monicGcd c w).size + (w / monicGcd c w).size ≤
              fuel + 1 := by
          omega
        exact Or.inr
          (ih (monicGcd c w) (w / monicGcd c w) (level + 1)
            htail_reachable htail_bound)

private theorem yunFactorsLevelCompletes_of_derivative_active_reachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    let g := monicGcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsLevelCompletes c g multiplicity 1 fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  cases fuel with
  | zero =>
      have hsize_pos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
  | succ fuel =>
      have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
        intro htrue
        rw [htrue] at hdf
        cases hdf
      have hreachable :
          yunFactorsDerivativeActiveReachable hp f c g (fuel + 1) := by
        simpa [c, g] using
          yunFactorsDerivativeActiveReachable_of_derivative_split hp f (fuel + 1) hdf_ne_true
      have hbound : c.size + g.size ≤ fuel + 2 := by
        have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
        have hsize :
            c.size + g.size = f.size + 1 := by
          simpa [c, g] using
            size_div_add_size_eq_size_add_one_of_dvd
              (monicGcd_dvd_left hp f (DensePoly.derivative f)) hf_ne
        omega
      simpa [c, g] using
        yunFactorsLevelCompletes_of_size_bound_derivative_active
          hp f c g multiplicity 1 (fuel + 1) hstate hreachable hbound

/-- Initial-split completion wrapper for the derivative-active branch.

The state payload is restricted to states reachable from the normalized
derivative-active call path: the initial split `g = gcd f f'`, `c = f / g`,
followed by Yun tail steps. Callers do not need, and this theorem does not
assume, a universal provider for arbitrary raw Yun states. -/
private theorem yunFactorsLevelCompletes_of_derivative_active_initial_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    let g := monicGcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsLevelCompletes c g multiplicity 1 fuel := by
  exact
    yunFactorsLevelCompletes_of_derivative_active_reachable
      hp f multiplicity fuel hmultiplicity hfuel hzero hdf hstate

/-- Initial-split completion wrapper for the normalized derivative-active branch.

This is the scalar-aware analogue of
`yunFactorsLevelCompletes_of_derivative_active_initial_split`: it consumes the
normalized state provider and proves the normalized completion predicate, so raw
nonzero scalar-unit states do not need to satisfy `isOne c = true`. -/
private theorem yunFactorsNormalizedLevelCompletes_of_derivative_active_initial_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate : YunDerivativeActiveNormalizedStateProvider hp) :
    let g := monicGcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsNormalizedLevelCompletes c g multiplicity 1 fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  cases fuel with
  | zero =>
      have hsize_pos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
  | succ fuel =>
      have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
        intro htrue
        rw [htrue] at hdf
        cases hdf
      have hreachable :
          yunFactorsDerivativeActiveReachable hp f c g (fuel + 1) := by
        simpa [c, g] using
          yunFactorsDerivativeActiveReachable_of_derivative_split hp f (fuel + 1) hdf_ne_true
      have hnonzero :=
        yunFactorsDerivativeActiveReachable_nonzero hp f c g (fuel + 1) hreachable
      have hbound :
          (normalizeMonic c).2.size + (normalizeMonic g).2.size ≤ fuel + 2 := by
        have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
        have hsize :
            c.size + g.size = f.size + 1 := by
          simpa [c, g] using
            size_div_add_size_eq_size_add_one_of_dvd
              (monicGcd_dvd_left hp f (DensePoly.derivative f)) hf_ne
        have hc_size : (normalizeMonic c).2.size = c.size :=
          normalizeMonic_nonzero_size_eq hp c hnonzero.1
        have hg_size : (normalizeMonic g).2.size = g.size :=
          normalizeMonic_nonzero_size_eq hp g hnonzero.2
        omega
      simpa [c, g] using
        yunFactorsNormalizedLevelCompletes_of_size_bound_derivative_active
          hp f c g multiplicity 1 (fuel + 1) hstate hreachable hbound

private theorem yunFactorsContributionWithLevel_raw_pow_invariant
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hlevelState : YunDerivativeActiveLevelStateProvider hp) :
    let g := monicGcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
    contribution.1 * pow contribution.2 multiplicity = pow f multiplicity := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
  have hstate_level :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false := by
    intro c w fuel hreach
    exact hlevelState f c w fuel hreach
  have hcompletes :
      yunFactorsLevelCompletes c g multiplicity 1 fuel := by
    simpa [c, g] using
      yunFactorsLevelCompletes_of_derivative_active_initial_split
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf hstate_level
  have hpow :=
    yunFactorsContributionWithLevel_pow_invariant_of_completes
      c g multiplicity 1 fuel hcompletes
  have hcg : c * g = f := by
    simpa [c, g] using div_monicGcd_mul_reconstruct hp f (DensePoly.derivative f)
  calc
    contribution.1 * pow contribution.2 multiplicity =
        pow c (multiplicity * 1) * pow g multiplicity := by
          simpa [contribution, Nat.mul_one] using hpow
    _ = pow c multiplicity * pow g multiplicity := by rw [Nat.mul_one]
    _ = pow (c * g) multiplicity := by
          exact (pow_mul_base c g multiplicity).symm
    _ = pow f multiplicity := by rw [hcg]

/--
Scalar-aware derivative-active product invariant for the normalized tail of the
scaled Yun contribution loop. The exact raw product identity is supplied as an
input; this theorem no longer requires the false raw/level provider path just
to expose the normalized-tail product form.
-/
private theorem yunFactorsContributionWithLevel_normalized_pow_invariant
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hnormalizedState : YunDerivativeActiveNormalizedStateProvider hp)
    (hrawProduct :
      let g := monicGcd f (DensePoly.derivative f)
      let c := f / g
      let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
      contribution.1 * pow contribution.2 multiplicity = pow f multiplicity) :
    let g := monicGcd f (DensePoly.derivative f)
    let c := f / g
    let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
    contribution.1 *
        (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
          pow (normalizeMonic contribution.2).2 multiplicity) =
      pow f multiplicity := by
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
  have _hnormalized_completes :
      yunFactorsNormalizedLevelCompletes c g multiplicity 1 fuel := by
    simpa [c, g] using
      yunFactorsNormalizedLevelCompletes_of_derivative_active_initial_split
        hp f multiplicity fuel hmultiplicity hfuel hzero hdf hnormalizedState
  simpa [contribution] using
    yunFactorsContributionWithLevel_normalized_tail_product_bridge
      hp f c g multiplicity 1 fuel multiplicity (by
        simpa [g, c, contribution] using hrawProduct)

/--
Combined provider for `yunFactorsContributionResidualComplete` driven by a
`yunFactorsLevelCompletes` termination witness and a pairwise reachability
chain. Walks the recursion through the `LevelCompletes` predicate; at each
state where `isOne c = true` the residual derivative-zero fact comes from
`yunFactorsPairwiseReachable_terminal_residual_derivative_zero`.
-/
private theorem yunFactorsContributionResidualComplete_of_pairwise_reachable_levelCompletes
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (multiplicity base level fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hcompletes : yunFactorsLevelCompletes c w base level fuel) :
    yunFactorsContributionResidualComplete c w multiplicity fuel := by
  induction fuel generalizing c w multiplicity level with
  | zero =>
      intro _hone
      have hc : isOne c = true := by
        simpa [yunFactorsLevelCompletes] using hcompletes
      exact
        yunFactorsPairwiseReachable_terminal_residual_derivative_zero
          c w 0 hreachable hc
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · simpa [yunFactorsContributionResidualComplete, hc] using
          (fun _hone : isOne w = false =>
            yunFactorsPairwiseReachable_terminal_residual_derivative_zero
              c w (fuel + 1) hreachable hc)
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        let y := monicGcd c w
        have htail_reachable :
            yunFactorsPairwiseReachable y (w / y) fuel := by
          simpa [y] using yunFactorsPairwiseReachable_step c w fuel hreachable
        have htail_completes :
            yunFactorsLevelCompletes y (w / y) base (level + 1) fuel := by
          have hcompletes_unfold :
              isOne c = true ∨
                yunFactorsLevelCompletes y (w / y) base (level + 1) fuel := by
            simpa [y, yunFactorsLevelCompletes] using hcompletes
          rcases hcompletes_unfold with hone | htail
          · exact False.elim (hc hone)
          · exact htail
        have htail :
            yunFactorsContributionResidualComplete y (w / y) (multiplicity + 1) fuel :=
          ih y (w / y) (multiplicity + 1) (level + 1) htail_reachable htail_completes
        simpa [yunFactorsContributionResidualComplete, hc_false, y] using htail

/--
Unscaled derivative-active provider for the contribution residual derivative-zero
fact. Discharges the `yunFactorsContributionResidualDerivativeZero` hypothesis
on `(c, g) = (f / gcd f f', gcd f f')` purely from the size bound, the
nonzero/derivative-active hypotheses on `f`, and a derivative-active state
provider, by combining `yunFactorsLevelCompletes_of_size_bound_derivative_active`
with the pairwise-reachable terminal residual derivative-zero lemma.
-/
private theorem yunFactorsContributionResidualDerivativeZero_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    let g := monicGcd f (DensePoly.derivative f)
    let c := f / g
    yunFactorsContributionResidualDerivativeZero c g multiplicity fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  have hdf_ne_true : (DensePoly.derivative f).isZero ≠ true := by
    intro htrue
    rw [htrue] at hdf
    cases hdf
  have hreachable : yunFactorsPairwiseReachable c g fuel := by
    simpa [c, g] using
      yunFactorsPairwiseReachable_of_derivative_split hp f fuel hdf_ne_true
  cases fuel with
  | zero =>
      exfalso
      have hsize_pos : 0 < f.size := size_pos_of_isZero_false f hzero
      omega
  | succ fuel =>
      have hda_reachable :
          yunFactorsDerivativeActiveReachable hp f c g (fuel + 1) := by
        simpa [c, g] using
          yunFactorsDerivativeActiveReachable_of_derivative_split
            hp f (fuel + 1) hdf_ne_true
      have hbound : c.size + g.size ≤ fuel + 2 := by
        have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero
        have hsize_eq : c.size + g.size = f.size + 1 := by
          simpa [c, g] using
            size_div_add_size_eq_size_add_one_of_dvd
              (monicGcd_dvd_left hp f (DensePoly.derivative f)) hf_ne
        omega
      have hcompletes :
          yunFactorsLevelCompletes c g multiplicity 1 (fuel + 1) :=
        yunFactorsLevelCompletes_of_size_bound_derivative_active
          hp f c g multiplicity 1 (fuel + 1) hstate hda_reachable hbound
      have hresidual_complete :
          yunFactorsContributionResidualComplete c g multiplicity (fuel + 1) :=
        yunFactorsContributionResidualComplete_of_pairwise_reachable_levelCompletes
          c g multiplicity multiplicity 1 (fuel + 1) hreachable hcompletes
      exact
        yunFactorsContributionResidualDerivativeZero_of_complete
          c g multiplicity (fuel + 1) hresidual_complete

/--
Scaled-loop residual derivative-zero invariant for the derivative-active
branch. Composes the unscaled witness
`yunFactorsContributionResidualDerivativeZero_of_derivative_split` with the
equality `yunFactorsContributionWithLevel_residual_derivative_zero_of_unscaled`:
the residual `.2` of `yunFactorsContributionWithLevel` agrees with that of
`yunFactorsContribution`, so derivative-zero transports directly.
-/
private theorem yunFactorsContributionWithLevel_residual_derivative_zero_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (base level fuel : Nat)
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = false)
    (hstate :
      ∀ c w : FpPoly p, ∀ fuel : Nat,
        yunFactorsDerivativeActiveReachable hp f c w fuel →
          squareFreeContributionReachable c ∧
            c.isZero = false ∧
              w.isZero = false) :
    isOne
        (yunFactorsContributionWithLevel
          (f / monicGcd f (DensePoly.derivative f))
          (monicGcd f (DensePoly.derivative f))
          base level fuel).2 = false →
      (DensePoly.derivative
          (yunFactorsContributionWithLevel
            (f / monicGcd f (DensePoly.derivative f))
            (monicGcd f (DensePoly.derivative f))
            base level fuel).2).isZero = true := by
  apply yunFactorsContributionWithLevel_residual_derivative_zero_of_unscaled
  exact
    yunFactorsContributionResidualDerivativeZero_of_derivative_split
      hp f level fuel hfuel hzero hdf hstate

/-- The residual invariant holds for any size-`≤ 1` input at any fuel: a nonzero
size-one polynomial is a constant, so its derivative is zero and the recursion
descends through `pthRoot`, which keeps the size `≤ 1`, bottoming out at fuel
`0`. -/
private theorem squareFreeAuxRevResidualSatisfied_of_size_le_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (m fuel : Nat) (hsize : f.size ≤ 1) :
    squareFreeAuxRevResidualSatisfied f m fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction fuel generalizing f m with
  | zero => exact trivial
  | succ fuel ih =>
      by_cases hzero : f.isZero = true
      · simp only [squareFreeAuxRevResidualSatisfied]
        rw [if_pos hzero]; exact trivial
      · have hzero_false : f.isZero = false := by
          cases h : f.isZero
          · rfl
          · exact False.elim (hzero h)
        have hsize_one : f.size = 1 := by
          have hpos := size_pos_of_isZero_false f hzero_false
          omega
        have hdf : (DensePoly.derivative f).isZero = true :=
          derivative_isZero_true_of_size_one f hsize_one
        simp only [squareFreeAuxRevResidualSatisfied]
        rw [if_neg (by simp [hzero_false]), if_pos hdf]
        have hroot_size : (pthRoot f).size ≤ 1 := by
          have h := pthRoot_size_of_derivative_zero hp f hzero_false hdf
          rw [hsize_one, Nat.sub_self, Nat.zero_div] at h
          omega
        exact ih (pthRoot f) (m * p) hroot_size

/-- The residual invariant holds whenever fuel exceeds the size: with monic
intermediates the loop residual divides the monic gcd (hence the input), so it
shrinks below the fuel and `pthRoot` strictly decreases it. The derivative-zero
residual fact is `yunFactorsContributionWithLevel_residual_derivative_zero_of_derivative_split`
and the recursion bound is `yunFactorsWithLevel_pthRoot_tail_fuel_bound`, both
discharged by the now-proven raw state provider. This is the size-bounded
replacement for the (false at small fuel) `∀ fuel` `residualInvariant`
hypothesis. -/
private theorem squareFreeAuxRevResidualSatisfied_of_size_lt
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (m fuel : Nat) (hbound : f.size < fuel) :
    squareFreeAuxRevResidualSatisfied f m fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  induction fuel generalizing f m with
  | zero => exact absurd hbound (by omega)
  | succ fuel ih =>
      by_cases hzero : f.isZero = true
      · simp only [squareFreeAuxRevResidualSatisfied]
        rw [if_pos hzero]; exact trivial
      · have hzero_false : f.isZero = false := by
          cases h : f.isZero
          · rfl
          · exact False.elim (hzero h)
        by_cases hsize1 : f.size ≤ 1
        · exact squareFreeAuxRevResidualSatisfied_of_size_le_one hp f m (fuel + 1) hsize1
        · have hnonconst : 1 < f.size := by omega
          by_cases hdf : (DensePoly.derivative f).isZero = true
          · simp only [squareFreeAuxRevResidualSatisfied]
            rw [if_neg (by simp [hzero_false]), if_pos hdf]
            have hroot_fuel : (pthRoot f).size < fuel :=
              pthRoot_fuel_decrease_of_derivative_zero_nonconstant hp f hbound hnonconst
            exact ih (pthRoot f) (m * p) hroot_fuel
          · have hdf_false : (DensePoly.derivative f).isZero = false := by
              cases h : (DensePoly.derivative f).isZero
              · rfl
              · exact False.elim (hdf h)
            have hstate : ∀ c w : FpPoly p, ∀ fuel : Nat,
                yunFactorsDerivativeActiveReachable hp f c w fuel →
                  squareFreeContributionReachable c ∧ c.isZero = false ∧
                    squareFreeContributionReachable w ∧ w.isZero = false :=
              fun c w fuel' hr =>
                yunDerivativeActiveRawStateProvider_holds hp f c w fuel' hr
            have hstateLvl : ∀ c w : FpPoly p, ∀ fuel : Nat,
                yunFactorsDerivativeActiveReachable hp f c w fuel →
                  squareFreeContributionReachable c ∧ c.isZero = false ∧
                    w.isZero = false :=
              fun c w fuel' hr =>
                let s := hstate c w fuel' hr
                ⟨s.1, s.2.1, s.2.2.2⟩
            have hreachable : yunFactorsDerivativeActiveReachable hp f
                (f / monicGcd f (DensePoly.derivative f))
                (monicGcd f (DensePoly.derivative f)) fuel :=
              yunFactorsDerivativeActiveReachable.derivativeSplit fuel (by simp [hdf_false])
            have hgcd_ne : (DensePoly.gcd f (DensePoly.derivative f)).isZero = false :=
              gcd_isZero_false_of_right_isZero_false f (DensePoly.derivative f) hdf_false
            have hg_inner_ne : monicGcd f (DensePoly.derivative f) ≠ 0 :=
              ne_zero_of_isZero_false
                (monicGcd_isZero_false_of_gcd_nonzero f (DensePoly.derivative f) hgcd_ne)
            have hf_ne : f ≠ 0 := ne_zero_of_isZero_false hzero_false
            have hbridge :
                (yunFactorsWithLevel
                    (f / monicGcd f (DensePoly.derivative f))
                    (monicGcd f (DensePoly.derivative f)) m 1 fuel []).2 =
                  (yunFactorsContributionWithLevel
                    (f / monicGcd f (DensePoly.derivative f))
                    (monicGcd f (DensePoly.derivative f)) m 1 fuel).2 :=
              (yunFactorsWithLevel_reconstruction_invariant
                (f / monicGcd f (DensePoly.derivative f))
                (monicGcd f (DensePoly.derivative f)) m 1 fuel []).1
            have hloop_dvd_f :
                (yunFactorsWithLevel
                    (f / monicGcd f (DensePoly.derivative f))
                    (monicGcd f (DensePoly.derivative f)) m 1 fuel []).2 ∣ f :=
              dvd_trans_poly
                (yunFactorsWithLevel_repeated_dvd_repeated
                  (f / monicGcd f (DensePoly.derivative f))
                  (monicGcd f (DensePoly.derivative f)) m 1 fuel)
                (monicGcd_dvd_left hp f (DensePoly.derivative f))
            have hloop_bound :
                (yunFactorsWithLevel
                    (f / monicGcd f (DensePoly.derivative f))
                    (monicGcd f (DensePoly.derivative f)) m 1 fuel []).2.size < fuel + 1 := by
              have := size_le_of_dvd_of_ne_zero hloop_dvd_f hf_ne
              omega
            have hderiv_impl :
                isOne
                    (yunFactorsContributionWithLevel
                      (f / monicGcd f (DensePoly.derivative f))
                      (monicGcd f (DensePoly.derivative f)) m 1 fuel).2 = false →
                  (DensePoly.derivative
                      (yunFactorsContributionWithLevel
                        (f / monicGcd f (DensePoly.derivative f))
                        (monicGcd f (DensePoly.derivative f)) m 1 fuel).2).isZero = true :=
              yunFactorsContributionWithLevel_residual_derivative_zero_of_derivative_split
                hp f m 1 fuel hbound hzero_false hdf_false hstateLvl
            have hloop_deriv :
                isOne
                    (yunFactorsWithLevel
                      (f / monicGcd f (DensePoly.derivative f))
                      (monicGcd f (DensePoly.derivative f)) m 1 fuel []).2 = false →
                  (DensePoly.derivative
                      (yunFactorsWithLevel
                        (f / monicGcd f (DensePoly.derivative f))
                        (monicGcd f (DensePoly.derivative f)) m 1 fuel []).2).isZero = true := by
              intro hone_false
              rw [hbridge]
              exact hderiv_impl (by rw [← hbridge]; exact hone_false)
            simp only [squareFreeAuxRevResidualSatisfied]
            rw [if_neg (by simp [hzero_false]), if_neg (by simp [hdf_false])]
            refine ⟨?_, ?_⟩
            · by_cases hone :
                  isOne
                    (yunFactorsWithLevel
                      (f / monicGcd f (DensePoly.derivative f))
                      (monicGcd f (DensePoly.derivative f)) m 1 fuel []).2 = true
              · exact Or.inl hone
              · refine Or.inr (hloop_deriv ?_)
                cases h : isOne
                    (yunFactorsWithLevel
                      (f / monicGcd f (DensePoly.derivative f))
                      (monicGcd f (DensePoly.derivative f)) m 1 fuel []).2
                · rfl
                · exact False.elim (hone h)
            · intro hone_false
              have hroot_fuel :
                  (pthRoot
                      (yunFactorsWithLevel
                        (f / monicGcd f (DensePoly.derivative f))
                        (monicGcd f (DensePoly.derivative f)) m 1 fuel []).2).size < fuel :=
                yunFactorsWithLevel_pthRoot_tail_fuel_bound hp f
                  (f / monicGcd f (DensePoly.derivative f))
                  (monicGcd f (DensePoly.derivative f)) m 1 fuel
                  hstate hreachable hloop_bound hone_false (hloop_deriv hone_false)
              exact ih _ (m * p) hroot_fuel


end FpPoly
end Hex
