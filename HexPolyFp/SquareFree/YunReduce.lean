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
public import HexPolyFp.SquareFree.YunContribution
import all HexPolyFp.SquareFree.Algebra
import all HexPolyFp.SquareFree.YunContribution

public section
set_option backward.proofsInPublic true

/-!
The `squareFreeAuxRev` / `squareFreeAux` recursion and its reconstruction
invariant, plus the pairwise-reachable derivative-split machinery.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]
/--
Recursive residual derivative-zero invariant for the `squareFreeAuxRev`
loop. At each non-trivial step the residual `loop.2` is either trivial
(`isOne`) or has zero derivative, and the recursion into `pthRoot loop.2`
continues to satisfy the same invariant.
-/
private def squareFreeAuxRevResidualSatisfied
    (g : FpPoly p) (m : Nat) : Nat → Prop
  | 0 => True
  | fuel + 1 =>
      if g.isZero then True
      else if (DensePoly.derivative g).isZero then
        squareFreeAuxRevResidualSatisfied (pthRoot g) (m * p) fuel
      else
        let g_inner := monicGcd g (DensePoly.derivative g)
        let c_inner := g / g_inner
        let loop := yunFactorsWithLevel c_inner g_inner m 1 fuel []
        ((isOne loop.2 = true) ∨ (DensePoly.derivative loop.2).isZero = true) ∧
          ((isOne loop.2 = false) →
            squareFreeAuxRevResidualSatisfied
              (pthRoot loop.2) (m * p) fuel)

/--
Tail-recursive square-free decomposition over `F_p[x]`, accumulating factors
in reverse output order. A derivative-zero branch descends through the formal
`p`-th root and scales multiplicities by `p`.
-/
@[expose]
def squareFreeAuxRev (f : FpPoly p) (multiplicity : Nat) :
    Nat → List (SquareFreeFactor p) → List (SquareFreeFactor p)
  | 0, accRev => accRev
  | fuel + 1, accRev =>
      if f.isZero then
        accRev
      else
        let df := DensePoly.derivative f
        if df.isZero then
          squareFreeAuxRev (pthRoot f) (multiplicity * p) fuel accRev
        else
          let g := monicGcd f df
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          let accRev' := loop.1
          let repeated := loop.2
          if isOne repeated then
            accRev'
          else
            squareFreeAuxRev (pthRoot repeated) (multiplicity * p) fuel accRev'

/--
Recursive square-free decomposition over `F_p[x]`. A derivative-zero branch
descends through the formal `p`-th root and scales multiplicities by `p`.
-/
@[expose]
def squareFreeAux (f : FpPoly p) (multiplicity : Nat)
    (fuel : Nat) : List (SquareFreeFactor p) :=
  (squareFreeAuxRev f multiplicity fuel []).reverse

private theorem squareFreeAuxRev_reconstruction_invariant
    (f : FpPoly p) (multiplicity fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    weightedProduct (squareFreeAuxRev f multiplicity fuel accRev).reverse =
      weightedProduct accRev.reverse *
        squareFreeAuxRevContribution f multiplicity fuel := by
  induction fuel generalizing f multiplicity accRev with
  | zero =>
      simp [squareFreeAuxRev, squareFreeAuxRevContribution]
  | succ fuel ih =>
      simp only [squareFreeAuxRev, squareFreeAuxRevContribution]
      by_cases hzero : f.isZero
      · simp [hzero]
      · simp [hzero]
        by_cases hdf : (DensePoly.derivative f).isZero
        · simpa [hdf] using ih (pthRoot f) (multiplicity * p) accRev
        · simp [hdf]
          let g := monicGcd f (DensePoly.derivative f)
          let c := f / g
          let loop := yunFactorsWithLevel c g multiplicity 1 fuel accRev
          let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
          have hloop :=
            yunFactorsWithLevel_reconstruction_invariant c g multiplicity 1 fuel accRev
          have hloop_repeated : loop.2 = contribution.2 := by
            simpa [loop, contribution] using hloop.1
          have hloop_product :
              weightedProduct loop.1.reverse =
                weightedProduct accRev.reverse * contribution.1 := by
            simpa [loop, contribution] using hloop.2
          by_cases hrepeated : isOne loop.2
          · have hcontribution_one : isOne contribution.2 := by
              simpa [hloop_repeated] using hrepeated
            simpa [g, c, loop, contribution, hrepeated, hcontribution_one] using hloop_product
          · have hcontribution_not_one : isOne contribution.2 = false := by
              cases hc : isOne contribution.2
              · exact rfl
              · exfalso
                apply hrepeated
                simpa [hloop_repeated] using hc
            have hrec :
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  weightedProduct loop.1.reverse *
                    squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := by
              exact ih (pthRoot loop.2) (multiplicity * p) loop.1
            have hrec_contribution :
                squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel =
                  squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel := by
              rw [hloop_repeated]
            have hcalc :
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse =
                  weightedProduct accRev.reverse *
                    (contribution.1 *
                      squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel) := by
              calc
                weightedProduct (squareFreeAuxRev (pthRoot loop.2) (multiplicity * p) fuel loop.1).reverse
                    = weightedProduct loop.1.reverse *
                        squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := hrec
                _ = (weightedProduct accRev.reverse * contribution.1) *
                        squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel := by
                      rw [hloop_product]
                _ = weightedProduct accRev.reverse *
                        (contribution.1 *
                          squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel) := by
                      exact DensePoly.mul_assoc_poly
                        (weightedProduct accRev.reverse) contribution.1
                        (squareFreeAuxRevContribution (pthRoot loop.2) (multiplicity * p) fuel)
                _ = weightedProduct accRev.reverse *
                        (contribution.1 *
                          squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel) := by
                      rw [hrec_contribution]
            simpa [g, c, loop, contribution, hrepeated, hcontribution_not_one, hloop_repeated]
              using hcalc

private def squareFreeFactorCoprimeRel :
    SquareFreeFactor p → SquareFreeFactor p → Prop :=
  fun a b => (normalizeMonic (DensePoly.gcd a.factor b.factor)).2 = 1

private def squareFreeFactorSquareFreeRel (sf : SquareFreeFactor p) : Prop :=
  (normalizeMonic (DensePoly.gcd sf.factor (DensePoly.derivative sf.factor))).2 = 1

private inductive yunFactorsPairwiseReachable :
    FpPoly p → FpPoly p → Nat → Prop
  | derivativeSplit (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
      (hdf : (DensePoly.derivative f).isZero ≠ true) :
      yunFactorsPairwiseReachable
        (f / monicGcd f (DensePoly.derivative f))
        (monicGcd f (DensePoly.derivative f))
        fuel
  | step (c w : FpPoly p) (fuel : Nat) :
      yunFactorsPairwiseReachable c w (fuel + 1) →
      yunFactorsPairwiseReachable
        (monicGcd c w)
        (w / monicGcd c w)
        fuel

private theorem yunFactorsPairwiseReachable_of_derivative_split
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (fuel : Nat)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    yunFactorsPairwiseReachable
      (f / monicGcd f (DensePoly.derivative f))
      (monicGcd f (DensePoly.derivative f))
      fuel :=
  yunFactorsPairwiseReachable.derivativeSplit hp f fuel hdf

private theorem yunFactorsPairwiseReachable_step
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1)) :
    yunFactorsPairwiseReachable
      (monicGcd c w)
      (w / monicGcd c w)
      fuel :=
  yunFactorsPairwiseReachable.step c w fuel hreachable

private def yunFactorsCurrentTailCoprime
    (c w : FpPoly p) (base level fuel : Nat) : Prop :=
  let y := monicGcd c w
  let z := c / y
  ∀ sf ∈ (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse,
    squareFreeFactorCoprimeRel { factor := z, multiplicity := base * level } sf

private def yunFactorsPairwiseReady
    (c w : FpPoly p) (base : Nat) : Nat → Nat → Prop
  | _, 0 => True
  | level, fuel + 1 =>
      let y := monicGcd c w
      let z := c / y
      yunFactorsPairwiseReady y (w / y) base (level + 1) fuel ∧
        (isOne c = false →
          isOne z = false →
            yunFactorsCurrentTailCoprime c w base level fuel)

private theorem yunFactorsPairwiseReady_succ_of_current_tail
    (c w : FpPoly p) (base level fuel : Nat)
    (htail :
      yunFactorsPairwiseReady
        (monicGcd c w)
        (w / monicGcd c w)
        base
        (level + 1)
        fuel)
    (hcurrent :
      isOne c = false →
        isOne (c / monicGcd c w) = false →
          yunFactorsCurrentTailCoprime c w base level fuel) :
    yunFactorsPairwiseReady c w base level (fuel + 1) := by
  simpa [yunFactorsPairwiseReady] using And.intro htail hcurrent

private structure yunFactorsPairwiseInvariant
    (c w : FpPoly p) (base level fuel : Nat) : Prop where
  reachable : yunFactorsPairwiseReachable c w fuel
  ready : yunFactorsPairwiseReady c w base level fuel

private theorem pairwise_append_of_cross
    {α : Type} (r : α → α → Prop) {xs ys : List α} :
    xs.Pairwise r →
    ys.Pairwise r →
    (∀ x ∈ xs, ∀ y ∈ ys, r x y) →
    (xs ++ ys).Pairwise r := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      intro hxs hys hcross
      simp only [List.pairwise_cons] at hxs ⊢
      constructor
      · intro z hz
        rcases List.mem_append.mp hz with hmem | hmem
        · exact hxs.1 z hmem
        · exact hcross x (by simp) z hmem
      · apply ih hxs.2 hys
        intro a ha b hb
        exact hcross a (by simp [ha]) b hb

private theorem yunFactorsWithLevel_reverse_append
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactorsWithLevel c w base level fuel accRev).1.reverse =
      accRev.reverse ++ (yunFactorsWithLevel c w base level fuel []).1.reverse := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simp [yunFactorsWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (level + 1) accRev
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
          have hacc := ih y (w / y) (level + 1) (sf :: accRev)
          have hsingle := ih y (w / y) (level + 1) [sf]
          simpa [y, z, hz, sf] using
            (calc
              (yunFactorsWithLevel y (w / y) base (level + 1) fuel (sf :: accRev)).1.reverse
                  = (sf :: accRev).reverse ++
                      (yunFactorsWithLevel y (w / y) base (level + 1) fuel []).1.reverse := hacc
              _ = accRev.reverse ++
                    (yunFactorsWithLevel y (w / y) base (level + 1) fuel [sf]).1.reverse := by
                  rw [hsingle]
                  simp [List.reverse_cons, List.append_assoc])

private theorem yunFactorsWithLevel_repeated_eq_nil
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactorsWithLevel c w base level fuel accRev).2 =
      (yunFactorsWithLevel c w base level fuel []).2 := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simp [yunFactorsWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (level + 1) accRev
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
          have hacc := ih y (w / y) (level + 1) (sf :: accRev)
          have hsingle := ih y (w / y) (level + 1) [sf]
          simpa [y, z, hz, sf] using hacc.trans hsingle.symm

private theorem dvd_trans_poly
    {a b c : FpPoly p} (hab : a ∣ b) (hbc : b ∣ c) :
    a ∣ c := by
  rcases hab with ⟨x, hx⟩
  rcases hbc with ⟨y, hy⟩
  refine ⟨x * y, ?_⟩
  calc c
      = b * y := hy
    _ = (a * x) * y := by rw [hx]
    _ = a * (x * y) := DensePoly.mul_assoc_poly a x y

private theorem yunFactorsWithLevel_repeated_dvd_repeated_of_acc
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    (yunFactorsWithLevel c w base level fuel accRev).2 ∣ w := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  induction fuel generalizing c w level accRev with
  | zero =>
      simp [yunFactorsWithLevel]
      exact ⟨1, by rw [mul_one]⟩
  | succ fuel ih =>
      simp only [yunFactorsWithLevel]
      by_cases hc : isOne c
      · simp [hc]
        exact ⟨1, by rw [mul_one]⟩
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        have hdiv_tail : w / y ∣ w := by
          exact ⟨y, by simpa [y] using (div_monicGcd_right_mul_reconstruct hp c w).symm⟩
        by_cases hz : isOne z
        · exact dvd_trans_poly
            (by simpa [y, z, hz] using ih y (w / y) (level + 1) accRev)
            hdiv_tail
        · let sf : SquareFreeFactor p := { factor := z, multiplicity := base * level }
          exact dvd_trans_poly
            (by simpa [y, z, hz, sf] using ih y (w / y) (level + 1) (sf :: accRev))
            hdiv_tail

private theorem yunFactorsWithLevel_repeated_dvd_repeated
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (base level fuel : Nat) :
    (yunFactorsWithLevel c w base level fuel []).2 ∣ w := by
  exact yunFactorsWithLevel_repeated_dvd_repeated_of_acc c w base level fuel []

private def yunFactorsContributionResidualDerivativeZero
    (c w : FpPoly p) (multiplicity fuel : Nat) : Prop :=
  let contribution := yunFactorsContribution c w multiplicity fuel
  isOne contribution.2 = false →
    (DensePoly.derivative contribution.2).isZero = true

private def yunFactorsContributionResidualComplete
    (c w : FpPoly p) (multiplicity : Nat) : Nat → Prop
  | 0 =>
      isOne w = false → (DensePoly.derivative w).isZero = true
  | fuel + 1 =>
      if isOne c then
        isOne w = false → (DensePoly.derivative w).isZero = true
      else
        let y := monicGcd c w
        yunFactorsContributionResidualComplete y (w / y) (multiplicity + 1) fuel

private theorem yunFactorsContributionResidualDerivativeZero_of_complete
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hcomplete :
      yunFactorsContributionResidualComplete c w multiplicity fuel) :
    yunFactorsContributionResidualDerivativeZero c w multiplicity fuel := by
  induction fuel generalizing c w multiplicity with
  | zero =>
      intro hrepeated
      simpa [yunFactorsContributionResidualDerivativeZero,
        yunFactorsContributionResidualComplete, yunFactorsContribution]
        using hcomplete hrepeated
  | succ fuel ih =>
      intro hrepeated
      by_cases hc : isOne c = true
      · have hcomplete_here :
            isOne w = false → (DensePoly.derivative w).isZero = true := by
          simpa [yunFactorsContributionResidualComplete, hc] using hcomplete
        have hrepeated_here : isOne w = false := by
          simpa [yunFactorsContribution, hc] using hrepeated
        simpa [yunFactorsContributionResidualDerivativeZero,
          yunFactorsContribution, hc] using hcomplete_here hrepeated_here
      · let y := monicGcd c w
        have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have hcomplete_tail :
            yunFactorsContributionResidualComplete y (w / y) (multiplicity + 1) fuel := by
          simpa [yunFactorsContributionResidualComplete, hc_false, y] using hcomplete
        have htail :
            yunFactorsContributionResidualDerivativeZero y (w / y) (multiplicity + 1) fuel :=
          ih y (w / y) (multiplicity + 1) hcomplete_tail
        have hrepeated_tail :
            isOne (yunFactorsContribution y (w / y) (multiplicity + 1) fuel).2 = false := by
          simpa [yunFactorsContribution, hc_false, y] using hrepeated
        simpa [yunFactorsContributionResidualDerivativeZero,
          yunFactorsContribution, hc_false, y] using htail hrepeated_tail

/--
The residual component of the scaled Yun contribution
`yunFactorsContributionWithLevel` agrees with that of the unscaled
`yunFactorsContribution`. The two recursions share an identical
`.2`-projection: the base/level scaling only affects the emitted
`pow z (base * level)` exponents in the first component.
-/
private theorem yunFactorsContributionWithLevel_residual_eq_yunFactorsContribution
    (c w : FpPoly p) (base level fuel : Nat) :
    (yunFactorsContributionWithLevel c w base level fuel).2 =
      (yunFactorsContribution c w level fuel).2 := by
  induction fuel generalizing c w level with
  | zero =>
      simp [yunFactorsContributionWithLevel, yunFactorsContribution]
  | succ fuel ih =>
      simp only [yunFactorsContributionWithLevel, yunFactorsContribution]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        exact ih (monicGcd c w) (w / monicGcd c w) (level + 1)

/--
Derivative-zero of the residual carries between the scaled
`yunFactorsContributionWithLevel` and the unscaled
`yunFactorsContribution`: both have the same residual, so the
derivative-zero fact transports directly.
-/
private theorem yunFactorsContributionWithLevel_residual_derivative_zero_of_unscaled
    (c w : FpPoly p) (base level fuel : Nat)
    (hresidual : yunFactorsContributionResidualDerivativeZero c w level fuel) :
    isOne (yunFactorsContributionWithLevel c w base level fuel).2 = false →
      (DensePoly.derivative
          (yunFactorsContributionWithLevel c w base level fuel).2).isZero = true := by
  intro hone
  rw [yunFactorsContributionWithLevel_residual_eq_yunFactorsContribution] at hone ⊢
  exact hresidual hone

private theorem ne_zero_of_isZero_false {f : FpPoly p}
    (hf : f.isZero = false) :
    f ≠ 0 := by
  intro hzero
  rw [hzero] at hf
  change (0 : FpPoly p).isZero = false at hf
  have hzero_isZero : (0 : FpPoly p).isZero = true := rfl
  rw [hzero_isZero] at hf
  cases hf

/-- The monic normalization absorbs a nonzero constant scalar: scaling the
input by `C v` (`v ≠ 0`) leaves the monic associate unchanged. This is the
algebraic root of `monicGcd_scalar_invariant`. -/
private theorem normalizeMonic_C_mul_snd
    [ZMod64.PrimeModulus p] {v : ZMod64 p} (hv : v ≠ 0) (h : FpPoly p) :
    (normalizeMonic (DensePoly.C v * h)).2 = (normalizeMonic h).2 := by
  cases hz : h.isZero with
  | true =>
      have hh0 : h = 0 := eq_zero_of_isZero_true h hz
      subst hh0
      rw [mul_zero]
  | false =>
      have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false h hz
      have hsize : h.size ≠ 0 := by
        simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
          Bool.not_eq_true] using hz
      have hCvh_ne : (DensePoly.C v * h).isZero = false := by
        cases hcvh : (DensePoly.C v * h).isZero with
        | false => rfl
        | true =>
            exfalso
            have hsz0 : (DensePoly.C v * h).size = 0 :=
              size_eq_zero_of_isZero_true _ hcvh
            rw [C_mul_eq_scale, scale_size_eq_of_ne_zero hv h] at hsz0
            exact hsize hsz0
      rw [normalizeMonic_nonzero h hz,
          normalizeMonic_nonzero (DensePoly.C v * h) hCvh_ne]
      show DensePoly.scale (DensePoly.leadingCoeff (DensePoly.C v * h))⁻¹
            (DensePoly.C v * h) =
          DensePoly.scale (DensePoly.leadingCoeff h)⁻¹ h
      rw [C_mul_eq_scale,
          leadingCoeff_scale_of_ne_zero_of_nonzero hv h hsize,
          scale_scale]
      congr 1
      have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
      have hva_ne : v * DensePoly.leadingCoeff h ≠ 0 := by
        intro h0
        rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp h0 with h1 | h1
        · exact hv h1
        · exact hlead_ne h1
      have hva_inv : v * DensePoly.leadingCoeff h * (v * DensePoly.leadingCoeff h)⁻¹ = 1 :=
        zmod64_mul_inv_eq_one_of_prime_ne_zero hp hva_ne
      have ha_inv : DensePoly.leadingCoeff h * (DensePoly.leadingCoeff h)⁻¹ = 1 :=
        zmod64_mul_inv_eq_one_of_prime_ne_zero hp hlead_ne
      have hv_inv : v * v⁻¹ = 1 :=
        zmod64_mul_inv_eq_one_of_prime_ne_zero hp hv
      grind

/-- Scaling both gcd inputs by independent nonzero constants leaves the monic
gcd unchanged. This is the load-bearing scalar-leak elimination: with monic
normalization the unit the raw gcd would pick up is absorbed, so the recursion
variables of the scaled and unscaled Yun loops coincide exactly. -/
private theorem monicGcd_scalar_invariant
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {u_c u_w : ZMod64 p} (hu_c : u_c ≠ 0) (hu_w : u_w ≠ 0) (c w : FpPoly p) :
    monicGcd (DensePoly.C u_c * c) (DensePoly.C u_w * w) = monicGcd c w := by
  obtain ⟨v, hv, hgcd⟩ :=
    gcd_C_mul_left_C_mul_right_eq_C_mul_gcd hp u_c u_w hu_c hu_w c w
  simp only [monicGcd_def]
  rw [hgcd, normalizeMonic_C_mul_snd hv]

private theorem pow_C_form
    [ZMod64.PrimeModulus p] (hp : Hex.Nat.Prime p)
    {a : ZMod64 p} (ha : a ≠ 0) :
    ∀ n : Nat, ∃ b : ZMod64 p, b ≠ 0 ∧
      pow (DensePoly.C a : FpPoly p) n = DensePoly.C b
  | 0 =>
      ⟨1, zmod64_one_ne_zero_of_prime hp, by
        rw [pow_eq_powLinear]
        rfl⟩
  | n + 1 =>
      by
        obtain ⟨b, hb, hpow⟩ := pow_C_form hp ha n
        refine ⟨b * a, ?_, ?_⟩
        · intro hzero
          rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hzero with hb_zero | ha_zero
          · exact hb hb_zero
          · exact ha ha_zero
        · rw [pow_succ, hpow, fpPoly_C_mul_C_eq]

private theorem coeff_derivative (f : FpPoly p) (n : Nat) :
    (DensePoly.derivative f).coeff n =
      ((n + 1 : Nat) : ZMod64 p) * f.coeff (n + 1) :=
  DensePoly.coeff_derivative f n (Lean.Grind.Semiring.mul_zero _)

private theorem derivative_degree?_lt_self_of_ne_zero
    (f : FpPoly p) (hder_ne : DensePoly.derivative f ≠ 0) :
    (DensePoly.derivative f).degree?.getD 0 < f.degree?.getD 0 := by
  have hder_pos : 0 < (DensePoly.derivative f).size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hder_ne
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le (DensePoly.derivative f) (by omega)
  let n := (DensePoly.derivative f).size - 1
  have hlast :
      (DensePoly.derivative f).coeff n ≠ 0 := by
    exact
      DensePoly.coeff_last_ne_zero_of_pos_size (DensePoly.derivative f) hder_pos
  have hn_lt : n + 1 < f.size := by
    by_cases hlt : n + 1 < f.size
    · exact hlt
    · have hf_le : f.size ≤ n + 1 := Nat.le_of_not_gt hlt
      have hcoeff : f.coeff (n + 1) = 0 :=
        DensePoly.coeff_eq_zero_of_size_le f hf_le
      exfalso
      apply hlast
      rw [coeff_derivative f n, hcoeff]
      exact (Lean.Grind.Semiring.mul_zero ((n + 1 : Nat) : ZMod64 p)).symm
  have hf_pos : 0 < f.size := by omega
  have hder_degree :
      (DensePoly.derivative f).degree? =
        some ((DensePoly.derivative f).size - 1) := by
    unfold DensePoly.degree?
    simp [Nat.ne_of_gt hder_pos]
  have hf_degree : f.degree? = some (f.size - 1) := by
    unfold DensePoly.degree?
    simp [Nat.ne_of_gt hf_pos]
  rw [hder_degree, hf_degree]
  simp
  omega

private theorem derivative_isZero_true_of_dvd_self_derivative
    [ZMod64.PrimeModulus p] (f : FpPoly p)
    (hdvd : f ∣ DensePoly.derivative f) :
    (DensePoly.derivative f).isZero = true := by
  cases hder : (DensePoly.derivative f).isZero with
  | true => rfl
  | false =>
      have hder_ne : DensePoly.derivative f ≠ 0 :=
        ne_zero_of_isZero_false hder
      have hf_ne : f ≠ 0 := by
        intro hf_zero
        apply hder_ne
        rw [hf_zero]
        exact DensePoly.derivative_zero
      rcases hdvd with ⟨q, hq⟩
      have hq_ne : q ≠ 0 := by
        intro hq_zero
        apply hder_ne
        rw [hq, hq_zero, mul_zero]
      have hdeg_mul := degree?_mul_eq_add_degree? f q hf_ne hq_ne
      have hdeg_lt := derivative_degree?_lt_self_of_ne_zero f hder_ne
      have hdeg_eq :
          (DensePoly.derivative f).degree?.getD 0 = (f * q).degree?.getD 0 := by
        rw [hq]
      rw [hdeg_mul] at hdeg_eq
      omega

/-- `powLinear d n ≠ 0` for any exponent `n` when the base `d` is nonzero, by induction on `n`. -/
private theorem powLinear_ne_zero
    [ZMod64.PrimeModulus p] {d : FpPoly p}
    (hd : d ≠ 0) :
    ∀ n, powLinear d n ≠ 0 := by
  intro n
  induction n with
  | zero =>
      intro hone
      have hcoeff := congrArg (fun f : FpPoly p => f.coeff 0) hone
      change (1 : FpPoly p).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
      change (DensePoly.C (1 : ZMod64 p)).coeff 0 = (0 : FpPoly p).coeff 0 at hcoeff
      rw [DensePoly.coeff_C, DensePoly.coeff_zero] at hcoeff
      exact zmod64_one_ne_zero_of_prime
        (ZMod64.PrimeModulus.prime (p := p)) hcoeff
  | succ n ih =>
      change powLinear d n * d ≠ 0
      exact mul_ne_zero_of_ne_zero ih hd

/-- `pow d n ≠ 0` for a nonzero base `d`, transported from `powLinear_ne_zero` via `pow_eq_powLinear`. -/
private theorem pow_ne_zero
    [ZMod64.PrimeModulus p] {d : FpPoly p}
    (hd : d ≠ 0) (n : Nat) :
    pow d n ≠ 0 := by
  rw [pow_eq_powLinear]
  exact powLinear_ne_zero hd n

/-- The degree of `powLinear d n` grows linearly: it equals `n * deg d` for a nonzero base `d`. -/
private theorem powLinear_degree?_getD
    [ZMod64.PrimeModulus p] {d : FpPoly p}
    (hd : d ≠ 0) :
    ∀ n, (powLinear d n).degree?.getD 0 = n * d.degree?.getD 0 := by
  intro n
  induction n with
  | zero =>
      change (1 : FpPoly p).degree?.getD 0 = 0 * d.degree?.getD 0
      change (DensePoly.C (1 : ZMod64 p)).degree?.getD 0 = 0 * d.degree?.getD 0
      rw [DensePoly.degree?_C_getD]
      simp
  | succ n ih =>
      change (powLinear d n * d).degree?.getD 0 =
        (n + 1) * d.degree?.getD 0
      rw [degree?_mul_eq_add_degree? (powLinear d n) d
        (powLinear_ne_zero hd n) hd, ih, Nat.succ_mul]

/-- The same linear degree identity `deg (pow d n) = n * deg d`, transported from `powLinear_degree?_getD`. -/
private theorem pow_degree?_getD
    [ZMod64.PrimeModulus p] {d : FpPoly p}
    (hd : d ≠ 0) (n : Nat) :
    (pow d n).degree?.getD 0 = n * d.degree?.getD 0 := by
  rw [pow_eq_powLinear]
  exact powLinear_degree?_getD hd n

/-- If every power `pow d n` divides a fixed nonzero `g`, then `d` is a unit (`d ∣ 1`): a positive-degree `d` would force `pow d n` past the degree of `g`. -/
private theorem dvd_one_of_all_powers_dvd_nonzero
    [ZMod64.PrimeModulus p] {d g : FpPoly p}
    (hg : g.isZero = false)
    (hall : ∀ n : Nat, pow d n ∣ g) :
    d ∣ (1 : FpPoly p) := by
  have hg_ne : g ≠ 0 := ne_zero_of_isZero_false hg
  have hd_ne : d ≠ 0 := by
    intro hd
    rcases hall 1 with ⟨q, hq⟩
    apply hg_ne
    rw [pow_one, hd, zero_mul] at hq
    exact hq
  have hd_degree_zero : d.degree?.getD 0 = 0 := by
    by_cases hdeg_zero : d.degree?.getD 0 = 0
    · exact hdeg_zero
    · have hdeg_pos : 0 < d.degree?.getD 0 := Nat.pos_of_ne_zero hdeg_zero
      let n := g.degree?.getD 0 + 1
      rcases hall n with ⟨q, hq⟩
      have hq_ne : q ≠ 0 := by
        intro hq_zero
        apply hg_ne
        rw [hq, hq_zero, mul_zero]
      have hpow_ne : pow d n ≠ 0 := pow_ne_zero hd_ne n
      have hdeg_mul := degree?_mul_eq_add_degree? (pow d n) q hpow_ne hq_ne
      have hdeg_pow := pow_degree?_getD hd_ne n
      have hdeg_eq :
          g.degree?.getD 0 = (pow d n * q).degree?.getD 0 := by
        rw [hq]
      rw [hdeg_mul, hdeg_pow] at hdeg_eq
      have hpow_large : g.degree?.getD 0 < n * d.degree?.getD 0 := by
        have hmul_ge :
            g.degree?.getD 0 + 1 ≤
              (g.degree?.getD 0 + 1) * d.degree?.getD 0 := by
          exact Nat.le_mul_of_pos_right (g.degree?.getD 0 + 1) hdeg_pos
        dsimp [n]
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hmul_ge
      have hpow_le : n * d.degree?.getD 0 ≤ g.degree?.getD 0 := by
        omega
      exact False.elim ((Nat.not_lt_of_ge hpow_le) hpow_large)
  have hd_size_pos : 0 < d.size := by
    apply Nat.pos_of_ne_zero
    intro hsize
    apply hd_ne
    apply DensePoly.ext_coeff
    intro n
    rw [DensePoly.coeff_zero]
    exact DensePoly.coeff_eq_zero_of_size_le d (by omega)
  have hd_size_ne : d.size ≠ 0 := Nat.pos_iff_ne_zero.mp hd_size_pos
  have hd_degree : d.degree? = some (d.size - 1) := by
    unfold DensePoly.degree?
    simp [hd_size_ne]
  have hd_size_one : d.size = 1 := by
    rw [hd_degree] at hd_degree_zero
    simp at hd_degree_zero
    omega
  have hcoeff_ne : d.coeff 0 ≠ 0 := by
    have hlast := DensePoly.coeff_last_ne_zero_of_pos_size d hd_size_pos
    rw [hd_size_one] at hlast
    exact hlast
  have hd_const : d = DensePoly.C (d.coeff 0) := by
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        rw [DensePoly.coeff_C]
        simp
    | succ n =>
        have hsize_le : d.size ≤ n + 1 := by
          rw [hd_size_one]
          omega
        rw [DensePoly.coeff_eq_zero_of_size_le d hsize_le, DensePoly.coeff_C]
        simp
  rw [hd_const, ← scale_one_poly]
  exact dvd_scale_self_of_ne_zero hcoeff_ne (1 : FpPoly p)

private theorem derivativeSplit_quotient_common_dvd_derivative_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    let g := monicGcd f (DensePoly.derivative f)
    let c := f / g
    ∀ d : FpPoly p,
      d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p) := by
  dsimp
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro d hdc hddc
  let g := monicGcd f (DensePoly.derivative f)
  have hdf_false : (DensePoly.derivative f).isZero = false := by
    cases h : (DensePoly.derivative f).isZero
    · rfl
    · exact False.elim (hdf h)
  have hg_nonzero : g.isZero = false := by
    simpa [g] using
      monicGcd_isZero_false_of_gcd_nonzero f (DensePoly.derivative f)
        (gcd_isZero_false_of_right_isZero_false f (DensePoly.derivative f) hdf_false)
  have hbase : pow d 0 ∣ g := by
    rw [pow_eq_powLinear]
    change (1 : FpPoly p) ∣ g
    exact ⟨g, by rw [one_mul]⟩
  have hstep :
      ∀ n, pow d n ∣ g → pow d (n + 1) ∣ g := by
    intro n hpow
    simpa [g] using
      derivativeSplit_quotient_pow_succ_dvd_gcd f d hdc hddc n (by simpa [g] using hpow)
  have hall : ∀ n : Nat, pow d n ∣ g := by
    intro n
    induction n with
    | zero =>
        exact hbase
    | succ n ih =>
        exact hstep n ih
  exact dvd_one_of_all_powers_dvd_nonzero hg_nonzero hall

private theorem derivativeSplit_residual_derivative_zero_of_coprime
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (_hdf : (DensePoly.derivative f).isZero = false)
    (hcoprime : ∀ d : FpPoly p,
      d ∣ (f / monicGcd f (DensePoly.derivative f)) →
      d ∣ monicGcd f (DensePoly.derivative f) →
      d ∣ (1 : FpPoly p)) :
    (DensePoly.derivative (monicGcd f (DensePoly.derivative f))).isZero = true := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  have hprod : c * g = f := by
    simpa [c, g] using div_monicGcd_mul_reconstruct hp f (DensePoly.derivative f)
  have hg_dvd_df : g ∣ DensePoly.derivative f := by
    simpa [g] using monicGcd_dvd_right hp f (DensePoly.derivative f)
  have hdf_prod :
      DensePoly.derivative f =
        DensePoly.derivative c * g + c * DensePoly.derivative g := by
    rw [← hprod]
    exact DensePoly.derivative_mul c g
  have hg_dvd_left : g ∣ DensePoly.derivative c * g := by
    exact ⟨DensePoly.derivative c, DensePoly.mul_comm_poly (DensePoly.derivative c) g⟩
  have hg_dvd_sum :
      g ∣ DensePoly.derivative c * g + c * DensePoly.derivative g := by
    simpa [hdf_prod] using hg_dvd_df
  have hg_dvd_cdg : g ∣ c * DensePoly.derivative g := by
    have hsub := dvd_sub_poly hg_dvd_sum hg_dvd_left
    have hsub_eq :
        (DensePoly.derivative c * g + c * DensePoly.derivative g) -
            DensePoly.derivative c * g =
          c * DensePoly.derivative g := by
      rw [sub_eq_add_neg]
      calc
        (DensePoly.derivative c * g + c * DensePoly.derivative g) +
            -(DensePoly.derivative c * g)
            = (c * DensePoly.derivative g + DensePoly.derivative c * g) +
                -(DensePoly.derivative c * g) := by
              exact congrArg (fun x => x + -(DensePoly.derivative c * g))
                (DensePoly.add_comm_poly (DensePoly.derivative c * g)
                  (c * DensePoly.derivative g))
        _ = c * DensePoly.derivative g +
                (DensePoly.derivative c * g + -(DensePoly.derivative c * g)) := by
              exact DensePoly.add_assoc_poly
                (c * DensePoly.derivative g)
                (DensePoly.derivative c * g)
                (-(DensePoly.derivative c * g))
        _ = c * DensePoly.derivative g + 0 := by rw [add_right_neg]
        _ = c * DensePoly.derivative g := add_zero _
    simpa [hsub_eq] using hsub
  have hg_dvd_dg : g ∣ DensePoly.derivative g := by
    exact dvd_of_dvd_mul_of_common_dvd_one
      (g := g) (c := c) (h := DensePoly.derivative g)
      hg_dvd_cdg
      (by
        intro d hdc hdg
        exact hcoprime d (by simpa [c, g] using hdc) (by simpa [g] using hdg))
  exact derivative_isZero_true_of_dvd_self_derivative g hg_dvd_dg

private theorem derivativeSplit_quotient_size_one_eq_one
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hdf : (DensePoly.derivative f).isZero ≠ true) :
    let g := monicGcd f (DensePoly.derivative f)
    let c := f / g
    c.size = 1 → c = 1 := by
  dsimp
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  intro hc_size
  have hdf_false : (DensePoly.derivative f).isZero = false := by
    cases h : (DensePoly.derivative f).isZero
    · rfl
    · exact False.elim (hdf h)
  have hc_der : (DensePoly.derivative c).isZero = true :=
    derivative_isZero_true_of_size_one c hc_size
  have hcoprime :
      ∀ d : FpPoly p, d ∣ c → d ∣ g → d ∣ (1 : FpPoly p) := by
    intro d hdc _hdg
    exact derivativeSplit_quotient_common_dvd_derivative_one hp f hdf d hdc
      (by
        refine ⟨0, ?_⟩
        rw [mul_zero, eq_zero_of_isZero_true (DensePoly.derivative c) hc_der])
  have hg_der : (DensePoly.derivative g).isZero = true :=
    derivativeSplit_residual_derivative_zero_of_coprime hp f hdf_false (by
      intro d hdc hdg
      exact hcoprime d (by simpa [c, g] using hdc) (by simpa [g] using hdg))
  have hprod : c * g = f := by
    simpa [c, g] using div_monicGcd_mul_reconstruct hp f (DensePoly.derivative f)
  have hdf_zero : DensePoly.derivative f = 0 := by
    rw [← hprod]
    calc
      DensePoly.derivative (c * g) =
          DensePoly.derivative c * g + c * DensePoly.derivative g := by
            exact DensePoly.derivative_mul c g
      _ = 0 * g + c * 0 := by
            rw [eq_zero_of_isZero_true (DensePoly.derivative c) hc_der,
              eq_zero_of_isZero_true (DensePoly.derivative g) hg_der]
      _ = 0 := by simp
  exfalso
  apply hdf
  rw [hdf_zero]
  rfl

private theorem squarefree_factor_of_squarefree
    {c y : FpPoly p}
    (hyc : y ∣ c)
    (hsquarefree :
      ∀ d : FpPoly p, d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p)) :
    ∀ d : FpPoly p,
      d ∣ y → d ∣ DensePoly.derivative y → d ∣ (1 : FpPoly p) := by
  intro d hdy hdderiv
  rcases hyc with ⟨q, hq⟩
  apply hsquarefree d
  · exact dvd_trans_poly hdy ⟨q, hq⟩
  · have hderiv :
        DensePoly.derivative c =
          DensePoly.derivative y * q + y * DensePoly.derivative q := by
      rw [hq]
      exact DensePoly.derivative_mul y q
    rw [hderiv]
    exact dvd_add_poly
      (dvd_mul_right_of_dvd (a := DensePoly.derivative y) (b := q) (d := d) hdderiv)
      (dvd_mul_right_of_dvd (a := y) (b := DensePoly.derivative q) (d := d) hdy)

private theorem yunFactorsPairwiseReachable_current_squarefree
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel) :
    ∀ d : FpPoly p,
      d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p) := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  induction hreachable with
  | derivativeSplit hp f fuel hdf =>
      intro d hdc hddc
      exact derivativeSplit_quotient_common_dvd_derivative_one hp f hdf d hdc hddc
  | step c w fuel _ ih =>
      exact squarefree_factor_of_squarefree
        (monicGcd_dvd_left hp c w) ih

private theorem yunFactorsPairwiseReachable_common_dvd_one
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1)) :
    ∀ d : FpPoly p,
      d ∣ c / monicGcd c w →
        d ∣ monicGcd c w →
          d ∣ (1 : FpPoly p) := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  intro d hdz hdy
  have hsquarefree :
      ∀ d : FpPoly p,
        d ∣ c → d ∣ DensePoly.derivative c → d ∣ (1 : FpPoly p) :=
    yunFactorsPairwiseReachable_current_squarefree c w (fuel + 1) hreachable
  apply hsquarefree d
  · let y := monicGcd c w
    let z := c / y
    have hprod : z * y = c := by
      simpa [z, y] using div_monicGcd_mul_reconstruct hp c w
    rw [← hprod]
    exact dvd_mul_right_of_dvd (a := z) (b := y) (d := d)
        (by simpa [z, y] using hdz)
  · exact yunStep_common_dvd_derivative_current c w d hdz hdy

private theorem dvd_mul_derivative_right_of_dvd_derivative_product
    (c w : FpPoly p)
    (hprev : w ∣ DensePoly.derivative (c * w)) :
    w ∣ c * DensePoly.derivative w := by
  have hw_dvd_left : w ∣ DensePoly.derivative c * w :=
    ⟨DensePoly.derivative c, DensePoly.mul_comm_poly (DensePoly.derivative c) w⟩
  have hder :
      DensePoly.derivative (c * w) =
        DensePoly.derivative c * w + c * DensePoly.derivative w :=
    DensePoly.derivative_mul c w
  have hsub := dvd_sub_poly (by simpa [hder] using hprev) hw_dvd_left
  have hsub_eq :
      (DensePoly.derivative c * w + c * DensePoly.derivative w) -
          DensePoly.derivative c * w =
        c * DensePoly.derivative w := by
    rw [sub_eq_add_neg]
    calc
      (DensePoly.derivative c * w + c * DensePoly.derivative w) +
          -(DensePoly.derivative c * w)
          = (c * DensePoly.derivative w + DensePoly.derivative c * w) +
              -(DensePoly.derivative c * w) := by
            exact congrArg (fun x => x + -(DensePoly.derivative c * w))
              (DensePoly.add_comm_poly
                (DensePoly.derivative c * w)
                (c * DensePoly.derivative w))
      _ = c * DensePoly.derivative w +
              (DensePoly.derivative c * w + -(DensePoly.derivative c * w)) := by
            exact DensePoly.add_assoc_poly
              (c * DensePoly.derivative w)
              (DensePoly.derivative c * w)
              (-(DensePoly.derivative c * w))
      _ = c * DensePoly.derivative w + 0 := by rw [add_right_neg]
      _ = c * DensePoly.derivative w := add_zero _
  simpa [hsub_eq] using hsub

private theorem yunStep_quotient_tail_common_dvd_one_of_reachable
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1)) :
    ∀ d : FpPoly p,
      d ∣ c / monicGcd c w →
        d ∣ w / monicGcd c w →
          d ∣ (1 : FpPoly p) := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  intro d hda hdz
  let y := monicGcd c w
  let a := c / y
  let z := w / y
  have hcy : a * y = c := by
    simpa [a, y] using div_monicGcd_mul_reconstruct hp c w
  have hwy : z * y = w := by
    simpa [z, y] using div_monicGcd_right_mul_reconstruct hp c w
  have hz_dvd_w : z ∣ w := ⟨y, by simpa [z, y] using hwy.symm⟩
  have hdy : d ∣ y := by
    apply dvd_monicGcd hp
    · rw [← hcy]
      exact dvd_mul_right_of_dvd (a := a) (b := y) (d := d)
        (by simpa [a, y] using hda)
    · exact dvd_trans_poly (by simpa [z, y] using hdz) hz_dvd_w
  exact
    yunFactorsPairwiseReachable_common_dvd_one c w fuel hreachable d
      hda
      (by simpa [y] using hdy)

private theorem quotient_dvd_of_mul_right_dvd_mul_right
    [ZMod64.PrimeModulus p]
    {a c w y z h : FpPoly p}
    (hy : y ≠ 0)
    (hcy : a * y = c)
    (hwy : z * y = w)
    (hdvd : w ∣ c * h) :
    z ∣ a * h := by
  rcases hdvd with ⟨q, hq⟩
  refine ⟨q, ?_⟩
  apply FpPoly.mul_right_cancel_of_ne_zero hy
  calc
    (a * h) * y
        = (a * y) * h := by
          calc
            (a * h) * y = a * (h * y) := DensePoly.mul_assoc_poly a h y
            _ = a * (y * h) := by
                  exact congrArg (fun x => a * x) (DensePoly.mul_comm_poly h y)
            _ = (a * y) * h := (DensePoly.mul_assoc_poly a y h).symm
    _ = c * h := by rw [hcy]
    _ = w * q := hq
    _ = (z * y) * q := by rw [hwy]
    _ = (z * q) * y := by
          calc
            (z * y) * q = z * (y * q) := DensePoly.mul_assoc_poly z y q
            _ = z * (q * y) := by
                  exact congrArg (fun x => z * x) (DensePoly.mul_comm_poly y q)
            _ = (z * q) * y := (DensePoly.mul_assoc_poly z q y).symm

set_option maxHeartbeats 800000 in
private theorem yunStep_residual_dvd_derivative_product_core
    [ZMod64.PrimeModulus p]
    (c w y a z : FpPoly p)
    (hcy : a * y = c)
    (hwy : z * y = w)
    (hcommon_az :
      ∀ d : FpPoly p, d ∣ a → d ∣ z → d ∣ (1 : FpPoly p))
    (hprev : w ∣ DensePoly.derivative (c * w)) :
    z ∣ DensePoly.derivative (y * z) := by
  have hw_dvd_cdw : w ∣ c * DensePoly.derivative w :=
    dvd_mul_derivative_right_of_dvd_derivative_product c w hprev
  have hz_dvd_adw : z ∣ a * DensePoly.derivative w := by
    by_cases hy_zero : y = 0
    · rw [← hwy, hy_zero, mul_zero] at hw_dvd_cdw
      rw [← hwy, hy_zero, mul_zero]
      exact ⟨0, by rw [DensePoly.derivative_zero, mul_zero, mul_zero]⟩
    · exact
        quotient_dvd_of_mul_right_dvd_mul_right
          (a := a) (c := c) (w := w) (y := y) (z := z)
          (h := DensePoly.derivative w) hy_zero hcy hwy hw_dvd_cdw
  have hz_dvd_dw : z ∣ DensePoly.derivative w :=
    dvd_of_dvd_mul_of_common_dvd_one
      (g := z) (c := a) (h := DensePoly.derivative w)
      hz_dvd_adw
      hcommon_az
  have hyz : y * z = w := by
    calc
      y * z = z * y := DensePoly.mul_comm_poly y z
      _ = w := hwy
  simpa [hyz] using hz_dvd_dw

private theorem yunStep_residual_dvd_derivative_product_of_previous
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w (fuel + 1))
    (hprev : w ∣ DensePoly.derivative (c * w)) :
    let y := monicGcd c w
    let z := w / y
    z ∣ DensePoly.derivative (y * z) := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  dsimp
  let y := monicGcd c w
  let a := c / y
  let z := w / y
  have hcy : a * y = c := by
    simpa [a, y] using div_monicGcd_mul_reconstruct hp c w
  have hwy : z * y = w := by
    simpa [z, y] using div_monicGcd_right_mul_reconstruct hp c w
  have hcommon_az :
      ∀ d : FpPoly p, d ∣ a → d ∣ z → d ∣ (1 : FpPoly p) := by
    intro d hda hdz
    exact
      yunStep_quotient_tail_common_dvd_one_of_reachable c w fuel hreachable d
        (by simpa [a, y] using hda)
        (by simpa [z, y] using hdz)
  exact
    yunStep_residual_dvd_derivative_product_core
      c w y a z hcy hwy hcommon_az hprev

private theorem yunFactorsPairwiseReachable_residual_dvd_derivative_product
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel) :
    w ∣ DensePoly.derivative (c * w) := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  induction hreachable with
  | derivativeSplit hp f fuel hdf =>
      let g := monicGcd f (DensePoly.derivative f)
      let c := f / g
      have hprod : c * g = f := by
        simpa [c, g] using div_monicGcd_mul_reconstruct hp f (DensePoly.derivative f)
      have hg_dvd_df : g ∣ DensePoly.derivative f := by
        simpa [g] using monicGcd_dvd_right hp f (DensePoly.derivative f)
      simpa [c, g, hprod] using hg_dvd_df
  | step c w fuel hprev ih =>
      exact
        yunStep_residual_dvd_derivative_product_of_previous
          c w fuel hprev ih

private theorem yunFactorsPairwiseReachable_terminal_residual_derivative_zero
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (fuel : Nat)
    (hreachable : yunFactorsPairwiseReachable c w fuel)
    (hc : isOne c = true) :
    (DensePoly.derivative w).isZero = true := by
  have hprod_dvd :
      w ∣ DensePoly.derivative (c * w) :=
    yunFactorsPairwiseReachable_residual_dvd_derivative_product c w fuel hreachable
  have hc_eq : c = 1 := eq_one_of_isOne_true c hc
  have hw_dvd_dw : w ∣ DensePoly.derivative w := by
    simpa [hc_eq, one_mul] using hprod_dvd
  exact derivative_isZero_true_of_dvd_self_derivative w hw_dvd_dw

private theorem one_lt_size_of_isOne_false_of_reachable
    [ZMod64.PrimeModulus p]
    (c : FpPoly p)
    (hzero : c.isZero = false)
    (hc : isOne c = false)
    (hreachable : squareFreeContributionReachable c) :
    1 < c.size := by
  have hpos : 0 < c.size := size_pos_of_isZero_false c hzero
  by_cases hsize : c.size = 1
  · have hc_eq_one : c = 1 := hreachable hsize
    rw [hc_eq_one, isOne_one] at hc
    cases hc
  · omega

private theorem pthRoot_valid_of_derivative_zero_nontrivial
    (hp : Hex.Nat.Prime p) (f : FpPoly p) {fuel : Nat}
    (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hone : isOne f = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeContributionReachable (pthRoot f) ∧
      (pthRoot f).isZero = false ∧
        (pthRoot f).size < fuel := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hsize : 1 < f.size :=
    one_lt_size_of_isOne_false_of_reachable f hzero hone hreachable
  exact ⟨
    pthRoot_reachable_of_derivative_zero hp f hzero hdf hreachable,
    pthRoot_nonzero_of_derivative_zero_nonconstant hp f hzero hdf hsize,
    pthRoot_fuel_decrease_of_derivative_zero_nonconstant hp f hfuel hsize⟩

private theorem normalizeMonic_nonzero_size_eq
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false) :
    (normalizeMonic f).2.size = f.size := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  rw [normalizeMonic_nonzero f hzero]
  have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  have hinv_ne := zmod64_inv_ne_zero_of_prime_ne_zero hp hlead_ne
  exact scale_size_eq_of_ne_zero (p := p) hinv_ne f

private theorem normalizeMonic_derivative_zero_of_derivative_zero
    (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    (DensePoly.derivative (normalizeMonic f).2).isZero = true := by
  rw [normalizeMonic_nonzero f hzero]
  have hderiv_zero : DensePoly.derivative f = 0 :=
    eq_zero_of_isZero_true (DensePoly.derivative f) hdf
  have hzero_poly :
      DensePoly.derivative
          (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) = 0 := by
    apply DensePoly.ext_coeff
    intro n
    have hcoeff_deriv :
        ((n + 1 : Nat) : ZMod64 p) * f.coeff (n + 1) = 0 := by
      have h := congrArg (fun g : FpPoly p => g.coeff n) hderiv_zero
      change (DensePoly.derivative f).coeff n = (0 : FpPoly p).coeff n at h
      rw [coeff_derivative, DensePoly.coeff_zero] at h
      exact h
    change
      (DensePoly.derivative
          (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f)).coeff n =
        (0 : FpPoly p).coeff n
    rw [coeff_derivative, DensePoly.coeff_zero]
    have hscale_coeff :
        (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff (n + 1) =
          (DensePoly.leadingCoeff f)⁻¹ * f.coeff (n + 1) := by
      exact DensePoly.coeff_scale_semiring (DensePoly.leadingCoeff f)⁻¹ f (n + 1)
    rw [hscale_coeff]
    calc
      ((n + 1 : Nat) : ZMod64 p) *
          ((DensePoly.leadingCoeff f)⁻¹ * f.coeff (n + 1)) =
          (DensePoly.leadingCoeff f)⁻¹ *
            (((n + 1 : Nat) : ZMod64 p) * f.coeff (n + 1)) := by
            grind
      _ = 0 := by
            rw [hcoeff_deriv]
            grind
  rw [hzero_poly]
  rfl

private theorem pthRoot_normalizeMonic_frobenius_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot (normalizeMonic f).2) p = (normalizeMonic f).2 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hnorm_zero :=
    normalizeMonic_nonzero_isZero_false (p := p) f hzero
  have hnorm_deriv :=
    normalizeMonic_derivative_zero_of_derivative_zero f hzero hdf
  exact pthRoot_frobenius_of_derivative_zero
    hp (normalizeMonic f).2 hnorm_zero hnorm_deriv

private theorem pthRoot_normalizeMonic_reconstruct_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    DensePoly.C (normalizeMonic f).1 *
        pow (pthRoot (normalizeMonic f).2) p = f := by
  rw [pthRoot_normalizeMonic_frobenius_of_derivative_zero hp f hzero hdf]
  exact normalizeMonic_reconstruct hp f

private theorem pow_normalized_pthRoot_reconstruct_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity : Nat)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (DensePoly.C (normalizeMonic f).1) multiplicity *
        pow (pthRoot (normalizeMonic f).2) (multiplicity * p) =
      pow f multiplicity := by
  have hreconstruct :=
    pthRoot_normalizeMonic_reconstruct_of_derivative_zero hp f hzero hdf
  calc
    pow (DensePoly.C (normalizeMonic f).1) multiplicity *
        pow (pthRoot (normalizeMonic f).2) (multiplicity * p) =
        pow (DensePoly.C (normalizeMonic f).1) multiplicity *
          pow (pow (pthRoot (normalizeMonic f).2) p) multiplicity := by
          rw [pow_pow_mul']
    _ = pow (DensePoly.C (normalizeMonic f).1 *
          pow (pthRoot (normalizeMonic f).2) p) multiplicity := by
          exact (pow_mul_base
            (DensePoly.C (normalizeMonic f).1)
            (pow (pthRoot (normalizeMonic f).2) p)
            multiplicity).symm
    _ = pow f multiplicity := by
          rw [hreconstruct]

/--
The raw repeated tail emitted by the scaled Yun contribution loop is recovered
from its normalized tail together with the explicit leading scalar. This is the
local synchronization fact used by the derivative-active proof path; it keeps
the scalar ambiguity of executable `DensePoly.gcd` visible rather than treating
raw gcd output as monic.
-/
private theorem yunFactorsContributionWithLevel_normalized_tail_reconstruct
    (hp : Hex.Nat.Prime p) (c w : FpPoly p) (base level fuel : Nat) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    DensePoly.C (normalizeMonic contribution.2).1 *
        (normalizeMonic contribution.2).2 =
      contribution.2 := by
  exact normalizeMonic_reconstruct hp
    (yunFactorsContributionWithLevel c w base level fuel).2

/--
Product-state synchronization for the raw scaled Yun split and its normalized
tail. If the raw contribution and residual reconstruct `pow f multiplicity`,
then replacing the residual power by the normalized residual power and the
explicit scalar power preserves the same product.

This lemma deliberately does not assume `DensePoly.gcd` is monic: all scalar
ambiguity is isolated in `DensePoly.C (normalizeMonic contribution.2).1`.
-/
private theorem yunFactorsContributionWithLevel_normalized_tail_product_bridge
    (hp : Hex.Nat.Prime p) (f c w : FpPoly p)
    (base level fuel multiplicity : Nat)
    (hproduct :
      let contribution := yunFactorsContributionWithLevel c w base level fuel
      contribution.1 * pow contribution.2 multiplicity = pow f multiplicity) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    contribution.1 *
        (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
          pow (normalizeMonic contribution.2).2 multiplicity) =
      pow f multiplicity := by
  let contribution := yunFactorsContributionWithLevel c w base level fuel
  have htail_reconstruct :
      DensePoly.C (normalizeMonic contribution.2).1 *
          (normalizeMonic contribution.2).2 =
        contribution.2 := by
    simpa [contribution] using
      yunFactorsContributionWithLevel_normalized_tail_reconstruct
        hp c w base level fuel
  calc
    contribution.1 *
        (pow (DensePoly.C (normalizeMonic contribution.2).1) multiplicity *
          pow (normalizeMonic contribution.2).2 multiplicity) =
        contribution.1 *
          pow (DensePoly.C (normalizeMonic contribution.2).1 *
            (normalizeMonic contribution.2).2) multiplicity := by
          rw [pow_mul_base]
    _ = contribution.1 * pow contribution.2 multiplicity := by
          rw [htail_reconstruct]
    _ = pow f multiplicity := by
          simpa [contribution] using hproduct

private theorem squareFreeAuxRevContribution_pthRoot_normalized_tail_bridge
    (hp : Hex.Nat.Prime p) (tail : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity)
    (hzero : tail.isZero = false)
    (hdf : (DensePoly.derivative tail).isZero = true)
    (hraw :
      squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        pow (pthRoot tail) (multiplicity * p))
    (hnormalized :
      squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel =
        pow (pthRoot (normalizeMonic tail).2) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
      pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
        squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel := by
  calc
    squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        pow (pthRoot tail) (multiplicity * p) := hraw
    _ = pow tail multiplicity := by
          exact pthRoot_pow_mul_prime_of_derivative_zero
            hp tail multiplicity hmultiplicity hzero hdf
    _ = pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
          pow (pthRoot (normalizeMonic tail).2) (multiplicity * p) := by
          exact (pow_normalized_pthRoot_reconstruct_of_derivative_zero
            hp tail multiplicity hzero hdf).symm
    _ = pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
          squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
            (multiplicity * p) fuel := by
          rw [hnormalized]

private theorem derivative_active_normalized_tail_weighted_product_bridge
    (hp : Hex.Nat.Prime p) (f tail contribution : FpPoly p)
    (multiplicity fuel : Nat)
    (hzero : tail.isZero = false)
    (hdf : (DensePoly.derivative tail).isZero = true)
    (htail :
      squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel =
        pow (pthRoot (normalizeMonic tail).2) (multiplicity * p))
    (hproduct : contribution * pow tail multiplicity = pow f multiplicity) :
    contribution *
        (pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
          squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
            (multiplicity * p) fuel) =
      pow f multiplicity := by
  have htail_pow :=
    pow_normalized_pthRoot_reconstruct_of_derivative_zero
      hp tail multiplicity hzero hdf
  calc
    contribution *
        (pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
          squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
            (multiplicity * p) fuel) =
        contribution *
          (pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
            pow (pthRoot (normalizeMonic tail).2) (multiplicity * p)) := by
          rw [htail]
    _ = contribution * pow tail multiplicity := by
          rw [htail_pow]
    _ = pow f multiplicity := hproduct

private theorem derivative_active_raw_tail_weighted_product_bridge_via_normalized
    (hp : Hex.Nat.Prime p) (f tail contribution : FpPoly p)
    (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity)
    (hzero : tail.isZero = false)
    (hdf : (DensePoly.derivative tail).isZero = true)
    (hrawReachable : squareFreeContributionReachable (pthRoot tail))
    (hrawZero : (pthRoot tail).isZero = false)
    (hrawFuel : (pthRoot tail).size < fuel)
    (hrawResidual :
      squareFreeAuxRevResidualSatisfied (pthRoot tail) (multiplicity * p) fuel)
    (hcorrect :
      ∀ (f : FpPoly p) (multiplicity : Nat),
        0 < multiplicity →
          f.size < fuel →
            f.isZero = false →
              squareFreeContributionReachable f →
                squareFreeAuxRevResidualSatisfied f multiplicity fuel →
                  squareFreeAuxRevContribution f multiplicity fuel =
                    pow f multiplicity)
    (hnormalized :
      squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
          (multiplicity * p) fuel =
        pow (pthRoot (normalizeMonic tail).2) (multiplicity * p))
    (hproduct : contribution * pow tail multiplicity = pow f multiplicity) :
    contribution *
        squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
      pow f multiplicity := by
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  have hmultiplicity_tail : 0 < multiplicity * p :=
    Nat.mul_pos hmultiplicity hp_pos
  have hraw :
      squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        pow (pthRoot tail) (multiplicity * p) :=
    hcorrect (pthRoot tail) (multiplicity * p)
      hmultiplicity_tail hrawFuel hrawZero hrawReachable hrawResidual
  have htail_bridge :=
    squareFreeAuxRevContribution_pthRoot_normalized_tail_bridge
      hp tail multiplicity fuel hmultiplicity hzero hdf hraw hnormalized
  calc
    contribution *
        squareFreeAuxRevContribution (pthRoot tail) (multiplicity * p) fuel =
        contribution *
          (pow (DensePoly.C (normalizeMonic tail).1) multiplicity *
            squareFreeAuxRevContribution (pthRoot (normalizeMonic tail).2)
              (multiplicity * p) fuel) := by
          rw [htail_bridge]
    _ = pow f multiplicity := by
          exact derivative_active_normalized_tail_weighted_product_bridge
            hp f tail contribution multiplicity fuel hzero hdf hnormalized hproduct

private theorem pthRoot_size_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    (pthRoot f).size = (f.size - 1) / p + 1 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  have hmod := derivative_zero_top_degree_mod_eq_zero hp f hzero hdf
  have hpos : 0 < f.size := size_pos_of_isZero_false f hzero
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  have hjp : (f.size - 1) / p * p = f.size - 1 := by
    have h := Nat.mod_add_div (f.size - 1) p
    rw [hmod, Nat.zero_add] at h
    rw [Nat.mul_comm]
    exact h
  have hlead_ne : DensePoly.leadingCoeff f ≠ 0 :=
    fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
  have hcoeff_jp : f.coeff ((f.size - 1) / p * p) = DensePoly.leadingCoeff f := by
    rw [DensePoly.leadingCoeff_eq_coeff_last f hpos, hjp]
  have hroot_coeff_j :
      (pthRoot f).coeff ((f.size - 1) / p) = DensePoly.leadingCoeff f := by
    rw [pthRoot_coeff]
    exact hcoeff_jp
  have hcoeff_above :
      ∀ i, (f.size - 1) / p < i → (pthRoot f).coeff i = 0 := by
    intro i hi
    rw [pthRoot_coeff]
    apply DensePoly.coeff_eq_zero_of_size_le
    have hmul : ((f.size - 1) / p + 1) * p ≤ i * p := Nat.mul_le_mul_right p hi
    have hexp : ((f.size - 1) / p + 1) * p = (f.size - 1) / p * p + p := by
      rw [Nat.add_mul, Nat.one_mul]
    rw [hexp, hjp] at hmul
    omega
  have hsize_le : (pthRoot f).size ≤ (f.size - 1) / p + 1 := by
    by_cases hgt : (pthRoot f).size ≤ (f.size - 1) / p + 1
    · exact hgt
    · exfalso
      have hbig : (f.size - 1) / p + 2 ≤ (pthRoot f).size :=
        Nat.lt_of_not_ge hgt
      have hpos' : 0 < (pthRoot f).size :=
        Nat.lt_of_lt_of_le (Nat.succ_pos _) hbig
      have hidx_succ : (f.size - 1) / p + 1 ≤ (pthRoot f).size - 1 := by
        have h1 : (pthRoot f).size - 1 + 1 = (pthRoot f).size :=
          Nat.sub_add_cancel hpos'
        have h2 : (f.size - 1) / p + 2 ≤ (pthRoot f).size - 1 + 1 := h1 ▸ hbig
        omega
      have hidx : (f.size - 1) / p < (pthRoot f).size - 1 :=
        Nat.lt_of_succ_le hidx_succ
      have hzero_top : (pthRoot f).coeff ((pthRoot f).size - 1) = 0 :=
        hcoeff_above _ hidx
      have hne : (pthRoot f).coeff ((pthRoot f).size - 1) ≠ 0 :=
        DensePoly.coeff_last_ne_zero_of_pos_size (pthRoot f) hpos'
      exact hne hzero_top
  have hsize_ge : (f.size - 1) / p + 1 ≤ (pthRoot f).size := by
    by_cases hge : (f.size - 1) / p + 1 ≤ (pthRoot f).size
    · exact hge
    · exfalso
      have hzero_at_j : (pthRoot f).coeff ((f.size - 1) / p) = 0 := by
        apply DensePoly.coeff_eq_zero_of_size_le
        omega
      rw [hzero_at_j] at hroot_coeff_j
      exact hlead_ne hroot_coeff_j.symm
  omega

private theorem normalizeMonic_squareFreeContributionReachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    squareFreeContributionReachable (normalizeMonic f).2 := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  intro hsize
  by_cases hzero : f.isZero = false
  · rw [normalizeMonic_nonzero f hzero] at hsize ⊢
    apply DensePoly.ext_coeff
    intro n
    cases n with
    | zero =>
        have hscale_size :
            (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size = f.size := by
          have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
          have hinv_ne := zmod64_inv_ne_zero_of_prime_ne_zero hp hlead_ne
          exact scale_size_eq_of_ne_zero (p := p) hinv_ne f
        have hf_size : f.size = 1 := by
          rw [← hscale_size]
          exact hsize
        have hunit_inv :
            (DensePoly.leadingCoeff f)⁻¹ * f.coeff 0 = 1 := by
          have hlead_ne := fpPoly_leadingCoeff_ne_zero_of_isZero_false f hzero
          have hlead : DensePoly.leadingCoeff f = f.coeff 0 := by
            have hlead_last :
                DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
              simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
            simpa [hf_size] using hlead_last
          rw [← hlead]
          have h := zmod64_mul_inv_eq_one_of_prime_ne_zero hp hlead_ne
          have hcomm :
              (DensePoly.leadingCoeff f)⁻¹ * DensePoly.leadingCoeff f =
                DensePoly.leadingCoeff f * (DensePoly.leadingCoeff f)⁻¹ := by
            grind
          rw [hcomm]
          exact h
        change
          (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff 0 =
            (DensePoly.C (1 : ZMod64 p)).coeff 0
        have hcoeff :
            (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff 0 =
              (DensePoly.leadingCoeff f)⁻¹ * f.coeff 0 := by
          exact DensePoly.coeff_scale (DensePoly.leadingCoeff f)⁻¹ f 0
            (zmod64_mul_zero _)
        rw [hcoeff, hunit_inv]
        exact (DensePoly.coeff_C (1 : ZMod64 p) 0).symm
    | succ n =>
        have hcoeff_zero :
            (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff (n + 1) = 0 :=
          DensePoly.coeff_eq_zero_of_size_le
            (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f) (by
              have hs :
                  (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).size = 1 := hsize
              omega)
        change
          (DensePoly.scale (DensePoly.leadingCoeff f)⁻¹ f).coeff (n + 1) =
            (DensePoly.C (1 : ZMod64 p)).coeff (n + 1)
        rw [hcoeff_zero]
        exact (DensePoly.coeff_C (1 : ZMod64 p) (n + 1)).symm
  · have hzero_true : f.isZero = true := by
      cases h : f.isZero
      · exact False.elim (hzero h)
      · rfl
    rw [normalizeMonic_zero f hzero_true] at hsize
    simp at hsize

private theorem normalizeMonic_squareFreeContributionPayload
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hzero : f.isZero = false) :
    squareFreeContributionReachable (normalizeMonic f).2 ∧
      (normalizeMonic f).2.isZero = false := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  exact
    ⟨normalizeMonic_squareFreeContributionReachable hp f,
      normalizeMonic_nonzero_isZero_false f hzero⟩

private theorem normalizeMonic_isOne_false_of_isOne_false
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hreachable : squareFreeContributionReachable f)
    (hone : isOne f = false) :
    isOne (normalizeMonic f).2 = false := by
  letI : ZMod64.PrimeModulus p := ZMod64.primeModulusOfPrime hp
  by_cases hnorm_one : isOne (normalizeMonic f).2 = true
  · have hnorm_eq_one : (normalizeMonic f).2 = 1 :=
      eq_one_of_isOne_true (normalizeMonic f).2 hnorm_one
    have hnorm_size : (normalizeMonic f).2.size = 1 := by
      rw [hnorm_eq_one]
      exact DensePoly.size_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
    have hf_size : f.size = 1 := by
      have hsize_eq := normalizeMonic_nonzero_size_eq hp f hzero
      omega
    have hf_eq_one : f = 1 := hreachable hf_size
    rw [hf_eq_one, isOne_one] at hone
    cases hone
  · cases h : isOne (normalizeMonic f).2
    · rfl
    · exact False.elim (hnorm_one h)


end FpPoly
end Hex
