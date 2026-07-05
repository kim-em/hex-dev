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
public import HexPolyFp.SquareFree.Algebra
import all HexPolyFp.SquareFree.Algebra

public section
set_option backward.proofsInPublic true
set_option backward.privateInPublic true

/-!
Yun-loop definitions (`yunFactorsWithLevel`, `yunFactors`,
`squareFreeAuxRevContribution`) with the reconstruction invariants,
contribution correctness, and the divisibility toolkit.
-/
namespace Hex

namespace FpPoly

variable {p : Nat} [ZMod64.Bounds p]
/--
Yun's inner loop: peel off the factors with multiplicities `i`, `i + 1`, ...
from the coprime/repeated split `(c, w)`, consing each discovered factor onto
the reverse-order accumulator.
-/
@[expose]
def yunFactorsWithLevel
    (c w : FpPoly p) (base level : Nat) (fuel : Nat)
    (accRev : List (SquareFreeFactor p)) :
    List (SquareFreeFactor p) × FpPoly p :=
  match fuel with
  | 0 => (accRev, w)
  | fuel + 1 =>
      if isOne c then
        (accRev, w)
      else
        let y := monicGcd c w
        let z := c / y
        let accRev' :=
          if isOne z then
            accRev
          else
            { factor := z, multiplicity := base * level } :: accRev
        yunFactorsWithLevel y (w / y) base (level + 1) fuel accRev'

/-- `yunFactors` is the multiplicity-indexed Yun inner loop, peeling factors off
the coprime/repeated split `(c, w)` and tagging each with the running
multiplicity `i`. -/
private def yunFactors
    (c w : FpPoly p) (i : Nat) (fuel : Nat)
    (accRev : List (SquareFreeFactor p)) :
    List (SquareFreeFactor p) × FpPoly p :=
  match fuel with
  | 0 => (accRev, w)
  | fuel + 1 =>
      if isOne c then
        (accRev, w)
      else
        let y := monicGcd c w
        let z := c / y
        let accRev' :=
          if isOne z then
            accRev
          else
            { factor := z, multiplicity := i } :: accRev
        yunFactors y (w / y) (i + 1) fuel accRev'

/--
Specification payload for `yunFactors`: the first component is the product
contributed by factors discovered from `(c, w, i, fuel)`, and the second is
the repeated part that remains for the `p`-th-root descent.
-/
private def yunFactorsContributionWithLevel
    (c w : FpPoly p) (base level : Nat) : Nat → FpPoly p × FpPoly p
  | 0 => (1, w)
  | fuel + 1 =>
      if isOne c then
        (1, w)
      else
        let y := monicGcd c w
        let z := c / y
        let tail := yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel
        let contribution :=
          if isOne z then
            tail.1
          else
            pow z (base * level) * tail.1
        (contribution, tail.2)

/-- `yunFactorsContribution` is the specification payload for `yunFactors`: the
product contributed by the discovered factors paired with the repeated part that
remains. -/
private def yunFactorsContribution
    (c w : FpPoly p) (i : Nat) : Nat → FpPoly p × FpPoly p
  | 0 => (1, w)
  | fuel + 1 =>
      if isOne c then
        (1, w)
      else
        let y := monicGcd c w
        let z := c / y
        let tail := yunFactorsContribution y (w / y) (i + 1) fuel
        let contribution :=
          if isOne z then
            tail.1
          else
            pow z i * tail.1
        (contribution, tail.2)

/-- `yunFactorsWithLevel_reconstruction_invariant` ties `yunFactorsWithLevel` to
`yunFactorsContributionWithLevel`: the loop's residual matches the contribution's
residual, and the reverse-order accumulator product equals the prior accumulator
product times the contribution. -/
private theorem yunFactorsWithLevel_reconstruction_invariant
    (c w : FpPoly p) (base level fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    let loop := yunFactorsWithLevel c w base level fuel accRev
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    loop.2 = contribution.2 ∧
      weightedProduct loop.1.reverse =
        weightedProduct accRev.reverse * contribution.1 := by
  induction fuel generalizing c w level accRev with
  | zero =>
      simp [yunFactorsWithLevel, yunFactorsContributionWithLevel]
  | succ fuel ih =>
      simp only [yunFactorsWithLevel, yunFactorsContributionWithLevel]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (level + 1) accRev
        · have htail := ih y (w / y) (level + 1)
            ({ factor := z, multiplicity := base * level } :: accRev)
          constructor
          · simpa [y, z, hz] using htail.1
          · have hmul :
                weightedProduct (yunFactorsWithLevel y (w / y) base (level + 1) fuel
                    ({ factor := z, multiplicity := base * level } :: accRev)).1.reverse =
                  weightedProduct accRev.reverse *
                    (pow z (base * level) *
                      (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1) := by
              calc
                weightedProduct (yunFactorsWithLevel y (w / y) base (level + 1) fuel
                    ({ factor := z, multiplicity := base * level } :: accRev)).1.reverse
                    = weightedProduct ({ factor := z, multiplicity := base * level } :: accRev).reverse *
                        (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
                          simpa [y, z] using htail.2
                _ = (weightedProduct accRev.reverse * pow z (base * level)) *
                        (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1 := by
                          rw [weightedProduct_reverse_cons]
                _ = weightedProduct accRev.reverse *
                        (pow z (base * level) *
                          (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1) := by
                          exact DensePoly.mul_assoc_poly
                            (weightedProduct accRev.reverse) (pow z (base * level))
                            (yunFactorsContributionWithLevel y (w / y) base (level + 1) fuel).1
            simpa [y, z, hz] using hmul

/-- `yunFactors_reconstruction_invariant` ties `yunFactors` to
`yunFactorsContribution`: the loop's residual matches the contribution's
residual, and the reverse-order accumulator product equals the prior accumulator
product times the contribution. -/
private theorem yunFactors_reconstruction_invariant
    (c w : FpPoly p) (i fuel : Nat) (accRev : List (SquareFreeFactor p)) :
    let loop := yunFactors c w i fuel accRev
    let contribution := yunFactorsContribution c w i fuel
    loop.2 = contribution.2 ∧
      weightedProduct loop.1.reverse =
        weightedProduct accRev.reverse * contribution.1 := by
  induction fuel generalizing c w i accRev with
  | zero =>
      simp [yunFactors, yunFactorsContribution]
  | succ fuel ih =>
      simp only [yunFactors, yunFactorsContribution]
      by_cases hc : isOne c
      · simp [hc]
      · simp [hc]
        let y := monicGcd c w
        let z := c / y
        by_cases hz : isOne z
        · simpa [y, z, hz] using ih y (w / y) (i + 1) accRev
        · have htail := ih y (w / y) (i + 1) ({ factor := z, multiplicity := i } :: accRev)
          constructor
          · simpa [y, z, hz] using htail.1
          · have hmul :
                weightedProduct (yunFactors y (w / y) (i + 1) fuel
                    ({ factor := z, multiplicity := i } :: accRev)).1.reverse =
                  weightedProduct accRev.reverse *
                    (pow z i * (yunFactorsContribution y (w / y) (i + 1) fuel).1) := by
              calc
                weightedProduct (yunFactors y (w / y) (i + 1) fuel
                    ({ factor := z, multiplicity := i } :: accRev)).1.reverse
                    = weightedProduct ({ factor := z, multiplicity := i } :: accRev).reverse *
                        (yunFactorsContribution y (w / y) (i + 1) fuel).1 := by
                          simpa [y, z] using htail.2
                _ = (weightedProduct accRev.reverse * pow z i) *
                        (yunFactorsContribution y (w / y) (i + 1) fuel).1 := by
                          rw [weightedProduct_reverse_cons]
                _ = weightedProduct accRev.reverse *
                        (pow z i * (yunFactorsContribution y (w / y) (i + 1) fuel).1) := by
                          exact DensePoly.mul_assoc_poly
                            (weightedProduct accRev.reverse) (pow z i)
                            (yunFactorsContribution y (w / y) (i + 1) fuel).1
            simpa [y, z, hz] using hmul

/--
Product contribution of `squareFreeAuxRev` before it is multiplied into the
caller-provided reverse accumulator.
-/
private def squareFreeAuxRevContribution (f : FpPoly p) (multiplicity : Nat) :
    Nat → FpPoly p
  | 0 => 1
  | fuel + 1 =>
      if f.isZero then
        1
      else
        let df := DensePoly.derivative f
        if df.isZero then
          squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel
        else
          let g := monicGcd f df
          let c := f / g
          let contribution := yunFactorsContributionWithLevel c g multiplicity 1 fuel
          if isOne contribution.2 then
            contribution.1
          else
            contribution.1 *
              squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel

private theorem squareFreeAuxRevContribution_pthRoot_correct_pow
    (_hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (_hmultiplicity : 0 < multiplicity) (_hfuel : f.size < fuel + 1)
    (_hzero : f.isZero = false)
    (_hdf : (DensePoly.derivative f).isZero = true)
    (hroot :
      squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
      pow (pthRoot f) (multiplicity * p) := by
  exact hroot

private theorem derivative_coeff_pred_of_pos_lt
    (f : FpPoly p) {n : Nat} (hn0 : 0 < n) (hn : n < f.size) :
    (DensePoly.derivative f).coeff (n - 1) =
      ((n : Nat) : ZMod64 p) * f.coeff n := by
  unfold DensePoly.derivative
  rw [DensePoly.coeff_ofCoeffs_list]
  have hpred : n - 1 < f.size - 1 := by omega
  have hget :
      (((List.range (f.size - 1)).map
          (fun i => (((i + 1 : Nat) : ZMod64 p) * f.coeff (i + 1)))).getD
        (n - 1) (0 : ZMod64 p)) =
          (((n - 1 + 1 : Nat) : ZMod64 p) * f.coeff (n - 1 + 1)) := by
    simp [List.getD, hpred]
  have hsucc : n - 1 + 1 = n := by omega
  rw [hsucc] at hget
  exact hget

private theorem zmod64_natCast_ne_zero_of_mod_ne_zero
    (n : Nat) (hn : n % p ≠ 0) :
    ((n : Nat) : ZMod64 p) ≠ 0 := by
  intro hzero
  apply hn
  have hnat : (ZMod64.natCast p n).toNat = (0 : ZMod64 p).toNat :=
    congrArg ZMod64.toNat hzero
  rw [ZMod64.toNat_natCast] at hnat
  exact hnat

private theorem derivative_zero_coeff_non_pmultiple
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (n : Nat)
    (hdf : (DensePoly.derivative f).isZero = true) (hn : n % p ≠ 0) :
    f.coeff n = 0 := by
  by_cases hsize : f.size ≤ n
  · exact DensePoly.coeff_eq_zero_of_size_le f hsize
  · have hnlt : n < f.size := Nat.lt_of_not_ge hsize
    have hn0 : 0 < n := by
      cases n with
      | zero =>
          simp at hn
      | succ n =>
          exact Nat.succ_pos n
    have hderiv_zero_poly : DensePoly.derivative f = 0 :=
      eq_zero_of_isZero_true (DensePoly.derivative f) hdf
    have hderiv_coeff : (DensePoly.derivative f).coeff (n - 1) = 0 := by
      rw [hderiv_zero_poly]
      exact DensePoly.coeff_zero (R := ZMod64 p) (n - 1)
    have hmul :
        ((n : Nat) : ZMod64 p) * f.coeff n = 0 := by
      rw [← derivative_coeff_pred_of_pos_lt f hn0 hnlt]
      exact hderiv_coeff
    rcases ZMod64.eq_zero_or_eq_zero_of_mul_eq_zero hp hmul with hnzero | hcoeff
    · exact False.elim (zmod64_natCast_ne_zero_of_mod_ne_zero n hn hnzero)
    · exact hcoeff

private theorem size_pos_of_isZero_false
    (f : FpPoly p) (hzero : f.isZero = false) :
    0 < f.size := by
  simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero,
    Nat.pos_iff_ne_zero] using hzero

private theorem size_eq_zero_of_isZero_true
    (f : FpPoly p) (hzero : f.isZero = true) :
    f.size = 0 := by
  simpa [DensePoly.isZero, DensePoly.size, Array.isEmpty_iff_size_eq_zero] using hzero

/-- `pthRoot` fixes the constant polynomial `1`, the unit base case of the `pthRoot` recursion. -/
private theorem pthRoot_one
    (hp : Hex.Nat.Prime p) :
    pthRoot (1 : FpPoly p) = 1 := by
  apply DensePoly.ext_coeff
  intro i
  rw [pthRoot_coeff]
  cases i with
  | zero =>
      simp
  | succ i =>
      have hp_pos : 0 < p := by
        have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
        omega
      have hne : (i + 1) * p ≠ 0 := by
        exact Nat.mul_ne_zero (Nat.succ_ne_zero i) (Nat.ne_of_gt hp_pos)
      change (DensePoly.C (1 : ZMod64 p)).coeff ((i + 1) * p) =
        (DensePoly.C (1 : ZMod64 p)).coeff (i + 1)
      rw [DensePoly.coeff_C, DensePoly.coeff_C]
      simp [hne]

/-- Every power of the constant polynomial `1` is `1`. -/
private theorem pow_one_base (n : Nat) :
    pow (1 : FpPoly p) n = 1 := by
  rw [pow_eq_powLinear]
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [powLinear, ih]
      exact mul_one (1 : FpPoly p)

/-- The square-free contribution of the constant polynomial `1` is `1`, halting the recursion at the unit. -/
private theorem squareFreeAuxRevContribution_one
    (hp : Hex.Nat.Prime p) (multiplicity fuel : Nat) :
    squareFreeAuxRevContribution (1 : FpPoly p) multiplicity fuel = 1 := by
  induction fuel generalizing multiplicity with
  | zero =>
      rfl
  | succ fuel ih =>
      simp only [squareFreeAuxRevContribution]
      have hone_ne : (1 : FpPoly p).isZero = false := by
        have hcoeffs :
            (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        simp [DensePoly.isZero, hcoeffs]
      have hdf_one : (DensePoly.derivative (1 : FpPoly p)).isZero = true := by
        have hcoeffs :
            (1 : FpPoly p).coeffs = #[(1 : ZMod64 p)] :=
          DensePoly.coeffs_C_of_ne_zero (zmod64_one_ne_zero_of_prime hp)
        have hsize : (1 : FpPoly p).size = 1 := by
          simpa [DensePoly.size] using congrArg Array.size hcoeffs
        unfold DensePoly.derivative
        simp [hsize, DensePoly.isZero, DensePoly.ofCoeffs, DensePoly.trimTrailingZeros]
        rfl
      simp [hone_ne]
      rw [hdf_one, pthRoot_one hp]
      exact ih (multiplicity * p)

/-- A polynomial of `size` one is constant, so its derivative is zero. -/
private theorem derivative_isZero_true_of_size_one
    (f : FpPoly p) (hsize : f.size = 1) :
    (DensePoly.derivative f).isZero = true := by
  unfold DensePoly.derivative
  simp [hsize, DensePoly.isZero, DensePoly.ofCoeffs, DensePoly.trimTrailingZeros]
  rfl

/-- Square-free contribution correctness on `pthRoot 1`: it equals `pow (pthRoot 1) multiplicity`, the constant base case of the `pthRoot` branch. -/
private theorem squareFreeAuxRevContribution_pthRoot_constant_correct
    (hp : Hex.Nat.Prime p) (multiplicity fuel : Nat) :
    squareFreeAuxRevContribution (pthRoot (1 : FpPoly p)) multiplicity fuel =
      pow (pthRoot (1 : FpPoly p)) multiplicity := by
  rw [pthRoot_one hp, squareFreeAuxRevContribution_one hp, pow_one_base]

/-- When the derivative vanishes on a nonzero `f`, its top degree `f.size - 1` is a multiple of `p`. -/
private theorem derivative_zero_top_degree_mod_eq_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    (f.size - 1) % p = 0 := by
  by_cases hmod : (f.size - 1) % p = 0
  · exact hmod
  ·
    have hpos : 0 < f.size := size_pos_of_isZero_false f hzero
    have hcoeff_zero :=
      derivative_zero_coeff_non_pmultiple hp f (f.size - 1) hdf hmod
    have hcoeff_ne := DensePoly.coeff_last_ne_zero_of_pos_size f hpos
    exact False.elim (hcoeff_ne hcoeff_zero)

/-- When the derivative vanishes on a nonconstant `f`, `pthRoot f` is nonzero, since its top coefficient is the nonzero top coefficient of `f`. -/
private theorem pthRoot_nonzero_of_derivative_zero_nonconstant
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hsize : 1 < f.size) :
    (pthRoot f).isZero = false := by
  by_cases hroot_false : (pthRoot f).isZero = false
  · exact hroot_false
  ·
    have hroot_true : (pthRoot f).isZero = true := by
      cases h : (pthRoot f).isZero <;> simp [h] at hroot_false ⊢
    have hroot_size : (pthRoot f).size = 0 :=
      size_eq_zero_of_isZero_true (pthRoot f) hroot_true
    let i := (f.size - 1) / p
    have hcoeff_root_zero :
        (pthRoot f).coeff i = 0 := by
      exact DensePoly.coeff_eq_zero_of_size_le (pthRoot f) (by
        rw [hroot_size]
        exact Nat.zero_le i)
    have hcoeff_f_zero : f.coeff (f.size - 1) = 0 := by
      have hmod := derivative_zero_top_degree_mod_eq_zero hp f hzero hdf
      have hmul : i * p = f.size - 1 := by
        have h := Nat.mod_add_div (f.size - 1) p
        rw [hmod, Nat.zero_add] at h
        simpa [i, Nat.mul_comm] using h
      rw [pthRoot_coeff] at hcoeff_root_zero
      simpa [hmul] using hcoeff_root_zero
    have hpos : 0 < f.size := by omega
    exact False.elim (DensePoly.coeff_last_ne_zero_of_pos_size f hpos hcoeff_f_zero)

/-- Taking `pthRoot` of a nonconstant polynomial strictly shrinks its `size`, so the recursion's fuel still bounds it. -/
private theorem pthRoot_fuel_decrease_of_derivative_zero_nonconstant
    (hp : Hex.Nat.Prime p) (f : FpPoly p) {fuel : Nat}
    (hfuel : f.size < fuel + 1)
    (hsize : 1 < f.size) :
    (pthRoot f).size < fuel := by
  by_cases hlt : (pthRoot f).size < fuel
  · exact hlt
  ·
    have hf_le : f.size ≤ fuel := by omega
    have hfuel_pos : 0 < fuel := by omega
    let i := (pthRoot f).size - 1
    have hi_lt : i < (pthRoot f).size := by omega
    have hroot_coeff_ne :
        (pthRoot f).coeff i ≠ 0 :=
      DensePoly.coeff_last_ne_zero_of_pos_size (pthRoot f) (by omega)
    have hroot_coeff_zero :
        (pthRoot f).coeff i = 0 := by
      rw [pthRoot_coeff]
      exact DensePoly.coeff_eq_zero_of_size_le f (by
        have hp_two : 2 ≤ p := Hex.Nat.Prime.two_le hp
        have hige : fuel - 1 ≤ i := by omega
        have hi : i * p ≥ fuel := by
          dsimp [i]
          have hfuel_ge_two : 2 ≤ fuel := by omega
          calc
            fuel = (fuel - 1) + 1 := by omega
            _ ≤ (fuel - 1) + (fuel - 1) := by omega
            _ = 2 * (fuel - 1) := by omega
            _ ≤ p * i := by
              exact Nat.mul_le_mul hp_two hige
            _ = i * p := Nat.mul_comm p i
        omega)
    exact False.elim (hroot_coeff_ne hroot_coeff_zero)

/-- When the derivative vanishes, raising `pthRoot f` to the `p`-th power recovers `f`, the Frobenius identity over `Fp`. -/
private theorem pthRoot_frobenius_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (_hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot f) p = f := by
  apply DensePoly.ext_coeff
  intro n
  rw [pthRoot_pow_prime_coeff hp f n]
  by_cases hn : n % p = 0
  · simp [hn]
  · simp [hn, derivative_zero_coeff_non_pmultiple hp f n hdf hn]

/-- When the derivative vanishes, `pthRoot f` divides `f`, since `f` is its `p`-th power. -/
private theorem pthRoot_dvd_self_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pthRoot f ∣ f := by
  have hp_pos : 0 < p := by
    have htwo : 2 ≤ p := Hex.Nat.Prime.two_le hp
    omega
  refine ⟨pow (pthRoot f) (p - 1), ?_⟩
  calc
    f = pow (pthRoot f) p := by
      exact (pthRoot_frobenius_of_derivative_zero hp f hzero hdf).symm
    _ = pow (pthRoot f) (1 + (p - 1)) := by
      have hp_eq : 1 + (p - 1) = p := by omega
      rw [hp_eq]
    _ = pow (pthRoot f) 1 * pow (pthRoot f) (p - 1) := by
      exact pow_add_exp (pthRoot f) 1 (p - 1)
    _ = pthRoot f * pow (pthRoot f) (p - 1) := by
      rw [pow_one]

/-- Iterating `pow` multiplies the exponents. -/
private theorem pow_pow_mul
    (f : FpPoly p) (m n : Nat) (_hm : 0 < m) :
    pow (pow f n) m = pow f (m * n) := by
  rw [pow_eq_powLinear, pow_eq_powLinear, pow_eq_powLinear]
  exact powLinear_powLinear_mul f m n

/-- When the derivative vanishes, `pow (pthRoot f) (multiplicity * p)` equals `pow f multiplicity`, transporting the recursion's contribution from `pthRoot f` back to `f`. -/
private theorem pthRoot_pow_mul_prime_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity : Nat)
    (hmultiplicity : 0 < multiplicity)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true) :
    pow (pthRoot f) (multiplicity * p) = pow f multiplicity := by
  calc
    pow (pthRoot f) (multiplicity * p) =
        pow (pow (pthRoot f) p) multiplicity := by
          exact (pow_pow_mul (pthRoot f) multiplicity p hmultiplicity).symm
    _ = pow f multiplicity := by
          rw [pthRoot_frobenius_of_derivative_zero hp f hzero hdf]

/-- Square-free contribution correctness on the derivative-zero branch: the recursive contribution of `pthRoot f` at multiplicity `multiplicity * p` equals `pow f multiplicity`. -/
private theorem squareFreeAuxRevContribution_derivative_zero_correct
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (multiplicity fuel : Nat)
    (hmultiplicity : 0 < multiplicity) (hfuel : f.size < fuel + 1)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hroot :
      squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p)) :
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
      pow f multiplicity := by
  calc
    squareFreeAuxRevContribution (pthRoot f) (multiplicity * p) fuel =
        pow (pthRoot f) (multiplicity * p) := by
          exact squareFreeAuxRevContribution_pthRoot_correct_pow
            hp f multiplicity fuel hmultiplicity hfuel hzero hdf hroot
    _ = pow f multiplicity := by
          exact pthRoot_pow_mul_prime_of_derivative_zero
            hp f multiplicity hmultiplicity hzero hdf

private def squareFreeContributionReachable (f : FpPoly p) : Prop :=
  f.size = 1 → f = 1

private theorem squareFreeContributionReachable_of_monic
    (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    squareFreeContributionReachable f := by
  intro hsize
  apply DensePoly.ext_coeff
  intro n
  cases n with
  | zero =>
      have hpos : 0 < f.size := by omega
      have hlead : DensePoly.leadingCoeff f = f.coeff 0 := by
        have hlead_last :
            DensePoly.leadingCoeff f = f.coeff (f.size - 1) := by
          simp [DensePoly.leadingCoeff, DensePoly.coeff, DensePoly.size]
        simpa [hsize] using hlead_last
      change f.coeff 0 = (DensePoly.C (1 : ZMod64 p)).coeff 0
      rw [← hlead, hmonic]
      exact (DensePoly.coeff_C (1 : ZMod64 p) 0).symm
  | succ n =>
      have hn : f.size ≤ n + 1 := by omega
      change f.coeff (n + 1) = (DensePoly.C (1 : ZMod64 p)).coeff (n + 1)
      rw [DensePoly.coeff_eq_zero_of_size_le f hn]
      exact (DensePoly.coeff_C (1 : ZMod64 p) (n + 1)).symm

private theorem pthRoot_reachable_of_derivative_zero
    (hp : Hex.Nat.Prime p) (f : FpPoly p)
    (hzero : f.isZero = false)
    (hdf : (DensePoly.derivative f).isZero = true)
    (hreachable : squareFreeContributionReachable f) :
    squareFreeContributionReachable (pthRoot f) := by
  intro hroot_size
  have hf_size_one : f.size = 1 := by
    by_cases hf : f.size = 1
    · exact hf
    ·
      have hf_gt : 1 < f.size := by
        have hpos := size_pos_of_isZero_false f hzero
        omega
      have htop_mod := derivative_zero_top_degree_mod_eq_zero hp f hzero hdf
      let i := (f.size - 1) / p
      have hi_pos : 0 < i := by
        have hdiv : i * p = f.size - 1 := by
          have h := Nat.mod_add_div (f.size - 1) p
          rw [htop_mod, Nat.zero_add] at h
          simpa [i, Nat.mul_comm] using h
        by_cases hi : i = 0
        · rw [hi] at hdiv
          simp at hdiv
          omega
        · exact Nat.pos_of_ne_zero hi
      have hi_ge : 1 ≤ i := Nat.succ_le_of_lt hi_pos
      have hroot_zero :
          (pthRoot f).coeff i = 0 :=
        DensePoly.coeff_eq_zero_of_size_le (pthRoot f) (by
          rw [hroot_size]
          exact hi_ge)
      have hf_zero : f.coeff (f.size - 1) = 0 := by
        have hmul : i * p = f.size - 1 := by
          have h := Nat.mod_add_div (f.size - 1) p
          rw [htop_mod, Nat.zero_add] at h
          simpa [i, Nat.mul_comm] using h
        rw [pthRoot_coeff] at hroot_zero
        simpa [hmul] using hroot_zero
      exact False.elim (DensePoly.coeff_last_ne_zero_of_pos_size f (by omega) hf_zero)
  have hf_one : f = 1 := hreachable hf_size_one
  rw [hf_one]
  exact pthRoot_one hp

/-- A monic prime-field polynomial is nonzero: its leading coefficient `1` is
nonzero by `zmod64_one_ne_zero_of_prime`, while a zero polynomial has leading
coefficient `0`. -/
private theorem ne_zero_of_monic_fpoly
    (hp : Hex.Nat.Prime p) {f : FpPoly p} (hmonic : DensePoly.Monic f) :
    f ≠ 0 := by
  intro hzero
  have hlead_one : DensePoly.leadingCoeff f = 1 := hmonic
  rw [hzero] at hlead_one
  have hlead_zero : DensePoly.leadingCoeff (0 : FpPoly p) = (0 : ZMod64 p) :=
    DensePoly.leadingCoeff_zero
  rw [hlead_zero] at hlead_one
  exact zmod64_one_ne_zero_of_prime hp hlead_one.symm

/-- A monic prime-field polynomial has unit scalar `1` under `normalizeMonic`:
the recorded leading coefficient is `1`, matching the leading coefficient of
the input. Companion to `normalizeMonic_eq_self_of_monic`. -/
private theorem normalizeMonic_fst_eq_one_of_monic
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    (normalizeMonic f).1 = 1 := by
  have hzero : f.isZero = false := by
    cases hz : f.isZero with
    | false => rfl
    | true =>
        exfalso
        have hf_zero : f = 0 := eq_zero_of_isZero_true f hz
        have hlead : DensePoly.leadingCoeff f = (1 : ZMod64 p) := hmonic
        rw [hf_zero, DensePoly.leadingCoeff_zero] at hlead
        exact zmod64_one_ne_zero_of_prime hp hlead.symm
  rw [normalizeMonic_nonzero f hzero]
  exact hmonic

/-- `normalizeMonic` is transparent on an already-monic polynomial: the
polynomial component of the split is the input unchanged. This lets downstream
code collapse a normalized provider back to the raw polynomial whenever it has
an explicit `DensePoly.Monic` hypothesis for that exact polynomial. -/
private theorem normalizeMonic_eq_self_of_monic
    (hp : Hex.Nat.Prime p) (f : FpPoly p) (hmonic : DensePoly.Monic f) :
    (normalizeMonic f).2 = f := by
  have hfst : (normalizeMonic f).1 = 1 :=
    normalizeMonic_fst_eq_one_of_monic hp f hmonic
  have hrec : DensePoly.C (normalizeMonic f).1 * (normalizeMonic f).2 = f :=
    normalizeMonic_reconstruct hp f
  rw [hfst] at hrec
  have hC_one : DensePoly.C (1 : ZMod64 p) = (1 : FpPoly p) := rfl
  rw [hC_one, one_mul] at hrec
  exact hrec

/-- Exact-quotient monicity: given a multiplicative factorization `q * b = a`
with `a` and `b` both monic in `FpPoly p`, the quotient `q` is also monic.

Used as substrate for the Yun derivative-active monic-residual invariant
(#6155): each Yun-loop transition produces an exact-quotient residual
`w / gcd c w` whose monicity is dispatched by combining this lemma with the
reconstruction identity `(w / gcd c w) * gcd c w = w`. The lemma also handles
the initial split residual `f / gcd f f'` symmetrically. -/
private theorem monic_of_mul_eq_monic_of_monic
    [ZMod64.PrimeModulus p]
    (hp : Hex.Nat.Prime p)
    {a b q : FpPoly p}
    (ha_monic : DensePoly.Monic a)
    (hb_monic : DensePoly.Monic b)
    (hrec : q * b = a) :
    DensePoly.Monic q := by
  have ha_ne : a ≠ 0 := ne_zero_of_monic_fpoly hp ha_monic
  have hb_ne : b ≠ 0 := ne_zero_of_monic_fpoly hp hb_monic
  have hq_ne : q ≠ 0 := by
    intro hq
    apply ha_ne
    rw [← hrec, hq, zero_mul]
  have hlead_a : DensePoly.leadingCoeff a = 1 := ha_monic
  have hlead_b : DensePoly.leadingCoeff b = 1 := hb_monic
  have hlead_mul :
      DensePoly.leadingCoeff (q * b) =
        DensePoly.leadingCoeff q * DensePoly.leadingCoeff b :=
    FpPoly.leadingCoeff_mul q b hq_ne hb_ne
  have hlead_q_b :
      DensePoly.leadingCoeff q * DensePoly.leadingCoeff b = 1 := by
    rw [← hlead_mul, hrec, hlead_a]
  have hlead_q : DensePoly.leadingCoeff q = 1 := by
    rw [hlead_b] at hlead_q_b
    simpa using hlead_q_b
  exact hlead_q

/-- Exact-quotient monicity for the right Yun residual through `monicGcd`: from
monic `w` and a monic `monicGcd c w` divisor, the right exact quotient
`w / monicGcd c w` is monic. This is the residual threaded into the next Yun
state, so it carries the monic invariant forward. -/
private theorem monic_div_monicGcd_right_of_monic
    [ZMod64.PrimeModulus p]
    (hp : Hex.Nat.Prime p)
    (c w : FpPoly p)
    (hw_monic : DensePoly.Monic w)
    (hgcd_monic : DensePoly.Monic (monicGcd c w)) :
    DensePoly.Monic (w / monicGcd c w) :=
  monic_of_mul_eq_monic_of_monic hp hw_monic hgcd_monic
    (div_monicGcd_right_mul_reconstruct hp c w)

/--
Algebraic step identity used to thread the scaled Yun product invariant through
a single non-terminating iteration. With `y = gcd c w`, `z = c / y`, and
`v = w / y`, the input `pow c (base * level) * pow w base` rebalances to
`pow z (base * level) * pow y (base * (level + 1)) * pow v base`, capturing the
emission of `z` at multiplicity `base * level` while moving `g`'s remaining
factor into the next level.
-/
private theorem yunFactorsContributionWithLevel_pow_step_algebra
    [ZMod64.PrimeModulus p] (c w : FpPoly p) (base level : Nat) :
    pow c (base * level) * pow w base =
      pow (c / monicGcd c w) (base * level) *
        pow (monicGcd c w) (base * (level + 1)) *
        pow (w / monicGcd c w) base := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  have hqg : (c / monicGcd c w) * monicGcd c w = c :=
    div_monicGcd_mul_reconstruct hp c w
  have hvg : (w / monicGcd c w) * monicGcd c w = w :=
    div_monicGcd_right_mul_reconstruct hp c w
  have hexp : base * level + base = base * (level + 1) := by
    rw [Nat.mul_succ]
  calc pow c (base * level) * pow w base
      = pow ((c / monicGcd c w) * monicGcd c w) (base * level) *
          pow ((w / monicGcd c w) * monicGcd c w) base := by rw [hqg, hvg]
    _ = (pow (c / monicGcd c w) (base * level) *
            pow (monicGcd c w) (base * level)) *
          (pow (w / monicGcd c w) base * pow (monicGcd c w) base) := by
        rw [pow_mul_base (c / monicGcd c w) (monicGcd c w) (base * level),
            pow_mul_base (w / monicGcd c w) (monicGcd c w) base]
    _ = pow (c / monicGcd c w) (base * level) *
          (pow (monicGcd c w) (base * level) *
            (pow (w / monicGcd c w) base * pow (monicGcd c w) base)) := by
        exact DensePoly.mul_assoc_poly _ _ _
    _ = pow (c / monicGcd c w) (base * level) *
          ((pow (monicGcd c w) (base * level) * pow (w / monicGcd c w) base) *
            pow (monicGcd c w) base) := by
        exact congrArg
          (fun x => pow (c / monicGcd c w) (base * level) * x)
          (DensePoly.mul_assoc_poly
            (pow (monicGcd c w) (base * level))
            (pow (w / monicGcd c w) base)
            (pow (monicGcd c w) base)).symm
    _ = pow (c / monicGcd c w) (base * level) *
          ((pow (w / monicGcd c w) base * pow (monicGcd c w) (base * level)) *
            pow (monicGcd c w) base) := by
        exact congrArg
          (fun x => pow (c / monicGcd c w) (base * level) *
            (x * pow (monicGcd c w) base))
          (DensePoly.mul_comm_poly
            (pow (monicGcd c w) (base * level))
            (pow (w / monicGcd c w) base))
    _ = pow (c / monicGcd c w) (base * level) *
          (pow (w / monicGcd c w) base *
            (pow (monicGcd c w) (base * level) * pow (monicGcd c w) base)) := by
        exact congrArg
          (fun x => pow (c / monicGcd c w) (base * level) * x)
          (DensePoly.mul_assoc_poly
            (pow (w / monicGcd c w) base)
            (pow (monicGcd c w) (base * level))
            (pow (monicGcd c w) base))
    _ = pow (c / monicGcd c w) (base * level) *
          (pow (w / monicGcd c w) base *
            pow (monicGcd c w) (base * level + base)) := by
        rw [← pow_add_exp]
    _ = pow (c / monicGcd c w) (base * level) *
          (pow (w / monicGcd c w) base *
            pow (monicGcd c w) (base * (level + 1))) := by
        rw [hexp]
    _ = pow (c / monicGcd c w) (base * level) *
          (pow (monicGcd c w) (base * (level + 1)) *
            pow (w / monicGcd c w) base) := by
        exact congrArg
          (fun x => pow (c / monicGcd c w) (base * level) * x)
          (DensePoly.mul_comm_poly
            (pow (w / monicGcd c w) base)
            (pow (monicGcd c w) (base * (level + 1))))
    _ = pow (c / monicGcd c w) (base * level) *
          pow (monicGcd c w) (base * (level + 1)) *
          pow (w / monicGcd c w) base := by
        exact (DensePoly.mul_assoc_poly _ _ _).symm

/--
Recursive termination predicate for the scaled Yun loop: the loop on
`(c, w, base, level)` reaches `isOne c = true` within `fuel` iterations.
The predicate is structural in `fuel`, with the witness chain mirroring
the loop's recursion through `(gcd c w, w / gcd c w, base, level + 1)`.
-/
private def yunFactorsLevelCompletes (c w : FpPoly p) (base : Nat) :
    Nat → Nat → Prop
  | _, 0 => isOne c = true
  | level, fuel + 1 =>
      isOne c = true ∨
        yunFactorsLevelCompletes
          (monicGcd c w) (w / monicGcd c w) base (level + 1) fuel

/--
Normalized termination predicate for the scaled Yun loop. This mirrors
`yunFactorsLevelCompletes`, but tests the normalized current contribution.
It is the right progress predicate for raw scalar-unit states, where `c` may
be a non-one constant while `(normalizeMonic c).2 = 1`.
-/
private def yunFactorsNormalizedLevelCompletes (c w : FpPoly p) (base : Nat) :
    Nat → Nat → Prop
  | _, 0 => isOne (normalizeMonic c).2 = true
  | level, fuel + 1 =>
      isOne (normalizeMonic c).2 = true ∨
        yunFactorsNormalizedLevelCompletes
          (monicGcd c w) (w / monicGcd c w) base (level + 1) fuel

/--
Conditional product invariant for the scaled Yun loop: when the loop
terminates by `isOne c = true` within the supplied `fuel`, the loop's
contribution times the power of its residual recovers
`pow c (base * level) * pow w base`. This is the deep algebraic content
of Yun's identity, packaged with the termination predicate so the
inductive base case discharges cleanly.
-/
private theorem yunFactorsContributionWithLevel_pow_invariant_of_completes
    [ZMod64.PrimeModulus p] (c w : FpPoly p) (base level fuel : Nat)
    (hcompletes : yunFactorsLevelCompletes c w base level fuel) :
    let contribution := yunFactorsContributionWithLevel c w base level fuel
    contribution.1 * pow contribution.2 base =
      pow c (base * level) * pow w base := by
  induction fuel generalizing c w level with
  | zero =>
      -- contribution = (1, w); hcompletes gives c = 1.
      have hc_eq : c = 1 := eq_one_of_isOne_true c hcompletes
      subst hc_eq
      simp [yunFactorsContributionWithLevel, pow_one_base]
  | succ fuel ih =>
      by_cases hc : isOne c = true
      · -- Loop terminates immediately: contribution = (1, w), c = 1.
        have hc_eq : c = 1 := eq_one_of_isOne_true c hc
        subst hc_eq
        simp [yunFactorsContributionWithLevel, hc, pow_one_base]
      · have hc_false : isOne c = false := by
          cases h : isOne c
          · rfl
          · exact False.elim (hc h)
        have htail_completes :
            yunFactorsLevelCompletes
              (monicGcd c w) (w / monicGcd c w) base (level + 1) fuel := by
          cases hcompletes with
          | inl hcone => exact False.elim (hc hcone)
          | inr htail => exact htail
        have htail := ih (monicGcd c w) (w / monicGcd c w) (level + 1)
          htail_completes
        -- htail :
        --   (yunFactorsContributionWithLevel y v base (level+1) fuel).1 *
        --     pow (yunFactorsContributionWithLevel y v base (level+1) fuel).2 base =
        --   pow y (base * (level + 1)) * pow v base
        simp only [yunFactorsContributionWithLevel, hc_false]
        -- Goal involves let-bound y := gcd c w, z := c/y, tail := ...
        by_cases hz : isOne (c / monicGcd c w) = true
        · -- z = 1 case: contribution.1 = tail.1
          have hz_eq : c / monicGcd c w = 1 := eq_one_of_isOne_true _ hz
          simp [hz_eq, pow_one_base]
          -- pow c (b*l) = pow (z * y) (b*l) = pow z (b*l) * pow y (b*l)
          -- With z = 1: pow c (b*l) = pow y (b*l)
          -- htail gives: tail.1 * pow tail.2 base = pow y (base*(level+1)) * pow v base
          -- We want: tail.1 * pow tail.2 base = pow c (b*l) * pow w base
          -- This follows from the step algebra with z=1.
          have hstep :=
            yunFactorsContributionWithLevel_pow_step_algebra c w base level
          rw [hz_eq, pow_one_base, one_mul] at hstep
          rw [hstep]
          exact htail
        · -- z ≠ 1 case: contribution.1 = pow z (b*l) * tail.1
          have hz_false : isOne (c / monicGcd c w) = false := by
            cases h : isOne (c / monicGcd c w)
            · rfl
            · exact False.elim (hz h)
          simp [hz_false]
          -- Goal: pow z (b*l) * tail.1 * pow tail.2 base = pow c (b*l) * pow w base
          have hstep :=
            yunFactorsContributionWithLevel_pow_step_algebra c w base level
          calc pow (c / monicGcd c w) (base * level) *
                  (yunFactorsContributionWithLevel
                    (monicGcd c w) (w / monicGcd c w) base (level + 1) fuel).1 *
                  pow (yunFactorsContributionWithLevel
                    (monicGcd c w) (w / monicGcd c w) base (level + 1) fuel).2 base
              = pow (c / monicGcd c w) (base * level) *
                  ((yunFactorsContributionWithLevel
                    (monicGcd c w) (w / monicGcd c w) base (level + 1) fuel).1 *
                    pow (yunFactorsContributionWithLevel
                      (monicGcd c w) (w / monicGcd c w) base (level + 1) fuel).2 base) :=
                DensePoly.mul_assoc_poly _ _ _
            _ = pow (c / monicGcd c w) (base * level) *
                  (pow (monicGcd c w) (base * (level + 1)) *
                    pow (w / monicGcd c w) base) :=
                congrArg
                  (fun x => pow (c / monicGcd c w) (base * level) * x) htail
            _ = pow (c / monicGcd c w) (base * level) *
                  pow (monicGcd c w) (base * (level + 1)) *
                  pow (w / monicGcd c w) base :=
                (DensePoly.mul_assoc_poly _ _ _).symm
            _ = pow c (base * level) * pow w base := hstep.symm

private theorem gcd_isZero_false_of_right_isZero_false
    [ZMod64.PrimeModulus p] (a b : FpPoly p)
    (hb : b.isZero = false) :
    (DensePoly.gcd a b).isZero = false := by
  cases hg : (DensePoly.gcd a b).isZero
  · rfl
  · have hg_zero : DensePoly.gcd a b = 0 :=
      eq_zero_of_isZero_true (DensePoly.gcd a b) hg
    rcases DensePoly.gcd_dvd_right a b with ⟨q, hq⟩
    have hb_zero : b = 0 := by
      rw [hq, hg_zero, zero_mul]
    have hb_true : b.isZero = true := by
      rw [hb_zero]
      rfl
    rw [hb_true] at hb
    cases hb

private theorem yunFactorsContribution_step_split
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) :
    let y := monicGcd c w
    let z := c / y
    z * y = c ∧ (w / y) * y = w := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  constructor
  · exact div_monicGcd_mul_reconstruct hp c w
  · exact div_monicGcd_right_mul_reconstruct hp c w

/-- `dvd_add_poly`: a common divisor of `a` and `b` divides their sum `a + b`. -/
private theorem dvd_add_poly
    {d a b : FpPoly p} (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ a + b := by
  rcases hda with ⟨qa, hqa⟩
  rcases hdb with ⟨qb, hqb⟩
  refine ⟨qa + qb, ?_⟩
  calc a + b
      = d * qa + d * qb := by rw [hqa, hqb]
    _ = d * (qa + qb) := (DensePoly.mul_add_right_poly d qa qb).symm

/-- `dvd_mul_left_of_dvd`: if `d ∣ a` then `d` divides the left-multiplied
product `b * a`. -/
private theorem dvd_mul_left_of_dvd
    {d a b : FpPoly p} (hda : d ∣ a) :
    d ∣ b * a := by
  rcases hda with ⟨q, hq⟩
  refine ⟨b * q, ?_⟩
  calc b * a
      = b * (d * q) := by rw [hq]
    _ = (b * d) * q := (DensePoly.mul_assoc_poly b d q).symm
    _ = (d * b) * q := by
          exact congrArg (fun x => x * q) (DensePoly.mul_comm_poly b d)
    _ = d * (b * q) := DensePoly.mul_assoc_poly d b q

/-- `dvd_mul_right_of_dvd`: if `d ∣ a` then `d` divides the right-multiplied
product `a * b`. -/
private theorem dvd_mul_right_of_dvd
    {d a b : FpPoly p} (hda : d ∣ a) :
    d ∣ a * b := by
  rcases hda with ⟨q, hq⟩
  refine ⟨q * b, ?_⟩
  calc a * b
      = (d * q) * b := by rw [hq]
    _ = d * (q * b) := DensePoly.mul_assoc_poly d q b

/-- `monicGcd` analogue of `DensePoly.dvd_gcd`: any common divisor of `c` and
`w` divides their monic gcd. The monic gcd is a constant-scalar associate of the
raw gcd, so it has the same divisors. -/
private theorem dvd_monicGcd
    [ZMod64.PrimeModulus p] (_hp : Hex.Nat.Prime p)
    {d : FpPoly p} (c w : FpPoly p) (hdc : d ∣ c) (hdw : d ∣ w) :
    d ∣ monicGcd c w := by
  have hdg : d ∣ DensePoly.gcd c w := DensePoly.dvd_gcd d c w hdc hdw
  cases hgz : (DensePoly.gcd c w).isZero with
  | true =>
      have hmg0 : monicGcd c w = 0 := by
        rw [monicGcd_def, normalizeMonic_zero _ hgz]
      exact ⟨0, by rw [hmg0]; simp⟩
  | false =>
      have hmg :
          monicGcd c w =
            DensePoly.C (DensePoly.leadingCoeff (DensePoly.gcd c w))⁻¹ *
              DensePoly.gcd c w := by
        rw [monicGcd_def, normalizeMonic_nonzero _ hgz, C_mul_eq_scale]
      rw [hmg]
      exact dvd_mul_left_of_dvd hdg

/-- `dvd_sub_poly`: a common divisor of `a` and `b` divides their difference
`a - b`. -/
private theorem dvd_sub_poly
    {d a b : FpPoly p} (hda : d ∣ a) (hdb : d ∣ b) :
    d ∣ a - b := by
  exact DensePoly.dvd_sub_poly hda hdb

/-- `pow_succ_dvd_mul_right_of_dvd`: the extra factor of `d` in `a * d * b` bumps
a prime-power divisor's exponent, so `pow d (n+1) ∣ a` gives
`pow d (n+2) ∣ a * d * b`. -/
private theorem pow_succ_dvd_mul_right_of_dvd
    {d a b : FpPoly p} {n : Nat}
    (h : pow d (n + 1) ∣ a) :
    pow d (n + 2) ∣ a * d * b := by
  rcases h with ⟨q, hq⟩
  refine ⟨q * b, ?_⟩
  calc a * d * b
      = (pow d (n + 1) * q) * d * b := by rw [hq]
    _ = (pow d (n + 1) * (q * d)) * b := by
          exact congrArg (fun x => x * b)
            (DensePoly.mul_assoc_poly (pow d (n + 1)) q d)
    _ = (pow d (n + 1) * (d * q)) * b := by
          exact congrArg (fun x => (pow d (n + 1) * x) * b)
            (DensePoly.mul_comm_poly q d)
    _ = (pow d (n + 1) * d) * q * b := by
          exact congrArg (fun x => x * b)
            (DensePoly.mul_assoc_poly (pow d (n + 1)) d q).symm
    _ = pow d (n + 2) * (q * b) := by
          rw [← pow_succ d (n + 1)]
          exact DensePoly.mul_assoc_poly (pow d (n + 2)) q b

/-- `pow_succ_dvd_mul_of_dvd_left_of_pow_dvd_right`: combining `d ∣ a` on the left
factor with `pow d n ∣ b` on the right gives `pow d (n+1) ∣ a * b`. -/
private theorem pow_succ_dvd_mul_of_dvd_left_of_pow_dvd_right
    {d a b : FpPoly p} {n : Nat}
    (hda : d ∣ a) (hdb : pow d n ∣ b) :
    pow d (n + 1) ∣ a * b := by
  rcases hda with ⟨qa, hqa⟩
  rcases hdb with ⟨qb, hqb⟩
  refine ⟨qa * qb, ?_⟩
  calc a * b
      = (d * qa) * (pow d n * qb) := by rw [hqa, hqb]
    _ = (pow d n * d) * (qa * qb) := by
          calc
            (d * qa) * (pow d n * qb)
                = ((d * qa) * pow d n) * qb := by
                  exact (DensePoly.mul_assoc_poly (d * qa) (pow d n) qb).symm
            _ = (pow d n * (d * qa)) * qb := by
                  exact congrArg (fun x => x * qb)
                    (DensePoly.mul_comm_poly (d * qa) (pow d n))
            _ = ((pow d n * d) * qa) * qb := by
                  exact congrArg (fun x => x * qb)
                    (DensePoly.mul_assoc_poly (pow d n) d qa).symm
            _ = (pow d n * d) * (qa * qb) := by
                  exact DensePoly.mul_assoc_poly (pow d n * d) qa qb
    _ = pow d (n + 1) * (qa * qb) := by rw [← pow_succ d n]

/-- `pow_succ_dvd_mul_of_pow_dvd_left_of_dvd_right`: combining `pow d n ∣ a` on the
left factor with `d ∣ b` on the right gives `pow d (n+1) ∣ a * b`. -/
private theorem pow_succ_dvd_mul_of_pow_dvd_left_of_dvd_right
    {d a b : FpPoly p} {n : Nat}
    (hda : pow d n ∣ a) (hdb : d ∣ b) :
    pow d (n + 1) ∣ a * b := by
  rcases hda with ⟨qa, hqa⟩
  rcases hdb with ⟨qb, hqb⟩
  refine ⟨qa * qb, ?_⟩
  calc a * b
      = (pow d n * qa) * (d * qb) := by rw [hqa, hqb]
    _ = (pow d n * d) * (qa * qb) := by
          calc
            (pow d n * qa) * (d * qb)
                = ((pow d n * qa) * d) * qb := by
                  exact (DensePoly.mul_assoc_poly (pow d n * qa) d qb).symm
            _ = (pow d n * (qa * d)) * qb := by
                  exact congrArg (fun x => x * qb)
                    (DensePoly.mul_assoc_poly (pow d n) qa d)
            _ = (pow d n * (d * qa)) * qb := by
                  exact congrArg (fun x => (pow d n * x) * qb)
                    (DensePoly.mul_comm_poly qa d)
            _ = ((pow d n * d) * qa) * qb := by
                  exact congrArg (fun x => x * qb)
                    (DensePoly.mul_assoc_poly (pow d n) d qa).symm
            _ = (pow d n * d) * (qa * qb) := by
                  exact DensePoly.mul_assoc_poly (pow d n * d) qa qb
    _ = pow d (n + 1) * (qa * qb) := by rw [← pow_succ d n]

private theorem quotient_common_dvd_mul_derivative_base
    [ZMod64.PrimeModulus p] (d c : FpPoly p)
    (hdc : d ∣ c)
    (hddc : d ∣ DensePoly.derivative c) :
    ∃ q, c = d * q ∧ d ∣ q * DensePoly.derivative d := by
  rcases hdc with ⟨q, hq⟩
  refine ⟨q, hq, ?_⟩
  have hderiv :
      DensePoly.derivative c =
        DensePoly.derivative d * q + d * DensePoly.derivative q := by
    rw [hq]
    exact DensePoly.derivative_mul d q
  have hd_second : d ∣ d * DensePoly.derivative q := ⟨DensePoly.derivative q, rfl⟩
  have hd_first : d ∣ DensePoly.derivative d * q := by
    have hsub : d ∣ DensePoly.derivative c - d * DensePoly.derivative q :=
      dvd_sub_poly hddc hd_second
    have hfirst_eq :
        DensePoly.derivative c - d * DensePoly.derivative q =
          DensePoly.derivative d * q := by
      rw [hderiv, sub_eq_add_neg]
      calc
        (DensePoly.derivative d * q + d * DensePoly.derivative q) +
            -(d * DensePoly.derivative q)
            = DensePoly.derivative d * q +
                (d * DensePoly.derivative q + -(d * DensePoly.derivative q)) := by
              exact DensePoly.add_assoc_poly
                (DensePoly.derivative d * q) (d * DensePoly.derivative q)
                (-(d * DensePoly.derivative q))
        _ = DensePoly.derivative d * q + 0 := by rw [add_right_neg]
        _ = DensePoly.derivative d * q := add_zero _
    simpa [hfirst_eq] using hsub
  exact (DensePoly.mul_comm_poly q (DensePoly.derivative d)).symm ▸ hd_first

private theorem pow_succ_dvd_cofactor_mul_derivative
    [ZMod64.PrimeModulus p] {d a : FpPoly p}
    (h : d ∣ a * DensePoly.derivative d) :
    ∀ m : Nat, pow d (m + 1) ∣ a * DensePoly.derivative (pow d (m + 1)) := by
  intro m
  induction m with
  | zero =>
      rw [pow_one]
      exact h
  | succ k ih =>
      rw [pow_succ]
      have hderiv :
          a * DensePoly.derivative (pow d (k + 1) * d) =
            a * (DensePoly.derivative (pow d (k + 1)) * d +
              pow d (k + 1) * DensePoly.derivative d) := by
        exact congrArg (fun x => a * x)
          (DensePoly.derivative_mul (pow d (k + 1)) d)
      rw [hderiv]
      have hsplit :
          a * (DensePoly.derivative (pow d (k + 1)) * d +
              pow d (k + 1) * DensePoly.derivative d) =
            a * (DensePoly.derivative (pow d (k + 1)) * d) +
              a * (pow d (k + 1) * DensePoly.derivative d) :=
        DensePoly.mul_add_right_poly a
          (DensePoly.derivative (pow d (k + 1)) * d)
          (pow d (k + 1) * DensePoly.derivative d)
      rw [hsplit]
      exact dvd_add_poly
        (by
          rcases ih with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          calc
            a * (DensePoly.derivative (pow d (k + 1)) * d)
                = (a * DensePoly.derivative (pow d (k + 1))) * d := by
                  exact (DensePoly.mul_assoc_poly a
                    (DensePoly.derivative (pow d (k + 1))) d).symm
            _ = (pow d (k + 1) * q) * d := by rw [hq]
            _ = (pow d (k + 1) * d) * q := by
                  calc
                    (pow d (k + 1) * q) * d
                        = pow d (k + 1) * (q * d) := by
                          exact DensePoly.mul_assoc_poly (pow d (k + 1)) q d
                    _ = pow d (k + 1) * (d * q) := by
                          exact congrArg (fun x => pow d (k + 1) * x)
                            (DensePoly.mul_comm_poly q d)
                    _ = (pow d (k + 1) * d) * q := by
                          exact (DensePoly.mul_assoc_poly (pow d (k + 1)) d q).symm
            _ = (pow d (k + 1) * d) * q := by rfl)
        (by
          rcases h with ⟨q, hq⟩
          refine ⟨q, ?_⟩
          calc
            a * (pow d (k + 1) * DensePoly.derivative d)
                = (a * DensePoly.derivative d) * pow d (k + 1) := by
                  calc
                    a * (pow d (k + 1) * DensePoly.derivative d)
                        = a * (DensePoly.derivative d * pow d (k + 1)) := by
                          exact congrArg (fun x => a * x)
                            (DensePoly.mul_comm_poly (pow d (k + 1))
                              (DensePoly.derivative d))
                    _ = (a * DensePoly.derivative d) * pow d (k + 1) := by
                          exact (DensePoly.mul_assoc_poly a
                            (DensePoly.derivative d) (pow d (k + 1))).symm
            _ = (d * q) * pow d (k + 1) := by rw [hq]
            _ = (pow d (k + 1) * d) * q := by
                  calc
                    (d * q) * pow d (k + 1)
                        = pow d (k + 1) * (d * q) := by
                          exact DensePoly.mul_comm_poly (d * q) (pow d (k + 1))
                    _ = (pow d (k + 1) * d) * q := by
                          exact (DensePoly.mul_assoc_poly (pow d (k + 1)) d q).symm
            _ = (pow d (k + 1) * d) * q := by rfl)

private theorem yunStep_common_dvd_derivative_product
    (z y d : FpPoly p)
    (hdz : d ∣ z) (hdy : d ∣ y) :
    d ∣ DensePoly.derivative (z * y) := by
  have hterms :
      d ∣ DensePoly.derivative z * y + z * DensePoly.derivative y :=
    dvd_add_poly
      (dvd_mul_left_of_dvd hdy)
      (dvd_mul_right_of_dvd hdz)
  exact (DensePoly.derivative_mul z y).symm ▸ hterms

private theorem yunStep_common_dvd_derivative_current
    [ZMod64.PrimeModulus p]
    (c w d : FpPoly p)
    (hdz : d ∣ c / monicGcd c w)
    (hdy : d ∣ monicGcd c w) :
    d ∣ DensePoly.derivative c := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  let y := monicGcd c w
  let z := c / y
  have hprod : z * y = c := by
    simpa [z, y] using div_monicGcd_mul_reconstruct hp c w
  rw [← hprod]
  exact yunStep_common_dvd_derivative_product z y d hdz hdy

private theorem derivativeSplit_common_dvd_quotient_derivative_dvd_gcd
    [ZMod64.PrimeModulus p]
    (f d : FpPoly p)
    (hdc : d ∣ f / monicGcd f (DensePoly.derivative f))
    (hddc : d ∣ DensePoly.derivative
      (f / monicGcd f (DensePoly.derivative f))) :
    d ∣ monicGcd f (DensePoly.derivative f) := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  have hprod : c * g = f := by
    simpa [c, g] using div_monicGcd_mul_reconstruct hp f (DensePoly.derivative f)
  have hdf :
      DensePoly.derivative f =
        DensePoly.derivative c * g + c * DensePoly.derivative g := by
    rw [← hprod]
    exact DensePoly.derivative_mul c g
  have hdf_dvd_f : d ∣ f := by
    rw [← hprod]
    exact dvd_mul_right_of_dvd (a := c) (b := g) (d := d) (by simpa [c, g] using hdc)
  have hdf_dvd_derivative : d ∣ DensePoly.derivative f := by
    rw [hdf]
    exact dvd_add_poly
      (dvd_mul_right_of_dvd (a := DensePoly.derivative c) (b := g) (d := d)
        (by simpa [c, g] using hddc))
      (dvd_mul_right_of_dvd (a := c) (b := DensePoly.derivative g) (d := d)
        (by simpa [c, g] using hdc))
  exact dvd_monicGcd hp f (DensePoly.derivative f) hdf_dvd_f hdf_dvd_derivative

private theorem derivativeSplit_quotient_pow_succ_dvd_gcd
    [ZMod64.PrimeModulus p] (f d : FpPoly p)
    (hdc : d ∣ f / monicGcd f (DensePoly.derivative f))
    (hddc : d ∣ DensePoly.derivative
      (f / monicGcd f (DensePoly.derivative f))) :
    ∀ n, pow d n ∣ monicGcd f (DensePoly.derivative f) →
      pow d (n + 1) ∣ monicGcd f (DensePoly.derivative f) := by
  have hp : Hex.Nat.Prime p := ZMod64.PrimeModulus.prime (p := p)
  intro n hpow
  let g := monicGcd f (DensePoly.derivative f)
  let c := f / g
  rcases quotient_common_dvd_mul_derivative_base d c
      (by simpa [c, g] using hdc) (by simpa [c, g] using hddc) with
    ⟨a, ha, hcofactor⟩
  have hprod : c * g = f := by
    simpa [c, g] using div_monicGcd_mul_reconstruct hp f (DensePoly.derivative f)
  have hdf :
      DensePoly.derivative f =
        DensePoly.derivative c * g + c * DensePoly.derivative g := by
    rw [← hprod]
    exact DensePoly.derivative_mul c g
  cases n with
  | zero =>
      rw [pow_one]
      exact derivativeSplit_common_dvd_quotient_derivative_dvd_gcd f d
        (by exact ⟨a, by simpa [c, g] using ha⟩) hddc
  | succ k =>
      rcases hpow with ⟨q, hq⟩
      have hg_eq : g = pow d (k + 1) * q := by simpa [g] using hq
      have hsucc_dvd_f : pow d (k + 2) ∣ f := by
        rw [← hprod, ha, hg_eq]
        refine ⟨a * q, ?_⟩
        calc
          (d * a) * (pow d (k + 1) * q)
              = (pow d (k + 1) * d) * (a * q) := by
                calc
                  (d * a) * (pow d (k + 1) * q)
                      = ((d * a) * pow d (k + 1)) * q := by
                        exact (DensePoly.mul_assoc_poly (d * a) (pow d (k + 1)) q).symm
                  _ = (pow d (k + 1) * (d * a)) * q := by
                        exact congrArg (fun x => x * q)
                          (DensePoly.mul_comm_poly (d * a) (pow d (k + 1)))
                  _ = ((pow d (k + 1) * d) * a) * q := by
                        exact congrArg (fun x => x * q)
                          (DensePoly.mul_assoc_poly (pow d (k + 1)) d a).symm
                  _ = (pow d (k + 1) * d) * (a * q) := by
                        exact DensePoly.mul_assoc_poly (pow d (k + 1) * d) a q
          _ = pow d (k + 2) * (a * q) := by rw [← pow_succ d (k + 1)]
      have hsucc_dvd_derivative : pow d (k + 2) ∣ DensePoly.derivative f := by
        rw [hdf]
        have hleft : pow d (k + 2) ∣ DensePoly.derivative c * g := by
          rw [hg_eq]
          exact pow_succ_dvd_mul_of_dvd_left_of_pow_dvd_right
            (by simpa [c, g] using hddc)
            (by exact ⟨q, rfl⟩)
        have hright : pow d (k + 2) ∣ c * DensePoly.derivative g := by
          rw [ha, hg_eq]
          have hderiv :
              (d * a) * DensePoly.derivative (pow d (k + 1) * q) =
                (d * a) * (DensePoly.derivative (pow d (k + 1)) * q +
                  pow d (k + 1) * DensePoly.derivative q) := by
            exact congrArg (fun x => (d * a) * x)
              (DensePoly.derivative_mul (pow d (k + 1)) q)
          rw [hderiv]
          have hsplit :
              (d * a) * (DensePoly.derivative (pow d (k + 1)) * q +
                  pow d (k + 1) * DensePoly.derivative q) =
                (d * a) * (DensePoly.derivative (pow d (k + 1)) * q) +
                  (d * a) * (pow d (k + 1) * DensePoly.derivative q) :=
            DensePoly.mul_add_right_poly (d * a)
              (DensePoly.derivative (pow d (k + 1)) * q)
              (pow d (k + 1) * DensePoly.derivative q)
          rw [hsplit]
          exact dvd_add_poly
            (by
              have haux := pow_succ_dvd_cofactor_mul_derivative hcofactor k
              rcases haux with ⟨r, hr⟩
              refine ⟨r * q, ?_⟩
              calc
                (d * a) * (DensePoly.derivative (pow d (k + 1)) * q)
                    = d * ((a * DensePoly.derivative (pow d (k + 1))) * q) := by
                      calc
                        (d * a) * (DensePoly.derivative (pow d (k + 1)) * q)
                            = ((d * a) * DensePoly.derivative (pow d (k + 1))) * q := by
                              exact (DensePoly.mul_assoc_poly (d * a)
                                (DensePoly.derivative (pow d (k + 1))) q).symm
                        _ = (d * (a * DensePoly.derivative (pow d (k + 1)))) * q := by
                              exact congrArg (fun x => x * q)
                                (DensePoly.mul_assoc_poly d a
                                  (DensePoly.derivative (pow d (k + 1))))
                        _ = d * ((a * DensePoly.derivative (pow d (k + 1))) * q) := by
                              exact DensePoly.mul_assoc_poly d
                                (a * DensePoly.derivative (pow d (k + 1))) q
                _ = d * ((pow d (k + 1) * r) * q) := by rw [hr]
                _ = (pow d (k + 1) * d) * (r * q) := by
                      calc
                        d * ((pow d (k + 1) * r) * q)
                            = (d * (pow d (k + 1) * r)) * q := by
                              exact (DensePoly.mul_assoc_poly d (pow d (k + 1) * r) q).symm
                        _ = ((pow d (k + 1) * r) * d) * q := by
                              exact congrArg (fun x => x * q)
                                (DensePoly.mul_comm_poly d (pow d (k + 1) * r))
                        _ = (pow d (k + 1) * (r * d)) * q := by
                              exact congrArg (fun x => x * q)
                                (DensePoly.mul_assoc_poly (pow d (k + 1)) r d)
                        _ = (pow d (k + 1) * (d * r)) * q := by
                              exact congrArg (fun x => (pow d (k + 1) * x) * q)
                                (DensePoly.mul_comm_poly r d)
                        _ = ((pow d (k + 1) * d) * r) * q := by
                              exact congrArg (fun x => x * q)
                                (DensePoly.mul_assoc_poly (pow d (k + 1)) d r).symm
                        _ = (pow d (k + 1) * d) * (r * q) := by
                              exact DensePoly.mul_assoc_poly (pow d (k + 1) * d) r q
                _ = pow d (k + 2) * (r * q) := by rw [← pow_succ d (k + 1)])
            (by
              refine ⟨a * DensePoly.derivative q, ?_⟩
              calc
                (d * a) * (pow d (k + 1) * DensePoly.derivative q)
                    = (pow d (k + 1) * d) * (a * DensePoly.derivative q) := by
                      calc
                        (d * a) * (pow d (k + 1) * DensePoly.derivative q)
                            = ((d * a) * pow d (k + 1)) * DensePoly.derivative q := by
                              exact (DensePoly.mul_assoc_poly (d * a)
                                (pow d (k + 1)) (DensePoly.derivative q)).symm
                        _ = (pow d (k + 1) * (d * a)) * DensePoly.derivative q := by
                              exact congrArg (fun x => x * DensePoly.derivative q)
                                (DensePoly.mul_comm_poly (d * a) (pow d (k + 1)))
                        _ = ((pow d (k + 1) * d) * a) * DensePoly.derivative q := by
                              exact congrArg (fun x => x * DensePoly.derivative q)
                                (DensePoly.mul_assoc_poly (pow d (k + 1)) d a).symm
                        _ = (pow d (k + 1) * d) * (a * DensePoly.derivative q) := by
                              exact DensePoly.mul_assoc_poly (pow d (k + 1) * d) a
                                (DensePoly.derivative q)
                _ = pow d (k + 2) * (a * DensePoly.derivative q) := by
                      rw [← pow_succ d (k + 1)])
        exact dvd_add_poly hleft hright
      exact dvd_monicGcd hp f (DensePoly.derivative f)
        hsucc_dvd_f hsucc_dvd_derivative

/--
Nonterminal step with empty multiplicity slot: when `c` is not one but the
stripped factor `z = c / gcd c w` is one, no factor power is emitted and the
recursion descends verbatim into the gcd state `(gcd c w, w / gcd c w)` at
index `i + 1`.
-/
private theorem yunFactorsContribution_step_of_not_isOne_of_isOne_z
    (c w : FpPoly p) (i fuel : Nat)
    (hc : isOne c = false)
    (hz : isOne (c / monicGcd c w) = true) :
    yunFactorsContribution c w i (fuel + 1) =
      yunFactorsContribution
        (monicGcd c w) (w / monicGcd c w) (i + 1) fuel := by
  simp [yunFactorsContribution, hc, hz]

/--
Nonterminal step that emits a factor: when neither `c` nor the stripped
factor `z = c / gcd c w` is one, the current contribution multiplies `pow z i`
onto the tail's factor product while passing the tail's residual through
unchanged.  This is the branch that records a multiplicity-`i` square-free
factor.
-/
private theorem yunFactorsContribution_step_of_not_isOne_of_not_isOne_z
    (c w : FpPoly p) (i fuel : Nat)
    (hc : isOne c = false)
    (hz : isOne (c / monicGcd c w) = false) :
    yunFactorsContribution c w i (fuel + 1) =
      (pow (c / monicGcd c w) i *
          (yunFactorsContribution
            (monicGcd c w) (w / monicGcd c w) (i + 1) fuel).1,
        (yunFactorsContribution
          (monicGcd c w) (w / monicGcd c w) (i + 1) fuel).2) := by
  simp [yunFactorsContribution, hc, hz]

/--
Both nonterminal branches descend identically on the residual: when `c` is not
one, the current contribution's residual equals the tail's residual, and the
repeated-part reconstruction `squareFreeAuxRevContribution (pthRoot ·) ·` agrees
between the current and tail states.  The factor-emit choice (`isOne z`) does
not perturb the residual carried into the next round.
-/
private theorem yunFactorsContribution_tail_repeated_descent
    (c w : FpPoly p) (multiplicity fuel : Nat)
    (hc : isOne c = false) :
    let y := monicGcd c w
    let tail := yunFactorsContribution y (w / y) (multiplicity + 1) fuel
    let contribution := yunFactorsContribution c w multiplicity (fuel + 1)
    contribution.2 = tail.2 ∧
      squareFreeAuxRevContribution (pthRoot contribution.2) (multiplicity * p) fuel =
        squareFreeAuxRevContribution (pthRoot tail.2) (multiplicity * p) fuel := by
  by_cases hz : isOne (c / monicGcd c w)
  · simp [yunFactorsContribution, hc, hz]
  · simp [yunFactorsContribution, hc, hz]

/--
Single nonterminal step transports a target equation from the recursive tail
to the current state.  Given branch-wise hypotheses that the tail's factor
product (optionally scaled by `pow z multiplicity`) equals `target`, the step
yields `contribution.1 = target`, `contribution.2 = tail.2`, and the two
gcd/division reconstruction equalities `(c / g) * g = c` and `(w / g) * g = w`.
This is the target-preservation half feeding `yunFactorsContribution_step_target_combiner`.
-/
private theorem yunFactorsContribution_step_preserves_target
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (multiplicity fuel : Nat) (target : FpPoly p)
    (hc : isOne c = false)
    (htarget_one :
      isOne (c / monicGcd c w) = true →
        (yunFactorsContribution
          (monicGcd c w) (w / monicGcd c w)
          (multiplicity + 1) fuel).1 = target)
    (htarget_factor :
      isOne (c / monicGcd c w) = false →
        pow (c / monicGcd c w) multiplicity *
          (yunFactorsContribution
            (monicGcd c w) (w / monicGcd c w)
            (multiplicity + 1) fuel).1 = target) :
    let tail :=
      yunFactorsContribution
        (monicGcd c w) (w / monicGcd c w)
        (multiplicity + 1) fuel
    let contribution := yunFactorsContribution c w multiplicity (fuel + 1)
    contribution.1 = target ∧
      contribution.2 = tail.2 ∧
        (c / monicGcd c w) * monicGcd c w = c ∧
          (w / monicGcd c w) * monicGcd c w = w := by
  dsimp
  have hsplit := yunFactorsContribution_step_split c w
  by_cases hz : isOne (c / monicGcd c w) = true
  · have hstep :=
      yunFactorsContribution_step_of_not_isOne_of_isOne_z
        c w multiplicity fuel hc hz
    rw [hstep]
    exact ⟨htarget_one hz, rfl, hsplit.1, hsplit.2⟩
  · have hz_false : isOne (c / monicGcd c w) = false := by
      cases h : isOne (c / monicGcd c w)
      · rfl
      · exact False.elim (hz h)
    have hstep :=
      yunFactorsContribution_step_of_not_isOne_of_not_isOne_z
        c w multiplicity fuel hc hz_false
    rw [hstep]
    exact ⟨htarget_factor hz_false, rfl, hsplit.1, hsplit.2⟩

/--
One nonterminal Yun step preserves the caller's target contribution and
keeps the repeated tail aligned with the recursive state.  This packages the
algebra needed by the successor fuel proof: callers supply the target facts
for the recursive tail, and the lemma returns the corresponding current-state
facts plus the two gcd/division reconstruction equalities.
-/
private theorem yunFactorsContribution_step_target_combiner
    [ZMod64.PrimeModulus p]
    (c w : FpPoly p) (multiplicity fuel : Nat) (target : FpPoly p)
    (hc : isOne c = false)
    (htarget_one :
      isOne (c / monicGcd c w) = true →
        (yunFactorsContribution
          (monicGcd c w) (w / monicGcd c w)
          (multiplicity + 1) fuel).1 = target)
    (htarget_factor :
      isOne (c / monicGcd c w) = false →
        pow (c / monicGcd c w) multiplicity *
          (yunFactorsContribution
            (monicGcd c w) (w / monicGcd c w)
            (multiplicity + 1) fuel).1 = target) :
    let y := monicGcd c w
    let tail :=
      yunFactorsContribution y (w / y) (multiplicity + 1) fuel
    let contribution := yunFactorsContribution c w multiplicity (fuel + 1)
    contribution.1 = target ∧
      contribution.2 = tail.2 ∧
        squareFreeAuxRevContribution (pthRoot contribution.2)
            (multiplicity * p) fuel =
          squareFreeAuxRevContribution (pthRoot tail.2)
            (multiplicity * p) fuel ∧
          (c / y) * y = c ∧ (w / y) * y = w := by
  dsimp
  have htarget :=
    yunFactorsContribution_step_preserves_target
      c w multiplicity fuel target hc htarget_one htarget_factor
  have hdescent :=
    yunFactorsContribution_tail_repeated_descent
      c w multiplicity fuel hc
  exact
    ⟨htarget.1, htarget.2.1, hdescent.2,
      htarget.2.2.1, htarget.2.2.2⟩

/--
Inductive predicate capturing states `(c, w, fuel)` reachable from the initial
derivative-active split of `f`. Used to scope the state payload hypothesis
expected by `yunFactorsLevelCompletes_of_derivative_active_initial_split`,
which the derivative-active branch threads into the recursive correctness
chain.
-/
private inductive yunFactorsDerivativeActiveReachable
    (hp : Hex.Nat.Prime p) (f : FpPoly p) :
    FpPoly p → FpPoly p → Nat → Prop
  | derivativeSplit (fuel : Nat)
      (hdf : (DensePoly.derivative f).isZero ≠ true) :
      yunFactorsDerivativeActiveReachable hp f
        (f / monicGcd f (DensePoly.derivative f))
        (monicGcd f (DensePoly.derivative f))
        fuel
  | step (c w : FpPoly p) (fuel : Nat) :
      yunFactorsDerivativeActiveReachable hp f c w (fuel + 1) →
      yunFactorsDerivativeActiveReachable hp f
        (monicGcd c w)
        (w / monicGcd c w)
        fuel


end FpPoly
end Hex
