/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexNumberFieldMathlib.PrincipalRoot
public import Mathlib.RingTheory.RootsOfUnity.Complex
public section

/-! The primitive root of unity nearest to the positive real axis in the upper half plane. -/
namespace HexNumberFieldMathlib.Unity
open Complex Real

/-- The standard positive primitive root of unity. -/
@[expose] noncomputable def zeta (n : Nat) : ℂ := exp (2 * π * I / n)

theorem primitive {n : Nat} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n := by
  simpa [zeta, div_eq_mul_inv] using Complex.isPrimitiveRoot_exp_of_coprime 1 n hn (Nat.coprime_one_left n)

theorem arg_zeta {n : Nat} (hn : 2 < n) : (zeta n).arg = 2 * π / n := by
  have hn' : (2 : ℝ) < n := by exact_mod_cast hn
  rw [zeta, arg_exp]
  have him : (2 * (π : ℂ) * I / n).im = 2 * π / n := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) by simp, div_ofReal_im]
    simp
  rw [him]
  apply (toIocMod_eq_self Real.two_pi_pos).mpr
  have hpos : 0 < 2 * π / (n : ℝ) := div_pos (by positivity) (by linarith)
  have hlt : 2 * π / (n : ℝ) < π := (div_lt_iff₀ (by linarith)).mpr (by nlinarith [pi_pos])
  constructor <;> linarith [pi_pos]

theorem im_zeta {n : Nat} (hn : 2 < n) : 0 < (zeta n).im := by
  have hn' : (2 : ℝ) < n := by exact_mod_cast hn
  apply PrincipalRoot.im_pos ((primitive (by omega)).ne_zero (by omega))
  · rw [arg_zeta hn]; positivity
  · rw [arg_zeta hn]; exact (div_lt_iff₀ (by linarith)).mpr (by nlinarith [pi_pos])

/-- Positive arguments of nth roots of unity are at least one full turn divided by n. -/
theorem arg_lower {n : Nat} (hn : n ≠ 0) {w : ℂ} (hw : w ^ n = 1) (him : 0 < w.im) :
    2 * π / n ≤ w.arg := by
  have hw0 : w ≠ 0 := by intro h; simp [h] at him
  have ha : 0 < w.arg := by
    have hnonneg := arg_nonneg_iff.mpr him.le
    have hne : w.arg ≠ 0 := fun h => (ne_of_gt him) (arg_eq_zero_iff.mp h).2
    exact lt_of_le_of_ne hnonneg (Ne.symm hne)
  have he : exp ((n : ℂ) * log w) = 1 := by rw [Complex.exp_nat_mul, Complex.exp_log hw0, hw]
  obtain ⟨k, hk⟩ := exp_eq_one_iff.mp he
  have hk' : (n : ℝ) * w.arg = (k : ℝ) * (2 * π) := by
    have h := congrArg Complex.im hk
    simpa [Complex.log_im] using h
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hkpos : (0 : ℝ) < k := by nlinarith [pi_pos, mul_pos hn' ha]
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by exact_mod_cast hkpos)
  apply (div_le_iff₀ hn').mpr
  nlinarith [pi_pos]

/-- Maximal real part among upper roots selects the standard primitive root. -/
theorem eq_of_max {n : Nat} (hn : 2 < n) {w : ℂ} (hw : w ^ n = 1)
    (him : 0 < w.im) (hre : (zeta n).re ≤ w.re) : w = zeta n := by
  have hn0 : n ≠ 0 := by omega
  have hw0 : w ≠ 0 := by intro h; simp [h] at him
  have hz0 := (primitive hn0).ne_zero hn0
  have hwNorm : ‖w‖ = 1 := by
    apply (pow_left_inj₀ (norm_nonneg w) (by positivity : (0 : ℝ) ≤ 1) hn0).mp
    simpa only [norm_pow, norm_one, one_pow] using congrArg norm hw
  have hzNorm : ‖zeta n‖ = 1 := (primitive hn0).norm'_eq_one hn0
  have habs := PrincipalRoot.abs_arg_le hw0 hz0 (hwNorm.trans hzNorm.symm) hre
  rw [abs_of_nonneg (arg_nonneg_iff.mpr him.le), arg_zeta hn,
    abs_of_pos (by positivity : 0 < 2 * π / (n : ℝ))] at habs
  exact ext_norm_arg (hwNorm.trans hzNorm.symm) (by rw [arg_zeta hn]; exact le_antisymm habs (arg_lower hn0 hw him))

end HexNumberFieldMathlib.Unity
