/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import Mathlib.Analysis.SpecialFunctions.Pow.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public section

/-! A principal radical is selected by maximal real part and the upper branch on ties. -/
namespace HexNumberFieldMathlib.PrincipalRoot
open Complex Real

/-- The principal radical has argument in the expected half-open sector. -/
theorem sector {z : ℂ} (hz : z ≠ 0) {n : Nat} (hn : n ≠ 0) :
    -(π / n) < (z ^ ((n : ℂ)⁻¹)).arg ∧ (z ^ ((n : ℂ)⁻¹)).arg ≤ π / n := by
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  have hnge : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
  have hc : π / n ≤ π := div_le_self pi_pos.le hnge
  have hlo : -(π / n) < z.arg / n := by
    rw [← neg_div]
    exact (div_lt_div_iff_of_pos_right hnpos).mpr (neg_pi_lt_arg z)
  have hhi : z.arg / n ≤ π / n := div_le_div_of_nonneg_right (arg_le_pi z) hnpos.le
  have him : (log z * (n : ℂ)⁻¹).im = z.arg / n := by
    rw [← div_eq_mul_inv, show (n : ℂ) = ((n : ℝ) : ℂ) by simp,
      Complex.div_ofReal_im, Complex.log_im]
  have ha : (z ^ ((n : ℂ)⁻¹)).arg = z.arg / n := by
    rw [cpow_def_of_ne_zero hz, arg_exp, him]
    apply (toIocMod_eq_self Real.two_pi_pos).mpr
    constructor <;> linarith
  rw [ha]
  exact ⟨hlo, hhi⟩

/-- On a circle, greater real part means smaller absolute argument. -/
theorem abs_arg_le {w v : ℂ} (hw : w ≠ 0) (hv : v ≠ 0)
    (hnorm : ‖w‖ = ‖v‖) (hre : v.re ≤ w.re) : |w.arg| ≤ |v.arg| := by
  by_contra h
  have hlt : |v.arg| < |w.arg| := lt_of_not_ge h
  have hcos := Real.cos_lt_cos_of_nonneg_of_le_pi (abs_nonneg v.arg) (abs_arg_le_pi w) hlt
  rw [Real.cos_abs, Real.cos_abs, cos_arg hw, cos_arg hv, hnorm] at hcos
  have hnormpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  exact (not_lt_of_ge hre) ((div_lt_div_iff_of_pos_right hnormpos).mp hcos)

/-- Maximal real part, with the nonnegative imaginary side preferred on a tie,
selects exactly Mathlib's principal nth root. -/
theorem eq_of_max {z w : ℂ} {n : Nat} (hn : n ≠ 0) (hw : w ^ n = z)
    (hre : ∀ v : ℂ, v ^ n = z → v.re ≤ w.re)
    (him : ∀ v : ℂ, v ^ n = z → v.re = w.re → 0 ≤ v.im → 0 ≤ w.im) :
    w = z ^ ((n : ℂ)⁻¹) := by
  by_cases hz : z = 0
  · have hwz : w = 0 := (pow_eq_zero_iff hn).mp (hw.trans hz)
    subst w
    simp [hz, hn]
  let v := z ^ ((n : ℂ)⁻¹)
  have hv : v ^ n = z := cpow_nat_inv_pow z hn
  have hw0 : w ≠ 0 := fun h => hz (by rw [← hw, h, zero_pow hn])
  have hv0 : v ≠ 0 := fun h => hz (by rw [← hv, h, zero_pow hn])
  have hnorm : ‖w‖ = ‖v‖ := by
    apply (pow_left_inj₀ (norm_nonneg w) (norm_nonneg v) hn).mp
    simpa only [norm_pow] using congrArg norm (hw.trans hv.symm)
  have harg := abs_arg_le hw0 hv0 hnorm (hre v hv)
  have hsector := sector hz hn
  change -(π / n) < v.arg ∧ v.arg ≤ π / n at hsector
  have habs : |v.arg| ≤ π / n := abs_le.mpr ⟨hsector.1.le, hsector.2⟩
  have hwsector := abs_le.mp (harg.trans habs)
  have hc : 0 < π / (n : ℝ) := div_pos pi_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn))
  have hwlo : -(π / n) < w.arg := by
    by_contra h
    have hwa : w.arg = -(π / n) := by linarith [hwsector.1]
    have hwb : |w.arg| = π / n := by rw [hwa, abs_neg, abs_of_pos hc]
    have hva : v.arg = π / n := by
      rw [hwb] at harg
      rcases le_total 0 v.arg with hp | hp
      · rw [abs_of_nonneg hp] at harg
        linarith [hsector.2]
      · rw [abs_of_nonpos hp] at harg
        linarith [hsector.1]
    have hreq : v.re = w.re := by
      rw [← norm_mul_cos_arg v, ← norm_mul_cos_arg w, hnorm, hwa, hva, Real.cos_neg]
    have hvim : 0 ≤ v.im := arg_nonneg_iff.mp (by rw [hva]; exact hc.le)
    have hwim : w.im < 0 := arg_neg_iff.mp (by rw [hwa]; linarith)
    exact (not_le_of_gt hwim) (him v hv hreq hvim)
  have heq := pow_cpow_nat_inv hn hwlo hwsector.2
  rw [hw] at heq
  exact heq.symm

end HexNumberFieldMathlib.PrincipalRoot
