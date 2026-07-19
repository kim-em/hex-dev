/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.Analysis.Complex.Polynomial.Basic

public section

/-!
# Polynomial logarithmic derivatives on circles

This Mathlib-only module packages the partial-fraction and circle-integral
lemmas used by the polynomial argument principle. Root multisets are retained
throughout, so repeated roots contribute with their multiplicity.
-/

open Complex Metric Polynomial Set

namespace HexRootsMathlib

noncomputable section

/-- Difference of two reciprocal linear factors, with both poles excluded. -/
theorem reciprocal_sub {z a b : ℂ} (hza : z ≠ a) (hzb : z ≠ b) :
    (z - a)⁻¹ - (z - b)⁻¹ =
      (a - b) / ((z - a) * (z - b)) := by
  calc
    (z - a)⁻¹ - (z - b)⁻¹ =
        ((z - b) - (z - a)) / ((z - a) * (z - b)) :=
      inv_sub_inv (sub_ne_zero.mpr hza) (sub_ne_zero.mpr hzb)
    _ = (a - b) / ((z - a) * (z - b)) := by ring

/-- The logarithmic derivative of a complex polynomial is the sum of its
reciprocal linear factors, counted over the root multiset. -/
theorem logDeriv_eq_sum (p : ℂ[X]) {z : ℂ} (hz : p.eval z ≠ 0) :
    p.derivative.eval z / p.eval z =
      (p.roots.map fun a => (z - a)⁻¹).sum := by
  simpa only [one_div] using
    (IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hz

/-- A reciprocal linear factor is circle integrable exactly when its pole is
not on the circle (apart from the degenerate zero-radius case). -/
theorem subInv_circleIntegrable {c a : ℂ} {R : ℝ}
    (ha : a ∉ sphere c |R|) :
    CircleIntegrable (fun z : ℂ => (z - a)⁻¹) c R := by
  exact circleIntegrable_sub_inv_iff.mpr (Or.inr ha)

/-- A pole strictly inside a positive-radius circle contributes `2πi`. -/
theorem integral_subInv_inside {c a : ℂ} {R : ℝ} (ha : a ∈ ball c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 2 * Real.pi * I :=
  circleIntegral.integral_sub_inv_of_mem_ball ha

/-- A pole outside the closed disc contributes zero. -/
theorem integral_subInv_outside {c a : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (ha : a ∉ closedBall c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  have hne : ∀ z ∈ closure (ball c R), z - a ≠ 0 := by
    intro z hz hza
    apply ha
    have : z = a := sub_eq_zero.mp hza
    subst z
    exact closure_ball_subset_closedBall hz
  exact ((differentiable_id.diffContOnCl.sub_const a).inv hne).circleIntegral_eq_zero hR

/-- A finite multiset sum of reciprocal linear factors is circle integrable
when none of its poles lies on the circle. -/
private theorem sum_subInv_circleIntegrable {roots : Multiset ℂ}
    {c : ℂ} {R : ℝ} (hroots : ∀ a ∈ roots, a ∉ sphere c |R|) :
    CircleIntegrable (fun z => (roots.map fun a => (z - a)⁻¹).sum) c R := by
  induction roots using Multiset.induction_on with
  | empty =>
      simp only [Multiset.map_zero, Multiset.sum_zero]
      exact circleIntegrable_const 0 c R
  | @cons a roots ih =>
      have ha := subInv_circleIntegrable (hroots a (Multiset.mem_cons_self a roots))
      have htail := ih (fun b hb => hroots b (Multiset.mem_cons_of_mem hb))
      apply (circleIntegrable_congr ?_).mpr (ha.add htail)
      intro z hz
      simp only [Multiset.map_cons, Multiset.sum_cons, Pi.add_apply]

/-- Circle integration commutes with a finite multiset sum of reciprocal
linear factors when none of the poles lies on the circle. -/
theorem integral_sum_subInv {roots : Multiset ℂ} {c : ℂ} {R : ℝ}
    (hroots : ∀ a ∈ roots, a ∉ sphere c |R|) :
    (∮ z in C(c, R), (roots.map fun a => (z - a)⁻¹).sum) =
      (roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum := by
  induction roots using Multiset.induction_on with
  | empty => simp [circleIntegral]
  | @cons a roots ih =>
      have ha := subInv_circleIntegrable (hroots a (Multiset.mem_cons_self a roots))
      have htail : ∀ b ∈ roots, b ∉ sphere c |R| :=
        fun b hb => hroots b (Multiset.mem_cons_of_mem hb)
      simp only [Multiset.map_cons, Multiset.sum_cons]
      rw [circleIntegral.integral_add ha (sum_subInv_circleIntegrable htail), ih htail]

/-- If a polynomial has no root on a nonnegative-radius circle, then its
logarithmic derivative is circle integrable. -/
theorem logDeriv_circleIntegrable {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    CircleIntegrable (fun z => p.derivative.eval z / p.eval z) c R := by
  let terms : ℂ → ℂ := fun z => (p.roots.map fun a => (z - a)⁻¹).sum
  have hterms : CircleIntegrable terms c R := by
    dsimp only [terms]
    apply sum_subInv_circleIntegrable
    intro a haRoot haSphere
    rw [abs_of_nonneg hR] at haSphere
    exact hboundary a haSphere ((mem_roots hp).mp haRoot)
  apply (circleIntegrable_congr ?_).mpr hterms
  intro z hz
  have hz' : z ∈ sphere c R := by simpa [abs_of_nonneg hR] using hz
  exact logDeriv_eq_sum p (hboundary z hz')

/-- The circle integral of a polynomial logarithmic derivative is the
multiset sum of its reciprocal-factor integrals. -/
theorem integral_logDeriv_eq_sum {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
      (p.roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum := by
  have hroots : ∀ a ∈ p.roots, a ∉ sphere c |R| := by
    intro a haRoot haSphere
    rw [abs_of_nonneg hR] at haSphere
    exact hboundary a haSphere ((mem_roots hp).mp haRoot)
  calc
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
        ∮ z in C(c, R), (p.roots.map fun a => (z - a)⁻¹).sum := by
      apply circleIntegral.integral_congr hR
      intro z hz
      exact logDeriv_eq_sum p (hboundary z hz)
    _ = _ := integral_sum_subInv hroots

end

end HexRootsMathlib
