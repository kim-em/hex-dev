/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.MeasureTheory.Integral.CircleIntegral
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.Nat

public section

/-!
# Topology for polynomial argument-principle homotopies

This Mathlib-only module records continuity of fixed-circle integrals in an
external parameter and constancy of continuous discrete-valued functions on
real intervals.  No winding-number API is needed.
-/

open Complex Set

namespace HexRootsMathlib

noncomputable section

/-- A fixed-circle integral varies continuously when the integrand restricted
to the parameter-times-circle parametrization is jointly continuous. -/
theorem continuous_circleIntegral {X E : Type*} [TopologicalSpace X]
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : X → ℂ → E}
    (c : ℂ) (R : ℝ)
    (hf : Continuous fun q : X × ℝ => f q.1 (circleMap c R q.2)) :
    Continuous fun x => ∮ z in C(c, R), f x z := by
  simp only [circleIntegral]
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  apply Continuous.smul
  · rw [show (fun q : X × ℝ => deriv (circleMap c R) q.2) =
        fun q => circleMap 0 R q.2 * I by funext q; rw [deriv_circleMap]]
    fun_prop
  · exact hf

/-- A fixed-circle integral of a quotient varies continuously if numerator
and denominator are jointly continuous on the parameterized circle and the
denominator never vanishes there. -/
theorem continuous_circleIntegral_div {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ → ℂ} (c : ℂ) (R : ℝ)
    (hf : Continuous fun q : X × ℝ => f q.1 (circleMap c R q.2))
    (hg : Continuous fun q : X × ℝ => g q.1 (circleMap c R q.2))
    (hzero : ∀ q : X × ℝ, g q.1 (circleMap c R q.2) ≠ 0) :
    Continuous fun x => ∮ z in C(c, R), f x z / g x z := by
  apply continuous_circleIntegral c R
  exact hf.div hg hzero

/-- A fixed-circle integral of a quotient varies continuously on a parameter
set when the data are jointly continuous and the denominator is nonzero only
over that set. -/
theorem continuousOn_circleIntegral_div {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ → ℂ} {s : Set X} (c : ℂ) (R : ℝ)
    (hf : ContinuousOn (fun q : X × ℝ => f q.1 (circleMap c R q.2)) (s ×ˢ univ))
    (hg : ContinuousOn (fun q : X × ℝ => g q.1 (circleMap c R q.2)) (s ×ˢ univ))
    (hzero : ∀ x ∈ s, ∀ θ : ℝ, g x (circleMap c R θ) ≠ 0) :
    ContinuousOn (fun x => ∮ z in C(c, R), f x z / g x z) s := by
  rw [continuousOn_iff_continuous_restrict]
  apply continuous_circleIntegral_div c R
  · simpa only [Function.comp_def] using hf.comp_continuous
      (show Continuous (fun q : s × ℝ => ((q.1 : X), q.2)) by fun_prop)
      (fun q => ⟨q.1.2, mem_univ q.2⟩)
  · simpa only [Function.comp_def] using hg.comp_continuous
      (show Continuous (fun q : s × ℝ => ((q.1 : X), q.2)) by fun_prop)
      (fun q => ⟨q.1.2, mem_univ q.2⟩)
  · exact fun q => hzero q.1.1 q.1.2 q.2

/-- The normalized fixed-circle integral inherits parametric continuity. -/
theorem continuous_normalizedCircleIntegral {X : Type*} [TopologicalSpace X]
    {f : X → ℂ → ℂ} (c : ℂ) (R : ℝ)
    (hf : Continuous fun q : X × ℝ => f q.1 (circleMap c R q.2)) :
    Continuous fun x => (2 * Real.pi * I)⁻¹ * ∮ z in C(c, R), f x z :=
  continuous_const.mul (continuous_circleIntegral c R hf)

/-- The normalized integral of a quotient varies continuously under the same
nonvanishing hypothesis as the unnormalized integral. -/
theorem continuous_normalizedCircleIntegral_div {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ → ℂ} (c : ℂ) (R : ℝ)
    (hf : Continuous fun q : X × ℝ => f q.1 (circleMap c R q.2))
    (hg : Continuous fun q : X × ℝ => g q.1 (circleMap c R q.2))
    (hzero : ∀ q : X × ℝ, g q.1 (circleMap c R q.2) ≠ 0) :
    Continuous fun x => (2 * Real.pi * I)⁻¹ * ∮ z in C(c, R), f x z / g x z :=
  continuous_const.mul (continuous_circleIntegral_div c R hf hg hzero)

/-- The normalized integral of a quotient varies continuously on a parameter
set under a nonvanishing hypothesis restricted to that set. -/
theorem continuousOn_normalizedCircleIntegral_div {X : Type*} [TopologicalSpace X]
    {f g : X → ℂ → ℂ} {s : Set X} (c : ℂ) (R : ℝ)
    (hf : ContinuousOn (fun q : X × ℝ => f q.1 (circleMap c R q.2)) (s ×ˢ univ))
    (hg : ContinuousOn (fun q : X × ℝ => g q.1 (circleMap c R q.2)) (s ×ˢ univ))
    (hzero : ∀ x ∈ s, ∀ θ : ℝ, g x (circleMap c R θ) ≠ 0) :
    ContinuousOn (fun x =>
      (2 * Real.pi * I)⁻¹ * ∮ z in C(c, R), f x z / g x z) s :=
  continuous_const.continuousOn.mul (continuousOn_circleIntegral_div c R hf hg hzero)

/-- Continuity of a real cast detects continuity of a natural-valued map. -/
theorem continuous_nat_of_cast {X : Type*} [TopologicalSpace X] {f : X → ℕ}
    (hf : Continuous fun x => (f x : ℝ)) : Continuous f := by
  exact Nat.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr hf

/-- Continuity of a complex cast detects continuity of a natural-valued map. -/
theorem continuous_nat_of_complexCast {X : Type*} [TopologicalSpace X]
    {f : X → ℕ} (hf : Continuous fun x => (f x : ℂ)) : Continuous f := by
  apply continuous_nat_of_cast
  have hre := Complex.continuous_re.comp hf
  change Continuous (fun x => ((f x : ℂ).re)) at hre
  simpa using hre

/-- Continuity of a real cast detects continuity of an integer-valued map. -/
theorem continuous_int_of_cast {X : Type*} [TopologicalSpace X] {f : X → ℤ}
    (hf : Continuous fun x => (f x : ℝ)) : Continuous f := by
  exact Int.isClosedEmbedding_coe_real.isInducing.continuous_iff.mpr hf

/-- Continuity of a complex cast detects continuity of an integer-valued map. -/
theorem continuous_int_of_complexCast {X : Type*} [TopologicalSpace X]
    {f : X → ℤ} (hf : Continuous fun x => (f x : ℂ)) : Continuous f := by
  apply continuous_int_of_cast
  have hre := Complex.continuous_re.comp hf
  change Continuous (fun x => ((f x : ℂ).re)) at hre
  simpa using hre

/-- Continuity on a set of a real cast detects continuity on that set of a
natural-valued map. -/
theorem continuousOn_nat_of_cast {X : Type*} [TopologicalSpace X] {f : X → ℕ}
    {s : Set X} (hf : ContinuousOn (fun x => (f x : ℝ)) s) : ContinuousOn f s := by
  exact Nat.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.mpr hf

/-- Continuity on a set of a complex cast detects continuity on that set of a
natural-valued map. -/
theorem continuousOn_nat_of_complexCast {X : Type*} [TopologicalSpace X]
    {f : X → ℕ} {s : Set X} (hf : ContinuousOn (fun x => (f x : ℂ)) s) :
    ContinuousOn f s := by
  apply continuousOn_nat_of_cast
  exact Complex.continuous_re.continuousOn.comp hf fun _ _ => mem_univ _

/-- Continuity on a set of a real cast detects continuity on that set of an
integer-valued map. -/
theorem continuousOn_int_of_cast {X : Type*} [TopologicalSpace X] {f : X → ℤ}
    {s : Set X} (hf : ContinuousOn (fun x => (f x : ℝ)) s) : ContinuousOn f s := by
  exact Int.isClosedEmbedding_coe_real.isInducing.continuousOn_iff.mpr hf

/-- Continuity on a set of a complex cast detects continuity on that set of an
integer-valued map. -/
theorem continuousOn_int_of_complexCast {X : Type*} [TopologicalSpace X]
    {f : X → ℤ} {s : Set X} (hf : ContinuousOn (fun x => (f x : ℂ)) s) :
    ContinuousOn f s := by
  apply continuousOn_int_of_cast
  exact Complex.continuous_re.continuousOn.comp hf fun _ _ => mem_univ _

/-- A continuous map from a real interval to a discrete space has equal
values at its endpoints. -/
theorem eq_endpoints_of_continuousOn {Y : Type*} [TopologicalSpace Y]
    [DiscreteTopology Y] {a b : ℝ} (hab : a ≤ b) {f : ℝ → Y}
    (hf : ContinuousOn f (Icc a b)) : f a = f b :=
  (ordConnected_Icc.isPreconnected).constant hf
    (left_mem_Icc.mpr hab) (right_mem_Icc.mpr hab)

/-- A natural-valued map has equal endpoint values when its complex cast is
continuous on the intervening interval. -/
theorem nat_eq_endpoints_of_complexCast {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℕ}
    (hf : ContinuousOn (fun x => (f x : ℂ)) (Icc a b)) : f a = f b :=
  eq_endpoints_of_continuousOn hab (continuousOn_nat_of_complexCast hf)

/-- An integer-valued map has equal endpoint values when its complex cast is
continuous on the intervening interval. -/
theorem int_eq_endpoints_of_complexCast {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℤ}
    (hf : ContinuousOn (fun x => (f x : ℂ)) (Icc a b)) : f a = f b :=
  eq_endpoints_of_continuousOn hab (continuousOn_int_of_complexCast hf)

end

end HexRootsMathlib
