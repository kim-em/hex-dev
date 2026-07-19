/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.CircleIntegralLemmas

public section

/-!
# The argument principle for complex polynomials

This module identifies the normalized circle integral of a polynomial's
logarithmic derivative with its number of roots in the enclosed open disc,
counted with multiplicity.
-/

open Complex Metric Polynomial Set

namespace HexRootsMathlib

noncomputable section

/-- Number of roots of `p` in the open disc, counted with multiplicity. -/
noncomputable def rootsInDisc (p : ℂ[X]) (c : ℂ) (R : ℝ) : ℕ := by
  classical
  exact p.roots.countP fun a => a ∈ ball c R

/-- A reciprocal factor whose pole is neither inside nor on a nonnegative-
radius circle has integral zero. -/
theorem integral_subInv_outside_of_not_mem {c a : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (haSphere : a ∉ sphere c R) (haBall : a ∉ ball c R) :
    (∮ z in C(c, R), (z - a)⁻¹) = 0 := by
  apply integral_subInv_outside hR
  intro hclosed
  apply haSphere
  rw [mem_sphere]
  rw [mem_closedBall] at hclosed
  exact le_antisymm hclosed (not_lt.mp (haBall ∘ mem_ball.mpr))

/-- The unnormalized logarithmic-derivative integral is `2πi` times the
number of roots in the open disc, counted with multiplicity. -/
theorem integral_logDeriv_eq_rootCount {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (∮ z in C(c, R), p.derivative.eval z / p.eval z) =
      (rootsInDisc p c R : ℂ) * (2 * Real.pi * I) := by
  classical
  rw [integral_logDeriv_eq_sum hp hR hboundary]
  have hroot : ∀ a ∈ p.roots, a ∉ sphere c R := by
    intro a haRoot haSphere
    exact hboundary a haSphere ((mem_roots hp).mp haRoot)
  have hsum : ∀ roots : Multiset ℂ,
      (∀ a ∈ roots, a ∉ sphere c R) →
      (roots.map fun a => ∮ z in C(c, R), (z - a)⁻¹).sum =
        (roots.countP (fun a => a ∈ ball c R) : ℂ) * (2 * Real.pi * I) := by
    intro roots
    induction roots using Multiset.induction_on with
    | empty => simp
    | @cons a roots ih =>
        intro hnone
        have ha := hnone a (Multiset.mem_cons_self a roots)
        have htail : ∀ b ∈ roots, b ∉ sphere c R :=
          fun b hb => hnone b (Multiset.mem_cons_of_mem hb)
        rw [Multiset.map_cons, Multiset.sum_cons, Multiset.countP_cons, ih htail]
        by_cases hin : a ∈ ball c R
        · rw [if_pos hin, integral_subInv_inside hin]
          push_cast
          ring
        · rw [if_neg hin, integral_subInv_outside_of_not_mem hR ha hin]
          simp
  simpa only [rootsInDisc] using hsum p.roots hroot

/-- Polynomial argument principle on a nonnegative-radius circle: the
normalized logarithmic-derivative integral is the number of roots in the open
disc, counted with multiplicity. The admitted case `R = 0` is degenerate and
both sides vanish. -/
theorem argumentPrinciple {p : ℂ[X]} (hp : p ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hboundary : ∀ z ∈ sphere c R, p.eval z ≠ 0) :
    (2 * Real.pi * I)⁻¹ *
        ∮ z in C(c, R), p.derivative.eval z / p.eval z =
      (rootsInDisc p c R : ℂ) := by
  rw [integral_logDeriv_eq_rootCount hp hR hboundary]
  field_simp [Real.pi_ne_zero]

/-- Under the argument-principle hypotheses, equality of two normalized
logarithmic-derivative integrals is equivalent to equality of their natural
root counts. -/
theorem rootsInDisc_eq_iff {p q : ℂ[X]} (hp : p ≠ 0) (hq : q ≠ 0)
    {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hpBoundary : ∀ z ∈ sphere c R, p.eval z ≠ 0)
    (hqBoundary : ∀ z ∈ sphere c R, q.eval z ≠ 0) :
    rootsInDisc p c R = rootsInDisc q c R ↔
      (2 * Real.pi * I)⁻¹ *
          ∮ z in C(c, R), p.derivative.eval z / p.eval z =
        (2 * Real.pi * I)⁻¹ *
          ∮ z in C(c, R), q.derivative.eval z / q.eval z := by
  rw [argumentPrinciple hp hR hpBoundary, argumentPrinciple hq hR hqBoundary]
  norm_cast

end


end HexRootsMathlib
