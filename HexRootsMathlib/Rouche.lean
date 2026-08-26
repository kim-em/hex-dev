/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.RoucheHomotopy

public section

/-!
# Rouché's theorem for complex polynomials on circles

The classical and symmetric norm inequalities exclude zeros of the affine
path on the boundary circle.  Root-count equality then follows from the
homotopy theorem.
-/

open Complex Metric Polynomial Set

namespace HexRootsMathlib

noncomputable section

/-- Classical Rouché theorem for complex polynomials on a circle, with roots
counted with multiplicity in the enclosed open disc. -/
theorem rouche {f g : ℂ[X]} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z ∈ sphere c R, ‖f.eval z - g.eval z‖ < ‖g.eval z‖) :
    rootsInDisc f c R = rootsInDisc g c R := by
  apply (affineHomotopy.rootsInDisc_eq hR ?_).symm
  intro t ht z hz hzero
  rw [affineHomotopy.eval] at hzero
  let d := f.eval z - g.eval z
  change g.eval z + (t : ℂ) * d = 0 at hzero
  have hg : g.eval z = -(t : ℂ) * d := by
    linear_combination hzero
  have hnorm : ‖g.eval z‖ = t * ‖d‖ := by
    rw [hg, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hle : ‖g.eval z‖ ≤ ‖d‖ := by
    rw [hnorm]
    exact mul_le_of_le_one_left (norm_nonneg _) ht.2
  exact (not_le_of_gt (by simpa only [d] using h z hz)) hle

/-- Symmetric Rouché theorem: strictness in the triangle inequality on the
boundary circle is enough to give equal root counts in the disc. -/
theorem rouche_symmetric {f g : ℂ[X]} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ z ∈ sphere c R,
      ‖f.eval z - g.eval z‖ < ‖f.eval z‖ + ‖g.eval z‖) :
    rootsInDisc f c R = rootsInDisc g c R := by
  apply (affineHomotopy.rootsInDisc_eq hR ?_).symm
  intro t ht z hz hzero
  rw [affineHomotopy.eval] at hzero
  let d := f.eval z - g.eval z
  change g.eval z + (t : ℂ) * d = 0 at hzero
  have hg : g.eval z = -(t : ℂ) * d := by
    linear_combination hzero
  have hf : f.eval z = ((1 - t : ℝ) : ℂ) * d := by
    push_cast
    linear_combination hzero
  have hnormg : ‖g.eval z‖ = t * ‖d‖ := by
    rw [hg, norm_mul, norm_neg, norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
  have hnormf : ‖f.eval z‖ = (1 - t) * ‖d‖ := by
    rw [hf, norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  have hsum : ‖d‖ = ‖f.eval z‖ + ‖g.eval z‖ := by
    rw [hnormf, hnormg]
    ring
  have hlt : ‖d‖ < ‖f.eval z‖ + ‖g.eval z‖ := by
    simpa only [d] using h z hz
  rw [← hsum] at hlt
  exact (lt_irrefl _ hlt)

end


end HexRootsMathlib
