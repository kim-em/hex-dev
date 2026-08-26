/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.ArgumentPrinciple
public import HexRootsMathlib.ArgumentTopology

public section

/-!
# Root counts along an affine polynomial homotopy

The affine path from `g` to `f` has constant root count in a fixed disc when
it remains nonzero on the boundary circle for parameters in `[0, 1]`.  The
inequalities used by Rouché's theorem to establish that nonvanishing are kept
out of this module.
-/

open Complex Metric Polynomial Set

namespace HexRootsMathlib

noncomputable section

/-- The affine polynomial path from `g` at `t = 0` to `f` at `t = 1`. -/
def affineHomotopy (f g : ℂ[X]) (t : ℝ) : ℂ[X] :=
  g + C (t : ℂ) * (f - g)

namespace affineHomotopy

@[simp]
theorem zero (f g : ℂ[X]) : affineHomotopy f g 0 = g := by
  simp [affineHomotopy]

@[simp]
theorem one (f g : ℂ[X]) : affineHomotopy f g 1 = f := by
  simp [affineHomotopy]

@[simp]
theorem eval (f g : ℂ[X]) (t : ℝ) (z : ℂ) :
    (affineHomotopy f g t).eval z =
      g.eval z + (t : ℂ) * (f.eval z - g.eval z) := by
  simp [affineHomotopy]

@[simp]
theorem derivative (f g : ℂ[X]) (t : ℝ) :
    (affineHomotopy f g t).derivative =
      affineHomotopy f.derivative g.derivative t := by
  simp [affineHomotopy]

/-- Evaluation of the affine path along a fixed parameterized circle is
jointly continuous in the homotopy parameter and circle parameter. -/
theorem continuous_eval (f g : ℂ[X]) (c : ℂ) (R : ℝ) :
    Continuous fun q : ℝ × ℝ =>
      (affineHomotopy f g q.1).eval (circleMap c R q.2) := by
  rw [show (fun q : ℝ × ℝ =>
      (affineHomotopy f g q.1).eval (circleMap c R q.2)) =
    fun q => g.eval (circleMap c R q.2) + (q.1 : ℂ) *
      (f.eval (circleMap c R q.2) - g.eval (circleMap c R q.2)) by
    funext q
    rw [eval]]
  fun_prop

/-- Derivative evaluation of the affine path along a fixed parameterized
circle is jointly continuous in both parameters. -/
theorem continuous_derivativeEval (f g : ℂ[X]) (c : ℂ) (R : ℝ) :
    Continuous fun q : ℝ × ℝ =>
      (affineHomotopy f g q.1).derivative.eval (circleMap c R q.2) := by
  rw [show (fun q : ℝ × ℝ =>
      (affineHomotopy f g q.1).derivative.eval (circleMap c R q.2)) =
    fun q => g.derivative.eval (circleMap c R q.2) + (q.1 : ℂ) *
      (f.derivative.eval (circleMap c R q.2) -
        g.derivative.eval (circleMap c R q.2)) by
    funext q
    rw [derivative, eval]]
  fun_prop

/-- The root count of a boundary-nonvanishing affine polynomial homotopy is
continuous on its parameter interval. -/
theorem continuous_rootsInDisc {f g : ℂ[X]} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c R,
      (affineHomotopy f g t).eval z ≠ 0) :
    ContinuousOn (fun t => rootsInDisc (affineHomotopy f g t) c R)
      (Icc (0 : ℝ) 1) := by
  have hpoly : ∀ t ∈ Icc (0 : ℝ) 1, affineHomotopy f g t ≠ 0 := by
    intro t ht hp
    have hn := hboundary t ht (circleMap c R 0) (circleMap_mem_sphere c hR 0)
    simp [hp] at hn
  apply continuousOn_nat_of_complexCast
  have hintegral := continuousOn_normalizedCircleIntegral_div
    (f := fun t z => (affineHomotopy f g t).derivative.eval z)
    (g := fun t z => (affineHomotopy f g t).eval z)
    (s := Icc (0 : ℝ) 1) c R
    (continuous_derivativeEval f g c R).continuousOn
    (continuous_eval f g c R).continuousOn
    (fun t ht θ => hboundary t ht (circleMap c R θ) (circleMap_mem_sphere c hR θ))
  apply hintegral.congr
  intro t ht
  exact (argumentPrinciple (hpoly t ht) hR
    (hboundary t ht)).symm

/-- A boundary-nonvanishing affine homotopy has equal root counts at its two
endpoints. -/
theorem rootsInDisc_eq {f g : ℂ[X]} {c : ℂ} {R : ℝ}
    (hR : 0 ≤ R)
    (hboundary : ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ sphere c R,
      (affineHomotopy f g t).eval z ≠ 0) :
    rootsInDisc g c R = rootsInDisc f c R := by
  have h := eq_endpoints_of_continuousOn (a := (0 : ℝ)) (b := 1) (by norm_num)
    (continuous_rootsInDisc hR hboundary)
  simpa using h

end affineHomotopy

end


end HexRootsMathlib
