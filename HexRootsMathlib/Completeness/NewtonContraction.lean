/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.KantorovichPoly

public section

/-!
# Newton contraction near a simple complex root

This module constructs the frozen-inverse Newton map at a simple root in the
complex sup-norm model and proves its exact first-order identities. The local
contraction neighbourhood is built from these identities below.
-/

open Polynomial

namespace NewtonKantorovich.ComplexSup

noncomputable section

/-- Multiplication by the exact inverse derivative at `z`. -/
@[expose] noncomputable def inverseAt (p : ℂ[X]) (z : ℂ) :
    ComplexSup →L[ℝ] ComplexSup :=
  mul (p.derivative.eval z)⁻¹

/-- The exact inverse derivative is a left inverse to multiplication by the
derivative at a simple root. -/
theorem inverseAt_comp_deriv {p : ℂ[X]} {z : ℂ}
    (hz : p.derivative.eval z ≠ 0) :
    (inverseAt p z).comp (evalDeriv p (equiv z)) = 1 := by
  rw [inverseAt, evalDeriv, ContinuousLinearEquiv.symm_apply_apply, mul_comp,
    inv_mul_cancel₀ hz, mul_one]

/-- Multiplication by a nonzero complex scalar is injective in sup
coordinates. -/
theorem mul_injective {z : ℂ} (hz : z ≠ 0) : Function.Injective (mul z) := by
  intro x y hxy
  apply equiv.symm.injective
  have h := congrArg equiv.symm hxy
  rw [equiv_symm_mul, equiv_symm_mul] at h
  exact mul_left_cancel₀ hz h

/-- The exact inverse derivative operator is injective. -/
theorem inverseAt_injective {p : ℂ[X]} {z : ℂ}
    (hz : p.derivative.eval z ≠ 0) : Function.Injective (inverseAt p z) := by
  apply mul_injective
  exact inv_ne_zero hz

/-- The frozen-inverse Newton map based at `z`. -/
@[expose] noncomputable def newtonAt (p : ℂ[X]) (z : ℂ)
    (x : ComplexSup) : ComplexSup :=
  x - inverseAt p z (eval p x)

/-- The real Fréchet derivative of the frozen-inverse Newton map. -/
@[expose] noncomputable def newtonDeriv (p : ℂ[X]) (z : ℂ)
    (x : ComplexSup) : ComplexSup →L[ℝ] ComplexSup :=
  1 - (inverseAt p z).comp (evalDeriv p x)

/-- The frozen-inverse Newton map has the expected derivative. -/
theorem hasFDerivAt_newtonAt (p : ℂ[X]) (z : ℂ) (x : ComplexSup) :
    HasFDerivAt (newtonAt p z) (newtonDeriv p z x) x := by
  exact (hasFDerivAt_id x).sub
    ((inverseAt p z).hasFDerivAt.comp x (hasFDerivAt_eval p x))

/-- The derivative of the frozen-inverse Newton map is continuous. -/
theorem continuous_newtonDeriv (p : ℂ[X]) (z : ℂ) :
    Continuous (newtonDeriv p z) := by
  have hcomp : Continuous fun x =>
      (inverseAt p z).comp (evalDeriv p x) :=
    ((inverseAt p z).postcomp ComplexSup).continuous.comp
      (continuous_evalDeriv p)
  exact continuous_const.sub hcomp

/-- At a simple root, the Newton-map derivative vanishes exactly. -/
theorem newtonDeriv_at_root {p : ℂ[X]} {z : ℂ}
    (hz : p.derivative.eval z ≠ 0) : newtonDeriv p z (equiv z) = 0 := by
  rw [newtonDeriv, inverseAt_comp_deriv hz]
  simp

/-- A root is a fixed point of its frozen-inverse Newton map. -/
theorem newtonAt_fixed {p : ℂ[X]} {z : ℂ} (hz : p.eval z = 0) :
    newtonAt p z (equiv z) = equiv z := by
  simp [newtonAt, eval, hz]

/-- With a nonzero derivative, the fixed points of the frozen Newton map are
exactly the polynomial roots. -/
theorem newtonAt_fixed_iff {p : ℂ[X]} {z : ℂ}
    (hz : p.derivative.eval z ≠ 0) (x : ComplexSup) :
    newtonAt p z x = x ↔ p.eval (equiv.symm x) = 0 := by
  rw [newtonAt, sub_eq_self]
  rw [map_eq_zero_iff _ (inverseAt_injective hz)]
  simp [eval]

/-- The Newton correction is exactly the displacement from the frozen
Newton image. -/
theorem inverseAt_eval_eq_sub (p : ℂ[X]) (z : ℂ) (x : ComplexSup) :
    inverseAt p z (eval p x) = x - newtonAt p z x := by
  simp [newtonAt]

/-- Near a simple root, both the derivative defect and the Newton residual
have uniform quantitative bounds for any chosen positive defect target.
Item 29 chooses the target against the executable square's centre margin and
combines these bounds with the executable reciprocal and Taylor bounds. -/
theorem exists_residual_bounds {p : ℂ[X]} {z : ℂ}
    (hroot : p.eval z = 0) (hsimple : p.derivative.eval z ≠ 0)
    {K : NNReal} (hK : 0 < K) :
    ∃ r : NNReal, 0 < r ∧ ∀ x ∈ Metric.closedBall (equiv z) r,
      ‖newtonDeriv p z x‖ ≤ (K : ℝ) ∧
      ‖inverseAt p z (eval p x)‖ ≤
        (1 + (K : ℝ)) * dist x (equiv z) := by
  let x₀ := equiv z
  have hcontinuous : ContinuousAt (newtonDeriv p z) x₀ :=
    (continuous_newtonDeriv p z).continuousAt
  rw [Metric.continuousAt_iff] at hcontinuous
  obtain ⟨δ, hδ, hnear⟩ := hcontinuous (K : ℝ) (NNReal.coe_pos.mpr hK)
  let r : NNReal := ⟨δ / 2, by positivity⟩
  have hr : 0 < r := by
    apply NNReal.coe_pos.mp
    dsimp [r]
    exact div_pos hδ (by norm_num)
  have hdefect : ∀ x ∈ Metric.closedBall x₀ r,
      ‖newtonDeriv p z x‖ ≤ (K : ℝ) := by
    intro x hx
    have hdist : dist x x₀ < δ := by
      rw [Metric.mem_closedBall] at hx
      change dist x x₀ ≤ δ / 2 at hx
      linarith
    have hclose := hnear hdist
    have hzero : newtonDeriv p z x₀ = 0 := newtonDeriv_at_root hsimple
    rw [hzero, dist_zero_right] at hclose
    exact hclose.le
  have hF (x : ComplexSup) :
      HasFDerivAt (newtonAt p z) (newtonDeriv p z x) x :=
    hasFDerivAt_newtonAt p z x
  have hlip : LipschitzOnWith K (newtonAt p z)
      (Metric.closedBall x₀ r) :=
    (convex_closedBall x₀ r).lipschitzOnWith_of_nnnorm_fderiv_le
      (𝕜 := ℝ) (fun x _ => (hF x).differentiableAt) (fun x hx => by
        rw [(hF x).fderiv]
        exact_mod_cast hdefect x hx)
  have hx₀ : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le
  have hfixed : newtonAt p z x₀ = x₀ := newtonAt_fixed hroot
  refine ⟨r, hr, fun x hx => ⟨hdefect x hx, ?_⟩⟩
  rw [inverseAt_eval_eq_sub, ← dist_eq_norm]
  calc
    dist x (newtonAt p z x) ≤
        dist x x₀ + dist (newtonAt p z x) x₀ := by
          simpa [dist_comm (newtonAt p z x) x₀] using
            dist_triangle x x₀ (newtonAt p z x)
    _ = dist x x₀ + dist (newtonAt p z x) (newtonAt p z x₀) := by
      rw [hfixed]
    _ ≤ dist x x₀ + (K : ℝ) * dist x x₀ := by
      gcongr
      exact hlip.dist_le_mul x hx x₀ hx₀
    _ = (1 + (K : ℝ)) * dist x x₀ := by ring

/-- Around every simple root, the frozen-inverse Newton map contracts by
`1/2` on some nontrivial closed sup ball, preserves that ball, and has the
given root as its unique fixed point there. -/
theorem exists_contraction {p : ℂ[X]} {z : ℂ}
    (hroot : p.eval z = 0) (hsimple : p.derivative.eval z ≠ 0) :
    ∃ r : NNReal, 0 < r ∧
      ∃ hmap : (Metric.closedBall (equiv z) r).MapsTo (newtonAt p z)
          (Metric.closedBall (equiv z) r),
        ContractingWith (1 / 2 : NNReal)
            (hmap.restrict (newtonAt p z)
              (Metric.closedBall (equiv z) r)
              (Metric.closedBall (equiv z) r)) ∧
          ∀ x ∈ Metric.closedBall (equiv z) r,
            newtonAt p z x = x → x = equiv z := by
  let x₀ := equiv z
  let K : NNReal := 1 / 2
  obtain ⟨r, hr, hbounds⟩ :=
    exists_residual_bounds hroot hsimple (K := K) (by norm_num)
  have hderiv : ∀ x ∈ Metric.closedBall x₀ r,
      ‖newtonDeriv p z x‖₊ ≤ K := by
    intro x hx
    exact_mod_cast (hbounds x hx).1
  have hF (x : ComplexSup) :
      HasFDerivAt (newtonAt p z) (newtonDeriv p z x) x :=
    hasFDerivAt_newtonAt p z x
  have hlip : LipschitzOnWith K (newtonAt p z)
      (Metric.closedBall x₀ r) :=
    (convex_closedBall x₀ r).lipschitzOnWith_of_nnnorm_fderiv_le
      (𝕜 := ℝ) (fun x hx => (hF x).differentiableAt) (fun x hx => by
        rw [(hF x).fderiv]
        exact hderiv x hx)
  have hx₀ : x₀ ∈ Metric.closedBall x₀ r := Metric.mem_closedBall_self hr.le
  have hfixed : newtonAt p z x₀ = x₀ := newtonAt_fixed hroot
  have hmap : (Metric.closedBall x₀ r).MapsTo (newtonAt p z)
      (Metric.closedBall x₀ r) := by
    intro x hx
    rw [Metric.mem_closedBall]
    calc
      dist (newtonAt p z x) x₀ =
          dist (newtonAt p z x) (newtonAt p z x₀) := by rw [hfixed]
      _ ≤ (K : ℝ) * dist x x₀ := hlip.dist_le_mul x hx x₀ hx₀
      _ ≤ (K : ℝ) * r := by
        gcongr
        exact (Metric.mem_closedBall.mp hx)
      _ ≤ r := by
        change (1 / 2 : ℝ) * (r : ℝ) ≤ r
        nlinarith [NNReal.coe_nonneg r]
  have hcontract : ContractingWith K
      (hmap.restrict (newtonAt p z)
        (Metric.closedBall x₀ r) (Metric.closedBall x₀ r)) := by
    apply contractingWith_of_nnnorm_fderiv_le hF hmap (by
      change (1 / 2 : NNReal) < 1
      norm_num)
    exact fun hx => hderiv _ hx
  refine ⟨r, hr, hmap, ?_, ?_⟩
  · exact hcontract
  · intro x hx hxfix
    exact ContractingWith.eq_of_fixedPoints hmap hcontract hx hx₀ hxfix hfixed

end


end NewtonKantorovich.ComplexSup
