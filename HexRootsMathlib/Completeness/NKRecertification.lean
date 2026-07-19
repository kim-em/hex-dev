/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRootsMathlib.Completeness.NewtonContraction
public import HexRootsMathlib.NKWitness

public section

/-!
# Eventual Newton--Kantorovich recertification

This module transfers the local exact-inverse Newton estimates to the pinned
dyadic reciprocal and exact Taylor quantities consumed by `Hex.nkWitness`.
-/

open Polynomial

namespace HexRootsMathlib.NKData

noncomputable section

/-- Exact-centre inverse applied to one Taylor coefficient, measured in the
sup operator norm. -/
@[expose] noncomputable def exactCoeffNorm (p : ℂ[X]) (k : Nat)
    (x : NewtonKantorovich.ComplexSup) : ℝ :=
  ‖NewtonKantorovich.ComplexSup.mul
    ((p.derivative.eval (NewtonKantorovich.ComplexSup.equiv.symm x))⁻¹ *
      (p.hasseDeriv k).eval (NewtonKantorovich.ComplexSup.equiv.symm x))‖

/-- The exact-coefficient norm varies continuously wherever the polynomial
derivative is nonzero. -/
theorem continuousAt_exactCoeffNorm {p : ℂ[X]} {x : NewtonKantorovich.ComplexSup}
    (hx : p.derivative.eval (NewtonKantorovich.ComplexSup.equiv.symm x) ≠ 0)
    (k : Nat) : ContinuousAt (exactCoeffNorm p k) x := by
  have hderiv : ContinuousAt
      (fun y : NewtonKantorovich.ComplexSup =>
        p.derivative.eval (NewtonKantorovich.ComplexSup.equiv.symm y)) x :=
    (p.derivative.hasDerivAt
      (NewtonKantorovich.ComplexSup.equiv.symm x)).continuousAt.comp
        NewtonKantorovich.ComplexSup.equiv.symm.continuousAt
  have hcoeff : ContinuousAt
      (fun y : NewtonKantorovich.ComplexSup =>
        (p.hasseDeriv k).eval (NewtonKantorovich.ComplexSup.equiv.symm y)) x :=
    ((p.hasseDeriv k).hasDerivAt
      (NewtonKantorovich.ComplexSup.equiv.symm x)).continuousAt.comp
        NewtonKantorovich.ComplexSup.equiv.symm.continuousAt
  exact (NewtonKantorovich.ComplexSup.continuous_mul.continuousAt.comp
    ((hderiv.inv₀ hx).mul hcoeff)).norm

/-- The exact majorant for the executable radial Taylor sum with every
radius power replaced by one. -/
@[expose] noncomputable def tailMajorant (p : Hex.ZPoly)
    (x : NewtonKantorovich.ComplexSup) : ℝ :=
  2 * ∑ k ∈ Finset.range p.size, if 2 ≤ k then
    (k : ℝ) * exactCoeffNorm (toPolyℂ p) k x
  else 0

theorem continuousAt_tailMajorant {p : Hex.ZPoly}
    {x : NewtonKantorovich.ComplexSup}
    (hx : (toPolyℂ p).derivative.eval
      (NewtonKantorovich.ComplexSup.equiv.symm x) ≠ 0) :
    ContinuousAt (tailMajorant p) x := by
  classical
  apply ContinuousAt.const_mul
  induction Finset.range p.size using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ :
      NewtonKantorovich.ComplexSup => (0 : ℝ)) x)
  | insert k S hk ih =>
      have hterm : ContinuousAt (fun x => if 2 ≤ k then
          (k : ℝ) * exactCoeffNorm (toPolyℂ p) k x else 0) x := by
        split_ifs
        · exact continuousAt_const.mul (continuousAt_exactCoeffNorm hx k)
        · exact continuousAt_const
      rw [show (fun x => ∑ i ∈ insert k S, if 2 ≤ i then
          (i : ℝ) * exactCoeffNorm (toPolyℂ p) i x else 0) =
          (fun x => if 2 ≤ k then (k : ℝ) * exactCoeffNorm (toPolyℂ p) k x else 0) +
          (fun x => ∑ i ∈ S, if 2 ≤ i then
            (i : ℝ) * exactCoeffNorm (toPolyℂ p) i x else 0) by
        funext y
        simp [Finset.sum_insert hk]]
      exact hterm.add ih

theorem tailMajorant_nonneg (p : Hex.ZPoly)
    (x : NewtonKantorovich.ComplexSup) : 0 ≤ tailMajorant p x := by
  unfold tailMajorant
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro k hk
  split_ifs
  · unfold exactCoeffNorm
    positivity
  · exact le_rfl

/-- The exact radial majorant is uniformly bounded on some nontrivial
closed neighbourhood of a simple root. -/
theorem exists_tail_bound {p : Hex.ZPoly} {z : ℂ}
    (hsimple : (toPolyℂ p).derivative.eval z ≠ 0) :
    ∃ R : NNReal, 0 < R ∧ ∃ B : ℝ, 0 < B ∧
      ∀ x ∈ Metric.closedBall (NewtonKantorovich.ComplexSup.equiv z) R,
        tailMajorant p x ≤ B := by
  let x₀ := NewtonKantorovich.ComplexSup.equiv z
  have hcont : ContinuousAt (tailMajorant p) x₀ := by
    apply continuousAt_tailMajorant
    simpa [x₀] using hsimple
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hnear⟩ := hcont 1 (by norm_num)
  let R : NNReal := ⟨δ / 2, by positivity⟩
  let B := tailMajorant p x₀ + 1
  have hR : 0 < R := by
    apply NNReal.coe_pos.mp
    change 0 < δ / 2
    positivity
  have hB : 0 < B := by
    dsimp [B]
    nlinarith [tailMajorant_nonneg p x₀]
  refine ⟨R, hR, B, hB, fun x hx => ?_⟩
  have hdist : dist x x₀ < δ := by
    rw [Metric.mem_closedBall] at hx
    change dist x x₀ ≤ δ / 2 at hx
    linarith
  have hclose := hnear hdist
  rw [Real.dist_eq] at hclose
  dsimp [B]
  linarith [le_abs_self (tailMajorant p x - tailMajorant p x₀)]

/-- The pinned reciprocal precision makes the relative floor error strictly
less than `2⁻⁸`, independently of the magnitude of the positive dyadic
input. -/
theorem invFloor_defect {x : Dyadic} (hx : 0 < x) :
    let q : Int := 8 + max 0 (Hex.Dyadic.ceilLog2 x)
    let u := Hex.Dyadic.invFloor x q
    0 ≤ Dyadic.toReal (1 - u * x) ∧
      Dyadic.toReal (1 - u * x) < (2 : ℝ) ^ (-8 : Int) := by
  dsimp only
  let e := max 0 (Hex.Dyadic.ceilLog2 x)
  let q : Int := 8 + e
  have hxR : 0 < Dyadic.toReal x := by
    simpa using (Dyadic.toReal_lt_toReal_iff.mpr hx)
  have hxe : Dyadic.toReal x ≤ (2 : ℝ) ^ e := by
    calc
      Dyadic.toReal x ≤ (2 : ℝ) ^ Hex.Dyadic.ceilLog2 x :=
        Dyadic.toReal_le_two_pow_ceilLog2 x hxR
      _ ≤ (2 : ℝ) ^ e :=
        (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone
          (le_max_right 0 (Hex.Dyadic.ceilLog2 x))
  have hu := Hex.Dyadic.invFloor_eq_invAtPrec_of_pos hx q
  have hlow := Dyadic.invAtPrec_mul_le_one hx q
  have hupp := Dyadic.one_lt_invAtPrec_add_inc_mul hx q
  rw [← hu] at hlow hupp
  have hnonneg : 0 ≤ Dyadic.toReal (1 - Hex.Dyadic.invFloor x q * x) := by
    rw [Dyadic.toReal_sub, Dyadic.toReal_one, Dyadic.toReal_mul]
    apply sub_nonneg.mpr
    simpa only [Dyadic.toReal_mul, Dyadic.toReal_one] using
      (Dyadic.toReal_le_toReal_iff.mpr hlow)
  have hstrict : Dyadic.toReal (1 - Hex.Dyadic.invFloor x q * x) <
      Dyadic.toReal (Dyadic.ofIntWithPrec 1 q) * Dyadic.toReal x := by
    rw [Dyadic.toReal_sub, Dyadic.toReal_one, Dyadic.toReal_mul]
    have huppR := Dyadic.toReal_lt_toReal_iff.mpr hupp
    simp only [Dyadic.toReal_one, Dyadic.toReal_mul, Dyadic.toReal_add] at huppR
    rw [add_mul] at huppR
    linarith
  refine ⟨hnonneg, hstrict.trans_le ?_⟩
  rw [Dyadic.toReal_ofIntWithPrec, Int.cast_one, one_mul]
  calc
    (2 : ℝ) ^ (-q) * Dyadic.toReal x ≤ 2 ^ (-q) * 2 ^ e := by
      gcongr
    _ = (2 : ℝ) ^ (-8 : Int) := by
      rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      dsimp [q]
      ring

/-- The executable first-order defect inherits the uniform `2⁻⁸` bound
from the pinned reciprocal floor. -/
theorem z1_lt (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hnorm : 0 < normSq p s) :
    Dyadic.toReal (z1 p s) < (2 : ℝ) ^ (-8 : Int) := by
  let u := Hex.Dyadic.invFloor (normSq p s) (invPrec p s)
  have hre : (residual p s 1).1 = u * normSq p s := by
    simp only [residual, inverse, u, normSq, c1, Hex.GaussDyadic.mul,
      Hex.GaussDyadic.normSq]
    apply Dyadic.toReal_injective
    simp only [Dyadic.toReal_sub, Dyadic.toReal_add, Dyadic.toReal_mul,
      Dyadic.toReal_neg]
    ring
  have him : (residual p s 1).2 = 0 := by
    simp only [residual, inverse, normSq, c1, Hex.GaussDyadic.mul,
      Hex.GaussDyadic.normSq]
    apply Dyadic.toReal_injective
    simp only [Dyadic.toReal_add, Dyadic.toReal_mul, Dyadic.toReal_neg,
      Dyadic.toReal_zero]
    ring
  have hdef := invFloor_defect hnorm
  change 0 ≤ Dyadic.toReal (1 - u * normSq p s) ∧
      Dyadic.toReal (1 - u * normSq p s) < (2 : ℝ) ^ (-8 : Int) at hdef
  rw [z1, hre, him, Dyadic.toReal_add, Dyadic.toReal_abs,
    Dyadic.toReal_abs, Dyadic.toReal_zero, abs_zero, add_zero,
    abs_of_nonneg hdef.1]
  exact hdef.2

end

end HexRootsMathlib.NKData

open Polynomial

namespace NewtonKantorovich.ComplexSup

noncomputable section

/-- A Newton defect strictly below one forces the derivative at the nearby
centre to remain nonzero. -/
theorem deriv_ne_zero_of_defect {p : ℂ[X]} {z : ℂ}
    (x : ComplexSup) (hdefect : ‖newtonDeriv p z x‖ < 1) :
    p.derivative.eval (equiv.symm x) ≠ 0 := by
  intro hzero
  have hderiv : newtonDeriv p z x = 1 := by
    simp [newtonDeriv, evalDeriv, hzero]
  rw [hderiv, norm_one] at hdefect
  exact lt_irrefl 1 hdefect

/-- If the frozen exact-root Newton derivative has norm at most `1/8` at a
nearby centre, inversion at that centre amplifies the exact-root correction
by at most `8/7`. -/
theorem inverseAt_eval_le {p : ℂ[X]} {z : ℂ} (hsimple : p.derivative.eval z ≠ 0)
    (x : ComplexSup) (hdefect : ‖newtonDeriv p z x‖ ≤ (1 / 8 : ℝ)) :
    ‖inverseAt p (equiv.symm x) (eval p x)‖ ≤
      (8 / 7 : ℝ) * ‖inverseAt p z (eval p x)‖ := by
  have hcenter : p.derivative.eval (equiv.symm x) ≠ 0 :=
    deriv_ne_zero_of_defect x (hdefect.trans_lt (by norm_num))
  let v := inverseAt p (equiv.symm x) (eval p x)
  let y := inverseAt p z (eval p x)
  let D := newtonDeriv p z x
  have hv : v = y + D v := by
    apply equiv.symm.injective
    simp only [map_add, map_sub, v, y, D, inverseAt, newtonDeriv, evalDeriv,
      equiv_symm_mul, sub_apply, one_apply_eq_self,
      ContinuousLinearMap.comp_apply, eval,
      ContinuousLinearEquiv.symm_apply_apply]
    field_simp
    ring
  have hmain : ‖v‖ ≤ ‖y‖ + (1 / 8 : ℝ) * ‖v‖ := calc
    ‖v‖ = ‖y + D v‖ := congrArg norm hv
    _ ≤ ‖y‖ + ‖D v‖ := norm_add_le _ _
    _ ≤ ‖y‖ + (1 / 8 : ℝ) * ‖v‖ := by
      gcongr
      exact (D.le_opNorm v).trans (mul_le_mul_of_nonneg_right hdefect (norm_nonneg v))
  nlinarith [norm_nonneg v, norm_nonneg y]

end

end NewtonKantorovich.ComplexSup

namespace HexRootsMathlib.NKData

noncomputable section

/-- The executable approximate inverse is a scalar in `[0,1]` times the
exact inverse at the executable centre. -/
theorem approxInverse_factor (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hnorm : 0 < normSq p s) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧
      approxInverse p s = θ • NewtonKantorovich.ComplexSup.inverseAt
        (toPolyℂ p) (DyadicSquare.center s) := by
  let u := Hex.Dyadic.invFloor (normSq p s) (invPrec p s)
  let θ := Dyadic.toReal (u * normSq p s)
  let c := GaussDyadic.toComplex (c1 p s)
  have hc : c ≠ 0 := by
    intro hc0
    have hnormR : 0 < Dyadic.toReal (normSq p s) := by
      simpa using (Dyadic.toReal_lt_toReal_iff.mpr hnorm)
    rw [normSq, GaussDyadic.toReal_normSq,
      show GaussDyadic.toComplex (c1 p s) = c from rfl,
      hc0, Complex.normSq_zero] at hnormR
    exact lt_irrefl 0 hnormR
  have hθ : 0 ≤ θ ∧ θ ≤ 1 := by
    have hdef : 0 ≤ 1 - θ ∧ 1 - θ < (2 : ℝ) ^ (-8 : Int) := by
      simpa [u, θ, invPrec, Dyadic.toReal_sub, Dyadic.toReal_mul] using
        (invFloor_defect hnorm)
    constructor
    · have hpow : (2 : ℝ) ^ (-8 : Int) = 1 / 256 := by norm_num
      rw [hpow] at hdef
      nlinarith
    · linarith [hdef.1]
  have hw0 : inverseComplex p s = (Dyadic.toReal u : ℂ) * star c := by
    apply Complex.ext <;>
      simp [inverseComplex, inverse, u, c, GaussDyadic.toComplex,
        Complex.mul_re, Complex.mul_im] <;> ring
  have hθc : (θ : ℂ) = (Dyadic.toReal u : ℂ) * Complex.normSq c := by
    apply Complex.ext <;>
      simp [θ, u, c, normSq, GaussDyadic.toReal_normSq]
  have hw : inverseComplex p s = (θ : ℂ) * c⁻¹ := by
    rw [hw0, hθc, Complex.normSq_eq_conj_mul_self]
    field_simp
    simp
  refine ⟨θ, hθ.1, hθ.2, ?_⟩
  apply ContinuousLinearMap.ext
  intro v₀
  change approxInverse p s v₀ = θ •
    NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p)
      (DyadicSquare.center s) v₀
  apply NewtonKantorovich.ComplexSup.equiv.symm.injective
  rw [map_smul]
  simp only [approxInverse, NewtonKantorovich.ComplexSup.equiv_symm_mul,
    NewtonKantorovich.ComplexSup.inverseAt]
  rw [hw, ← coeff_one]
  simp [c, mul_assoc]

/-- Flooring the reciprocal can only decrease the sup norm of the exact
Newton correction based at the executable centre. -/
theorem norm_approxInverse_le (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hnorm : 0 < normSq p s) (v₀ : NewtonKantorovich.ComplexSup) :
    ‖approxInverse p s v₀‖ ≤
      ‖NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p)
        (DyadicSquare.center s) v₀‖ := by
  obtain ⟨θ, hθ0, hθ1, hfactor⟩ := approxInverse_factor p s hnorm
  have heq : approxInverse p s v₀ = θ •
      NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p)
        (DyadicSquare.center s) v₀ := by
    rw [hfactor]
    rfl
  rw [heq, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0]
  exact mul_le_of_le_one_left
    (norm_nonneg (NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p)
      (DyadicSquare.center s) v₀)) hθ1

theorem norm_exactCoeff (p : Hex.ZPoly) (s : Hex.DyadicSquare) (k : Nat) :
    ‖(NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p)
      (DyadicSquare.center s)).comp
      (NewtonKantorovich.ComplexSup.mul
        (GaussDyadic.toComplex ((coeffs p s).getD k (0, 0))))‖ =
      exactCoeffNorm (toPolyℂ p) k (centerSup s) := by
  have hcoeff := shifted_coeff p s k
  rw [shifted, Polynomial.taylor_coeff] at hcoeff
  unfold exactCoeffNorm NewtonKantorovich.ComplexSup.inverseAt
  simp only [centerSup, ContinuousLinearEquiv.symm_apply_apply]
  rw [NewtonKantorovich.ComplexSup.mul_comp, hcoeff]

/-- Each executable residual-coefficient row norm is bounded by its exact
centre-inverse counterpart. -/
theorem hi_residual_le (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hnorm : 0 < normSq p s) (k : Nat) :
    Dyadic.toReal (Hex.GaussDyadic.hi (residual p s k)) ≤
      exactCoeffNorm (toPolyℂ p) k (centerSup s) := by
  rw [GaussDyadic.toReal_hi,
    ← NewtonKantorovich.ComplexSup.norm_mul]
  obtain ⟨θ, hθ0, hθ1, hfactor⟩ := approxInverse_factor p s hnorm
  have hop : NewtonKantorovich.ComplexSup.mul
      (GaussDyadic.toComplex (residual p s k)) =
      (approxInverse p s).comp (NewtonKantorovich.ComplexSup.mul
        (GaussDyadic.toComplex ((coeffs p s).getD k (0, 0)))) := by
    rw [approxInverse, NewtonKantorovich.ComplexSup.mul_comp,
      inverseComplex, residual, GaussDyadic.toComplex_mul]
  rw [hop, hfactor]
  have hcomp : (θ • NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p)
      (DyadicSquare.center s)).comp (NewtonKantorovich.ComplexSup.mul
        (GaussDyadic.toComplex ((coeffs p s).getD k (0, 0)))) =
      θ • (NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p)
        (DyadicSquare.center s)).comp (NewtonKantorovich.ComplexSup.mul
          (GaussDyadic.toComplex ((coeffs p s).getD k (0, 0)))) := by
    apply ContinuousLinearMap.ext
    intro v
    rfl
  rw [hcomp, norm_smul, Real.norm_eq_abs, abs_of_nonneg hθ0,
    norm_exactCoeff]
  apply mul_le_of_le_one_left _ hθ1
  unfold exactCoeffNorm
  positivity

/-- Once the executable radial upper bound is at most one, `z2` is bounded
by the continuous exact-centre majorant. -/
theorem z2_le_tailMajorant (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hnorm : 0 < normSq p s) (hradius : Dyadic.toReal s.radiusHi ≤ 1) :
    Dyadic.toReal (z2 p s) ≤ tailMajorant p (centerSup s) := by
  rw [z2, Dyadic.toReal_mul, Dyadic.toReal_two, toReal_z2Sum,
    tailMajorant]
  gcongr
  rw [coeffs_size]
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk2 : 2 ≤ k
  · simp only [hk2, ↓reduceIte]
    have hρ0 : 0 ≤ Dyadic.toReal s.radiusHi := by
      rw [DyadicSquare.radiusHi_eq]
      apply mul_nonneg
      · rw [DyadicSquare.halfWidth_eq]
        positivity
      · norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    have hhi0 : 0 ≤ Dyadic.toReal
        (Hex.GaussDyadic.hi (residual p s k)) := by
      rw [GaussDyadic.toReal_hi]
      positivity
    calc
      (k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi (residual p s k)) *
          Dyadic.toReal s.radiusHi ^ (k - 2) ≤
          (k : ℝ) * Dyadic.toReal (Hex.GaussDyadic.hi (residual p s k)) * 1 := by
        gcongr
        exact pow_le_one₀ hρ0 hradius
      _ ≤ (k : ℝ) * exactCoeffNorm (toPolyℂ p) k (centerSup s) := by
        simp only [mul_one]
        gcongr
        exact hi_residual_le p s hnorm k
  · simp [hk2]

/-- A nonzero derivative at the executable centre gives a positive exact
dyadic squared norm. -/
theorem normSq_pos (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hderiv : (toPolyℂ p).derivative.eval (DyadicSquare.center s) ≠ 0) :
    0 < normSq p s := by
  rw [← Dyadic.toReal_lt_toReal_iff]
  simp only [Dyadic.toReal_zero, normSq, GaussDyadic.toReal_normSq, coeff_one]
  exact Complex.normSq_pos.mpr hderiv

/-- The concrete margins used to close the executable witness inequalities.
The first-order defect is supplied automatically by the pinned reciprocal;
the caller supplies the local residual and shrinking `z2 * r` estimates. -/
theorem witness_of_estimates (p : Hex.ZPoly) (s : Hex.DyadicSquare)
    (hsize : 2 ≤ (coeffs p s).size) (hnorm : 0 < normSq p s)
    (hy : Dyadic.toReal (y p s) ≤
      (9 / 14 : ℝ) * DyadicSquare.halfWidth s)
    (hz2 : Dyadic.toReal (z2 p s) * DyadicSquare.halfWidth s < (1 / 8 : ℝ)) :
    Hex.nkWitness p s := by
  rw [witness_iff]
  refine ⟨hsize, hnorm, ?_, ?_⟩
  · rw [← Dyadic.toReal_lt_toReal_iff]
    simp only [Dyadic.toReal_add, Dyadic.toReal_mul, toReal_radius,
      toReal_halfRadiusSq]
    have hz1 := z1_lt p s hnorm
    have hr : 0 < DyadicSquare.halfWidth s := by
      rw [DyadicSquare.halfWidth_eq]
      positivity
    have hz20 := toReal_z2_nonneg p s
    have hz1' : Dyadic.toReal (z1 p s) < 1 / 256 := by
      norm_num at hz1 ⊢
      exact hz1
    nlinarith
  · rw [← Dyadic.toReal_lt_toReal_iff]
    simp only [Dyadic.toReal_add, Dyadic.toReal_mul, toReal_radius,
      Dyadic.toReal_one]
    have hz1 := z1_lt p s hnorm
    norm_num at hz1
    nlinarith

/-- On the local Newton neighbourhood, a square whose root has the doubled
enclosing-square margin certifies as soon as its radial `z2 * r` term is
small. -/
theorem exists_witness_of_z2 {p : Hex.ZPoly} {z : ℂ}
    (hroot : (toPolyℂ p).eval z = 0)
    (hsimple : (toPolyℂ p).derivative.eval z ≠ 0)
    (hsize : 2 ≤ p.size) :
    ∃ R : NNReal, 0 < R ∧ ∀ s : Hex.DyadicSquare,
      centerSup s ∈ Metric.closedBall (NewtonKantorovich.ComplexSup.equiv z) R →
      dist (centerSup s) (NewtonKantorovich.ComplexSup.equiv z) ≤
        DyadicSquare.halfWidth s / 2 →
      Dyadic.toReal (z2 p s) * DyadicSquare.halfWidth s < (1 / 8 : ℝ) →
      Hex.nkWitness p s := by
  obtain ⟨R, hR, hbounds⟩ :=
    NewtonKantorovich.ComplexSup.exists_residual_bounds hroot hsimple
      (K := (1 / 8 : NNReal)) (by norm_num)
  refine ⟨R, hR, fun s hs hmargin hz2small => ?_⟩
  have hdefect := (hbounds (centerSup s) hs).1
  have hcenter : (toPolyℂ p).derivative.eval (DyadicSquare.center s) ≠ 0 := by
    simpa [centerSup] using
      NewtonKantorovich.ComplexSup.deriv_ne_zero_of_defect (centerSup s)
        (hdefect.trans_lt (by norm_num))
  have hnorm := normSq_pos p s hcenter
  apply witness_of_estimates p s (by simpa [coeffs_size] using hsize) hnorm
  · rw [← norm_residual]
    calc
      ‖approxInverse p s
          (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s))‖ ≤
          ‖NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p)
            (DyadicSquare.center s)
            (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s))‖ :=
        norm_approxInverse_le p s hnorm _
      _ ≤ (8 / 7 : ℝ) *
          ‖NewtonKantorovich.ComplexSup.inverseAt (toPolyℂ p) z
            (NewtonKantorovich.ComplexSup.eval (toPolyℂ p) (centerSup s))‖ :=
        NewtonKantorovich.ComplexSup.inverseAt_eval_le hsimple (centerSup s) hdefect
      _ ≤ (8 / 7 : ℝ) * ((1 + (1 / 8 : ℝ)) *
          dist (centerSup s) (NewtonKantorovich.ComplexSup.equiv z)) := by
        gcongr
        exact (hbounds (centerSup s) hs).2
      _ ≤ (9 / 14 : ℝ) * DyadicSquare.halfWidth s := by
        have hdist0 : 0 ≤ dist (centerSup s)
            (NewtonKantorovich.ComplexSup.equiv z) := dist_nonneg
        nlinarith
  · exact hz2small

/-- Every sufficiently small doubled square whose centre is within half a
half-width of a simple root passes the actual executable NK witness. -/
theorem exists_nkWitness_radius {p : Hex.ZPoly} {z : ℂ}
    (hroot : (toPolyℂ p).eval z = 0)
    (hsimple : (toPolyℂ p).derivative.eval z ≠ 0)
    (hsize : 2 ≤ p.size) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : Hex.DyadicSquare,
      dist (centerSup s) (NewtonKantorovich.ComplexSup.equiv z) ≤
        DyadicSquare.halfWidth s / 2 →
      DyadicSquare.halfWidth s < ε → Hex.nkWitness p s := by
  obtain ⟨Rc, hRc, hcert⟩ := exists_witness_of_z2 hroot hsimple hsize
  obtain ⟨Rd, hRd, hbounds⟩ :=
    NewtonKantorovich.ComplexSup.exists_residual_bounds hroot hsimple
      (K := (1 / 8 : NNReal)) (by norm_num)
  obtain ⟨Rt, hRt, B, hB, htail⟩ := exists_tail_bound hsimple
  let ε := min (2 * (Rc : ℝ)) (min (2 * (Rd : ℝ))
    (min (2 * (Rt : ℝ)) (min (1 / 2 : ℝ) (1 / (8 * B)))))
  have hε : 0 < ε := by
    dsimp [ε]
    repeat' apply lt_min <;> positivity
  refine ⟨ε, hε, fun s hmargin hsmall => ?_⟩
  have hparts :
      DyadicSquare.halfWidth s < 2 * (Rc : ℝ) ∧
      DyadicSquare.halfWidth s < 2 * (Rd : ℝ) ∧
      DyadicSquare.halfWidth s < 2 * (Rt : ℝ) ∧
      DyadicSquare.halfWidth s < (1 / 2 : ℝ) ∧
      DyadicSquare.halfWidth s < 1 / (8 * B) := by
    simpa [ε, lt_min_iff] using hsmall
  have hsRc : centerSup s ∈ Metric.closedBall
      (NewtonKantorovich.ComplexSup.equiv z) Rc := by
    rw [Metric.mem_closedBall]
    nlinarith
  have hsRd : centerSup s ∈ Metric.closedBall
      (NewtonKantorovich.ComplexSup.equiv z) Rd := by
    rw [Metric.mem_closedBall]
    nlinarith
  have hsRt : centerSup s ∈ Metric.closedBall
      (NewtonKantorovich.ComplexSup.equiv z) Rt := by
    rw [Metric.mem_closedBall]
    nlinarith
  have hdefect := (hbounds (centerSup s) hsRd).1
  have hcenter : (toPolyℂ p).derivative.eval (DyadicSquare.center s) ≠ 0 := by
    simpa [centerSup] using
      NewtonKantorovich.ComplexSup.deriv_ne_zero_of_defect (centerSup s)
        (hdefect.trans_lt (by norm_num))
  have hnorm := normSq_pos p s hcenter
  have hradius : Dyadic.toReal s.radiusHi ≤ 1 := by
    rw [DyadicSquare.radiusHi_eq]
    have hsqrt : Dyadic.toReal Hex.sqrt2Hi = (1449 / 1024 : ℝ) := by
      norm_num [Hex.sqrt2Hi, Dyadic.toReal_ofIntWithPrec]
    rw [hsqrt]
    nlinarith [show (0 : ℝ) < DyadicSquare.halfWidth s by
      rw [DyadicSquare.halfWidth_eq]; positivity]
  have hz2bound := z2_le_tailMajorant p s hnorm hradius
  have htailbound := htail (centerSup s) hsRt
  have hz2small : Dyadic.toReal (z2 p s) * DyadicSquare.halfWidth s <
      (1 / 8 : ℝ) := by
    have hr0 : 0 ≤ DyadicSquare.halfWidth s := by
      rw [DyadicSquare.halfWidth_eq]
      positivity
    have hz20 := toReal_z2_nonneg p s
    calc
      Dyadic.toReal (z2 p s) * DyadicSquare.halfWidth s ≤
          tailMajorant p (centerSup s) * DyadicSquare.halfWidth s := by
        gcongr
      _ ≤ B * DyadicSquare.halfWidth s := by gcongr
      _ < 1 / 8 := by
        have := hparts.2.2.2.2
        calc
          B * DyadicSquare.halfWidth s < B * (1 / (8 * B)) := by gcongr
          _ = 1 / 8 := by field_simp
  exact hcert s hsRc hmargin hz2small

/-- Precision-threshold form of eventual executable NK recertification.
The half-radius centre hypothesis is exactly the margin obtained by testing
the square concentric with an enclosing square one level coarser. -/
theorem exists_nkWitness_prec {p : Hex.ZPoly} {z : ℂ}
    (hroot : (toPolyℂ p).eval z = 0)
    (hsimple : (toPolyℂ p).derivative.eval z ≠ 0)
    (hsize : 2 ≤ p.size) :
    ∃ N : Nat, ∀ s : Hex.DyadicSquare, (N : Int) ≤ s.prec →
      dist (centerSup s) (NewtonKantorovich.ComplexSup.equiv z) ≤
        DyadicSquare.halfWidth s / 2 →
      Hex.nkWitness p s := by
  obtain ⟨ε, hε, hcert⟩ := exists_nkWitness_radius hroot hsimple hsize
  obtain ⟨N, hN⟩ : ∃ N : Nat, (1 / 2 : ℝ) ^ N < ε :=
    exists_pow_lt_of_lt_one hε (by norm_num)
  refine ⟨N, fun s hprec hmargin => hcert s hmargin ?_⟩
  rw [DyadicSquare.halfWidth_eq]
  calc
    (2 : ℝ) ^ (-s.prec) ≤ (2 : ℝ) ^ (-(N : Int)) :=
      (zpow_right_strictMono₀ (by norm_num : (1 : ℝ) < 2)).monotone
        (neg_le_neg hprec)
    _ = (1 / 2 : ℝ) ^ N := by
      rw [zpow_neg, zpow_natCast]
      simp
    _ < ε := hN

end

end HexRootsMathlib.NKData
