/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberField.Roots
public import HexNumberFieldMathlib.Lazy

public section

/-!
# Correctness of root-candidate disambiguation

This module supplies the polynomial lower bound and complex-ball facts used by
the bounded zero test in the fixed-field and tower root drivers.
-/

namespace Hex

namespace QAdjoin

private theorem le_mul_ceilDiv (n d : Nat) (hd : 0 < d) :
    n ≤ ((n + d - 1) / d) * d := by
  by_cases hn : n = 0
  · simp [hn]
  · have hrewrite : n + d - 1 = (n - 1) + d := by omega
    rw [hrewrite, Nat.add_div_right _ hd]
    have hmod := Nat.mod_lt (n - 1) hd
    have hdecomp := Nat.div_add_mod (n - 1) d
    have hpred : n - 1 + 1 = n := Nat.sub_add_cancel (by omega)
    calc
      n = n - 1 + 1 := hpred.symm
      _ = d * ((n - 1) / d) + (n - 1) % d + 1 := by rw [hdecomp]
      _ ≤ d * ((n - 1) / d) + d := by omega
      _ = ((n - 1) / d + 1) * d := by ring

private theorem le_mul_ratAbsCeil (q : Rat) :
    q.num.natAbs ≤ ratAbsCeil q * q.den := by
  unfold ratAbsCeil
  exact le_mul_ceilDiv q.num.natAbs q.den q.den_pos

/-- The executable rational ceiling majorizes the complex norm of the
rational coefficient. -/
theorem norm_rat_le_ratAbsCeil (q : Rat) :
    ‖(q : ℂ)‖ ≤ ratAbsCeil q := by
  rw [show (q : ℂ) = ((q : ℝ) : ℂ) by norm_num,
    Complex.norm_real, Real.norm_eq_abs, Rat.cast_def, abs_div]
  have hdenReal : 0 < (q.den : ℝ) := by positivity
  rw [abs_of_pos hdenReal]
  apply (div_le_iff₀ hdenReal).mpr
  rw [← Int.cast_abs, ← Nat.cast_natAbs]
  exact_mod_cast le_mul_ratAbsCeil q

private theorem evalRat_horner (coefficients : List Rat) (z : ℂ) :
    (coefficients.foldr
      (fun coefficient value =>
        Polynomial.C coefficient + Polynomial.X * value) 0).eval₂
        (algebraMap Rat ℂ) z =
      coefficients.foldr
        (fun coefficient value => (coefficient : ℂ) + z * value) 0 := by
  induction coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      simp only [List.foldr_cons, Polynomial.eval₂_add, Polynomial.eval₂_C,
        Polynomial.eval₂_mul, Polynomial.eval₂_X]
      change (algebraMap Rat ℂ) coefficient + z *
          (coefficients.foldr
            (fun coefficient value =>
              Polynomial.C coefficient + Polynomial.X * value) 0).eval₂
              (algebraMap Rat ℂ) z =
        (coefficient : ℂ) + z * coefficients.foldr
          (fun coefficient value => (coefficient : ℂ) + z * value) 0
      rw [ih]
      rfl

private theorem coeff_rat_horner (coefficients : List Rat) (n : Nat) :
    (coefficients.foldr
      (fun coefficient value =>
        Polynomial.C coefficient + Polynomial.X * value) 0).coeff n =
      coefficients.getD n 0 := by
  induction coefficients generalizing n with
  | nil =>
      simp
  | cons coefficient coefficients ih =>
      cases n with
      | zero => simp
      | succ n => simpa using ih n

private theorem toPolynomial_eq_horner (f : DensePoly Rat) :
    HexPolyMathlib.toPolynomial f =
      f.toList.foldr
        (fun coefficient value =>
          Polynomial.C coefficient + Polynomial.X * value) 0 := by
  ext n
  rw [HexPolyMathlib.coeff_toPolynomial, coeff_rat_horner]
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
    ← Array.getD_eq_getD_getElem?]
  exact (DensePoly.toArray_getD f n).symm

private theorem norm_horner_le (coefficients : List Rat) (z : ℂ) (B : Nat)
    (hz : ‖z‖ ≤ B) :
    ‖coefficients.foldr
        (fun coefficient value => (coefficient : ℂ) + z * value) 0‖ ≤
      (coefficients.foldr
        (fun coefficient value => value * B + ratAbsCeil coefficient) 0 : Nat) := by
  induction coefficients with
  | nil => simp
  | cons coefficient coefficients ih =>
      simp only [List.foldr_cons]
      have hproduct :
          ‖z‖ * ‖coefficients.foldr
              (fun coefficient value => (coefficient : ℂ) + z * value) 0‖ ≤
            (B : ℝ) *
              (coefficients.foldr
                (fun coefficient value =>
                  value * B + ratAbsCeil coefficient) 0 : Nat) := by
        exact mul_le_mul hz ih (norm_nonneg _) (by positivity)
      calc
        ‖(coefficient : ℂ) + z * coefficients.foldr
            (fun coefficient value => (coefficient : ℂ) + z * value) 0‖ ≤
            ‖(coefficient : ℂ)‖ +
              ‖z * coefficients.foldr
                (fun coefficient value => (coefficient : ℂ) + z * value) 0‖ :=
          norm_add_le _ _
        _ = ‖(coefficient : ℂ)‖ + ‖z‖ *
              ‖coefficients.foldr
                (fun coefficient value => (coefficient : ℂ) + z * value) 0‖ := by
          rw [norm_mul]
        _ ≤ (ratAbsCeil coefficient : ℝ) + (B : ℝ) *
              (coefficients.foldr
                (fun coefficient value =>
                  value * B + ratAbsCeil coefficient) 0 : Nat) :=
          add_le_add (norm_rat_le_ratAbsCeil coefficient) hproduct
        _ = ((coefficients.foldr
              (fun coefficient value =>
                value * B + ratAbsCeil coefficient) 0) * B +
              ratAbsCeil coefficient : Nat) := by
          norm_num
          ring

/-- The coordinate majorant bounds the complex norm at the selected field
embedding. -/
theorem norm_toComplex_le_valueMajorant {p : ZPoly} {x : SimpleRoot p}
    (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) :
    ‖toComplex a rep h‖ ≤ valueMajorant a := by
  let B := 2 ^ cauchyExp p + 1
  have hp : HexRootsMathlib.toPolyℂ p ≠ 0 := by
    have hpRaw : p ≠ 0 :=
      HexRootsMathlib.RefinedIsolation.poly_ne_zero rep
    exact HexRootsMathlib.toPolyℂ_ne_zero p fun hsize =>
      hpRaw ((DensePoly.size_eq_zero_iff p).mp hsize)
  have hroot : (HexRootsMathlib.toPolyℂ p).IsRoot rep.root :=
    HexRootsMathlib.RefinedIsolation.isRoot rep
  have hdegree : 0 < p.degree?.getD 0 := by
    rw [← HexRootsMathlib.natDegree_toPolyℂ p,
      Polynomial.natDegree_pos_iff_degree_pos]
    exact Polynomial.degree_pos_of_root hp hroot
  have hz : ‖rep.root‖ ≤ B := by
    calc
      ‖rep.root‖ ≤ (Polynomial.cauchyBound
          (HexRootsMathlib.toPolyℂ p) : ℝ) := by
        exact_mod_cast (hroot.norm_lt_cauchyBound hp).le
      _ ≤ (2 : ℝ) ^ cauchyExp p :=
        HexRootsMathlib.cauchyBound_le_two_pow p hdegree
      _ ≤ (B : ℝ) := by
        dsimp [B]
        norm_num
  rw [toComplex, toPolynomial_eq_horner, evalRat_horner]
  unfold valueMajorant
  rw [← Array.foldr_toList]
  exact norm_horner_le a.coeffs.toList rep.root B hz

end QAdjoin

namespace AlgebraicRoot

/-- The executable Cauchy root bound majorizes the represented complex norm. -/
theorem norm_lt_rootBound (a : AlgebraicRoot) :
    ‖a.toComplex‖ < (2 ^ cauchyExp a.p + 1 : Nat) := by
  have hp : HexRootsMathlib.toPolyℂ a.p ≠ 0 := by
    have hpRaw : a.p ≠ 0 :=
      HexRootsMathlib.RefinedIsolation.poly_ne_zero a.rep
    exact HexRootsMathlib.toPolyℂ_ne_zero a.p fun hsize =>
      hpRaw ((DensePoly.size_eq_zero_iff a.p).mp hsize)
  have hroot : (HexRootsMathlib.toPolyℂ a.p).IsRoot a.toComplex :=
    AlgebraicRoot.toComplex_isRoot a
  calc
    ‖a.toComplex‖ <
        (Polynomial.cauchyBound (HexRootsMathlib.toPolyℂ a.p) : ℝ) := by
      exact_mod_cast hroot.norm_lt_cauchyBound hp
    _ ≤ (2 : ℝ) ^ cauchyExp a.p :=
      HexRootsMathlib.cauchyBound_le_two_pow a.p a.pos_degree
    _ < (2 ^ cauchyExp a.p + 1 : Nat) := by norm_num

end AlgebraicRoot

namespace ZPoly

/-- Normalizing an evaluation eliminant preserves nonzeroness. -/
theorem normalizeEval_ne_zero {q : ZPoly} (hq : q ≠ 0) :
    q.normalizeEval ≠ 0 := by
  unfold normalizeEval
  have hremove : q.removeX ≠ 0 := removeX_ne_zero hq
  exact ne_zero_of_primitive _
    (primitivePart_primitive _ (HexPolyZMathlib.content_ne_zero _ hremove))

/-- Normalizing an evaluation eliminant preserves every nonzero complex root. -/
theorem normalizeEval_isRoot {q : ZPoly} {z : ℂ}
    (hq : q ≠ 0) (hz : z ≠ 0)
    (hroot : (HexRootsMathlib.toPolyℂ q).IsRoot z) :
    (HexRootsMathlib.toPolyℂ q.normalizeEval).IsRoot z := by
  have hremove : q.removeX ≠ 0 := removeX_ne_zero hq
  have hremoveRoot : (HexRootsMathlib.toPolyℂ q.removeX).IsRoot z :=
    removeX_isRoot hz hroot
  have hdecomp :
      HexRootsMathlib.toPolyℂ q.removeX =
        Polynomial.C (q.removeX.content : ℂ) *
          HexRootsMathlib.toPolyℂ q.removeX.primitivePart := by
    change (HexPolyZMathlib.toPolynomial q.removeX).map
        (Int.castRingHom ℂ) =
      Polynomial.C ((Int.castRingHom ℂ) q.removeX.content) *
        (HexPolyZMathlib.toPolynomial q.removeX.primitivePart).map
          (Int.castRingHom ℂ)
    have h := congrArg (Polynomial.map (Int.castRingHom ℂ))
      (HexPolyZMathlib.toPolynomial_eq_C_content_mul_primitivePart q.removeX)
    simpa only [Polynomial.map_mul, Polynomial.map_C] using h
  have hcontent : (q.removeX.content : ℂ) ≠ 0 := by
    exact_mod_cast HexPolyZMathlib.content_ne_zero q.removeX hremove
  change (HexRootsMathlib.toPolyℂ q.removeX.primitivePart).eval z = 0
  change (HexRootsMathlib.toPolyℂ q.removeX).eval z = 0 at hremoveRoot
  rw [hdecomp, Polynomial.eval_mul, Polynomial.eval_C] at hremoveRoot
  exact (mul_eq_zero.mp hremoveRoot).resolve_left hcontent

/-- The normalized evaluation eliminant gives the lower bound used by the
bounded zero test. -/
theorem normalizeEval_root_norm_lower {q : ZPoly} {z : ℂ}
    (hq : q ≠ 0) (hz : z ≠ 0)
    (hroot : (HexRootsMathlib.toPolyℂ q).IsRoot z) :
    (((q.evalLowerDenom : Nat) : ℝ))⁻¹ < ‖z‖ := by
  have hlower := root_norm_lower (normalizeEval_ne_zero hq) hz
    (normalizeEval_isRoot hq hz hroot)
  simpa only [evalLowerDenom, Nat.cast_add, Nat.cast_one, add_comm] using hlower

end ZPoly

namespace DyadicComplexBall

private theorem center_max_nonneg (b : DyadicComplexBall) :
    0 ≤ max |b.center.re| |b.center.im| := by positivity

private theorem center_max_eq (b : DyadicComplexBall) :
    max |b.center.re| |b.center.im| =
      HexRootsMathlib.Dyadic.toReal
        (Hex.Dyadic.max (Hex.Dyadic.abs b.re) (Hex.Dyadic.abs b.im)) := by
  simp [center, HexRootsMathlib.GaussDyadic.toComplex]

private theorem radius_nonneg_of_mem {b : DyadicComplexBall} {z : ℂ}
    (hz : z ∈ b.set) :
    0 ≤ b.realRadius := by
  rw [set, Metric.mem_closedBall] at hz
  exact dist_nonneg.trans hz

private theorem hi_le_two_norm_add_three_halves_radius
    {b : DyadicComplexBall} {z : ℂ} (hz : z ∈ b.set) :
    HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (b.re, b.im)) ≤
      2 * ‖z‖ + (3 / 2 : ℝ) * b.realRadius := by
  have hradius : 0 ≤ b.realRadius := radius_nonneg_of_mem hz
  have hmem : dist z b.center ≤ b.realRadius := by
    simpa only [set, Metric.mem_closedBall] using hz
  have hcenter : ‖b.center‖ ≤ ‖z‖ + b.realRadius := by
    calc
      ‖b.center‖ = ‖(b.center - z) + z‖ := by
        congr 1
        ring
      _ ≤ ‖b.center - z‖ + ‖z‖ := norm_add_le _ _
      _ = dist z b.center + ‖z‖ := by rw [dist_comm, dist_eq_norm]
      _ ≤ b.realRadius + ‖z‖ := add_le_add hmem le_rfl
      _ = ‖z‖ + b.realRadius := add_comm _ _
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  calc
    HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (b.re, b.im)) ≤
        Real.sqrt 2 * ‖b.center‖ := by
      simpa only [center] using
        HexRootsMathlib.GaussDyadic.hi_le_sqrt_two_mul_norm (b.re, b.im)
    _ ≤ (3 / 2 : ℝ) * ‖b.center‖ :=
      mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    _ ≤ (3 / 2 : ℝ) * (‖z‖ + b.realRadius) :=
      mul_le_mul_of_nonneg_left hcenter (by norm_num)
    _ ≤ 2 * ‖z‖ + (3 / 2 : ℝ) * b.realRadius := by
      nlinarith [norm_nonneg z]

private theorem realRadius_horner_le
    {z value coefficient : ℂ}
    (zBall valueBall coefficientBall : DyadicComplexBall)
    (B V E δ : ℝ)
    (hz : z ∈ zBall.set) (hvalue : value ∈ valueBall.set)
    (hcoefficient : coefficient ∈ coefficientBall.set)
    (hzNorm : ‖z‖ ≤ B) (hvalueNorm : ‖value‖ ≤ V)
    (hzRadius : zBall.realRadius ≤ (3 / 4 : ℝ) * δ)
    (hvalueRadius : valueBall.realRadius ≤ E * δ)
    (hcoefficientRadius : coefficientBall.realRadius ≤ δ)
    (hB : 0 ≤ B) (hV : 0 ≤ V) (hE : 0 ≤ E)
    (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (coefficientBall.add (zBall.mul valueBall)).realRadius ≤
      (2 * V + 2 * B * E + 3 * E + 1) * δ := by
  have hzRadius0 : 0 ≤ zBall.realRadius := radius_nonneg_of_mem hz
  have hvalueRadius0 : 0 ≤ valueBall.realRadius :=
    radius_nonneg_of_mem hvalue
  have hcoefficientRadius0 : 0 ≤ coefficientBall.realRadius :=
    radius_nonneg_of_mem hcoefficient
  have hzHi := hi_le_two_norm_add_three_halves_radius hz
  have hvalueHi := hi_le_two_norm_add_three_halves_radius hvalue
  have hzHi' :
      HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (zBall.re, zBall.im)) ≤
        2 * B + (3 / 2 : ℝ) * zBall.realRadius := by
    exact hzHi.trans (add_le_add
      (mul_le_mul_of_nonneg_left hzNorm (by norm_num)) le_rfl)
  have hvalueHi' :
      HexRootsMathlib.Dyadic.toReal
          (GaussDyadic.hi (valueBall.re, valueBall.im)) ≤
        2 * V + (3 / 2 : ℝ) * valueBall.realRadius := by
    exact hvalueHi.trans (add_le_add
      (mul_le_mul_of_nonneg_left hvalueNorm (by norm_num)) le_rfl)
  have hmul :
      (zBall.mul valueBall).realRadius ≤
        2 * B * valueBall.realRadius +
          2 * V * zBall.realRadius +
            4 * zBall.realRadius * valueBall.realRadius := by
    rw [realRadius_mul]
    calc
      HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (zBall.re, zBall.im)) *
            valueBall.realRadius +
          HexRootsMathlib.Dyadic.toReal
              (GaussDyadic.hi (valueBall.re, valueBall.im)) *
            zBall.realRadius +
          zBall.realRadius * valueBall.realRadius ≤
          (2 * B + (3 / 2 : ℝ) * zBall.realRadius) *
              valueBall.realRadius +
            (2 * V + (3 / 2 : ℝ) * valueBall.realRadius) *
              zBall.realRadius +
            zBall.realRadius * valueBall.realRadius := by
        exact add_le_add
          (add_le_add
            (mul_le_mul_of_nonneg_right hzHi' hvalueRadius0)
            (mul_le_mul_of_nonneg_right hvalueHi' hzRadius0))
          le_rfl
      _ = 2 * B * valueBall.realRadius +
          2 * V * zBall.realRadius +
            4 * zBall.realRadius * valueBall.realRadius := by ring
  have hzRadius' : zBall.realRadius ≤ δ := by nlinarith
  have hfirst :
      2 * B * valueBall.realRadius ≤ 2 * B * E * δ := by
    calc
      2 * B * valueBall.realRadius ≤ 2 * B * (E * δ) :=
        mul_le_mul_of_nonneg_left hvalueRadius (by positivity)
      _ = 2 * B * E * δ := by ring
  have hsecond : 2 * V * zBall.realRadius ≤ 2 * V * δ :=
    mul_le_mul_of_nonneg_left hzRadius' (by positivity)
  have hcross0 :
      zBall.realRadius * valueBall.realRadius ≤
        ((3 / 4 : ℝ) * δ) * (E * δ) := by
    exact mul_le_mul hzRadius hvalueRadius hvalueRadius0 (by positivity)
  have hδsq : δ * δ ≤ δ := by
    nlinarith [mul_nonneg hδ (sub_nonneg.mpr hδ1)]
  have hcross :
      4 * zBall.realRadius * valueBall.realRadius ≤ 3 * E * δ := by
    calc
      4 * zBall.realRadius * valueBall.realRadius =
          4 * (zBall.realRadius * valueBall.realRadius) := by ring
      _ ≤ 4 * (((3 / 4 : ℝ) * δ) * (E * δ)) :=
        mul_le_mul_of_nonneg_left hcross0 (by norm_num)
      _ = 3 * E * (δ * δ) := by ring
      _ ≤ 3 * E * δ :=
        mul_le_mul_of_nonneg_left hδsq (by positivity)
  rw [realRadius_add]
  calc
    coefficientBall.realRadius + (zBall.mul valueBall).realRadius ≤
        δ + (2 * B * valueBall.realRadius +
          2 * V * zBall.realRadius +
            4 * zBall.realRadius * valueBall.realRadius) :=
      add_le_add hcoefficientRadius hmul
    _ ≤ δ + (2 * B * E * δ + 2 * V * δ + 3 * E * δ) :=
      add_le_add le_rfl (add_le_add (add_le_add hfirst hsecond) hcross)
    _ = (2 * V + 2 * B * E + 3 * E + 1) * δ := by ring

/-- A ball that passes the executable zero-exclusion test cannot contain zero. -/
theorem excludesZero_sound {b : DyadicComplexBall} {z : ℂ}
    (hz : z ∈ b.set) (hexcludes : b.excludesZero) :
    z ≠ 0 := by
  intro hzero
  subst z
  have hmem : dist 0 b.center ≤ b.realRadius := by
    simpa [set] using hz
  have hnorm : ‖b.center‖ ≤ b.realRadius := by
    simpa [dist_eq_norm, norm_neg] using hmem
  have hmax : max |b.center.re| |b.center.im| ≤ ‖b.center‖ :=
    max_le (Complex.abs_re_le_norm _) (Complex.abs_im_le_norm _)
  have hexcludes' :
      HexRootsMathlib.Dyadic.toReal b.radius <
        HexRootsMathlib.Dyadic.toReal
          (Hex.Dyadic.max (Hex.Dyadic.abs b.re) (Hex.Dyadic.abs b.im)) := by
    rw [HexRootsMathlib.Dyadic.toReal_lt_toReal_iff]
    exact of_decide_eq_true hexcludes
  rw [← center_max_eq, ← realRadius] at hexcludes'
  linarith

/-- A sufficiently small ball containing a value above a reciprocal lower
bound passes the executable zero-exclusion test. -/
theorem excludesZero_of_mem_of_lower {b : DyadicComplexBall} {z : ℂ} {D : Nat}
    (hD : 0 < D) (hz : z ∈ b.set)
    (hlower : (((D : Nat) : ℝ))⁻¹ < ‖z‖)
    (hsmall : 3 * (D : ℝ) * b.realRadius < 1) :
    b.excludesZero := by
  apply decide_eq_true
  rw [← HexRootsMathlib.Dyadic.toReal_lt_toReal_iff,
    ← center_max_eq, ← realRadius]
  by_contra hnot
  have hcenterMax : max |b.center.re| |b.center.im| ≤ b.realRadius :=
    le_of_not_gt hnot
  have hmax0 := center_max_nonneg b
  have hradius0 : 0 ≤ b.realRadius := hmax0.trans hcenterMax
  have hsqrt0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hsqrtSq : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrtLe : Real.sqrt 2 ≤ 2 := by nlinarith
  have hcenter : ‖b.center‖ ≤ 2 * b.realRadius := by
    calc
      ‖b.center‖ ≤ Real.sqrt 2 * max |b.center.re| |b.center.im| :=
        Complex.norm_le_sqrt_two_mul_max _
      _ ≤ Real.sqrt 2 * b.realRadius :=
        mul_le_mul_of_nonneg_left hcenterMax hsqrt0
      _ ≤ 2 * b.realRadius :=
        mul_le_mul_of_nonneg_right hsqrtLe hradius0
  have hmem : dist z b.center ≤ b.realRadius := by
    simpa [set] using hz
  have hnorm : ‖z‖ ≤ 3 * b.realRadius := by
    calc
      ‖z‖ = ‖(z - b.center) + b.center‖ := by ring_nf
      _ ≤ ‖z - b.center‖ + ‖b.center‖ := norm_add_le _ _
      _ = dist z b.center + ‖b.center‖ := by rw [dist_eq_norm]
      _ ≤ b.realRadius + 2 * b.realRadius := add_le_add hmem hcenter
      _ = 3 * b.realRadius := by ring
  have hDreal : 0 < (D : ℝ) := by positivity
  have hsmall' : 3 * b.realRadius < ((D : ℝ))⁻¹ := by
    rw [inv_eq_one_div]
    exact (lt_div_iff₀ hDreal).mpr (by nlinarith)
  linarith

end DyadicComplexBall

namespace QAdjoin.Roots

variable {p : ZPoly} {x : SimpleRoot p}

private theorem hornerBall_bounds [ZPoly.CheckedIrreducible p]
    (coefficients : List (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (z : ℂ) (zBall : DyadicComplexBall)
    (prec : Nat) (rootBound : Nat) (init : ℂ)
    (initBall : DyadicComplexBall) (initState : Nat × Nat)
    (hz : z ∈ zBall.set) (hzNorm : ‖z‖ ≤ rootBound)
    (hzRadius : zBall.realRadius ≤
      (3 / 4 : ℝ) * (2 : ℝ) ^ (-(prec : Int)))
    (hinit : init ∈ initBall.set)
    (hinitNorm : ‖init‖ ≤ initState.1)
    (hinitRadius : initBall.realRadius ≤
      (initState.2 : ℝ) * (2 : ℝ) ^ (-(prec : Int))) :
    let state := coefficients.foldr
      (fun coeff state =>
        (state.1 * rootBound + valueMajorant coeff,
          2 * state.1 + 2 * rootBound * state.2 + 3 * state.2 + 1))
      initState
    let value := coefficients.foldr
      (fun coeff value => toComplex coeff rep h + z * value) init
    let ball := coefficients.foldr
      (fun coeff value =>
        (coeff.approx rep h (prec : Int)).2.add (zBall.mul value))
      initBall
    value ∈ ball.set ∧ ‖value‖ ≤ state.1 ∧
      ball.realRadius ≤
        (state.2 : ℝ) * (2 : ℝ) ^ (-(prec : Int)) := by
  induction coefficients with
  | nil =>
      exact ⟨hinit, hinitNorm, hinitRadius⟩
  | cons coefficient coefficients ih =>
      simp only [List.foldr_cons]
      obtain ⟨hvalue, hvalueNorm, hvalueRadius⟩ := ih
      let state := coefficients.foldr
        (fun coeff state =>
          (state.1 * rootBound + valueMajorant coeff,
            2 * state.1 + 2 * rootBound * state.2 + 3 * state.2 + 1))
        initState
      let value := coefficients.foldr
        (fun coeff value => toComplex coeff rep h + z * value) init
      let ball := coefficients.foldr
        (fun coeff value =>
          (coeff.approx rep h (prec : Int)).2.add (zBall.mul value))
        initBall
      have hcoefficient := QAdjoin.approx_sound coefficient rep h (prec : Int)
      have hcoefficientNorm :=
        QAdjoin.norm_toComplex_le_valueMajorant coefficient rep h
      have hcoefficientRadius :=
        QAdjoin.approx_radius coefficient rep h (prec : Int)
      have hδ : 0 ≤ (2 : ℝ) ^ (-(prec : Int)) := by positivity
      have hδ1 : (2 : ℝ) ^ (-(prec : Int)) ≤ 1 := by
        rw [← zpow_zero (2 : ℝ)]
        exact zpow_le_zpow_right₀ (by norm_num) (by omega)
      have hnorm :
          ‖toComplex coefficient rep h + z * value‖ ≤
            (state.1 * rootBound + valueMajorant coefficient : Nat) := by
        have hproduct : ‖z‖ * ‖value‖ ≤
            (rootBound : ℝ) * (state.1 : ℝ) := by
          exact mul_le_mul hzNorm hvalueNorm (norm_nonneg _) (by positivity)
        calc
          ‖toComplex coefficient rep h + z * value‖ ≤
              ‖toComplex coefficient rep h‖ + ‖z * value‖ :=
            norm_add_le _ _
          _ = ‖toComplex coefficient rep h‖ + ‖z‖ * ‖value‖ := by
            rw [norm_mul]
          _ ≤ (valueMajorant coefficient : ℝ) +
              (rootBound : ℝ) * (state.1 : ℝ) :=
            add_le_add hcoefficientNorm hproduct
          _ = (state.1 * rootBound + valueMajorant coefficient : Nat) := by
            norm_num
            ring
      refine ⟨?_, hnorm, ?_⟩
      · exact DyadicComplexBall.add_mem hcoefficient
          (DyadicComplexBall.mul_mem hz hvalue)
      · have hradius := DyadicComplexBall.realRadius_horner_le
          zBall ball (coefficient.approx rep h (prec : Int)).2
          (rootBound : ℝ) (state.1 : ℝ) (state.2 : ℝ)
          ((2 : ℝ) ^ (-(prec : Int)))
          hz hvalue hcoefficient hzNorm hvalueNorm hzRadius hvalueRadius
          hcoefficientRadius (by positivity) (by positivity) (by positivity)
          hδ hδ1
        simpa only [state, ball, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
          Nat.cast_one] using hradius

end QAdjoin.Roots

namespace QAdjoin.Roots

variable {p : ZPoly} {x : SimpleRoot p}

/-- The certified fixed-field Horner evaluator has the radius promised by its
executable error majorant. -/
theorem evalBall?_radius [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot) (prec : Nat)
    {ball : DyadicComplexBall}
    (hrun : evalBall? f rep h candidate prec = some ball) :
    ball.realRadius ≤ (evalMajorant f candidate.p : ℝ) *
      (2 : ℝ) ^ (-(prec : Int)) := by
  rw [evalBall?] at hrun
  obtain ⟨candidate', hrefine, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  have hroot : candidate'.1.root = candidate.toComplex := by
    calc
      candidate'.1.root = candidate.rep.root :=
        HexRootsMathlib.RefinedIsolation.refineTo_root candidate.rep
          ((prec : Int) + 1) .nkThenPellet hrefine
      _ = candidate.toComplex := by
        unfold AlgebraicRoot.toComplex
        rfl
  have hz : candidate.toComplex ∈ candidate'.1.1.square.toBall.set := by
    rw [← hroot]
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc candidate'.1)
  have hzNorm : ‖candidate.toComplex‖ ≤
      (2 ^ cauchyExp candidate.p + 1 : Nat) :=
    (AlgebraicRoot.norm_lt_rootBound candidate).le
  have hzRadius : candidate'.1.1.square.toBall.realRadius ≤
      (3 / 4 : ℝ) * (2 : ℝ) ^ (-(prec : Int)) := by
    apply DyadicComplexBall.realRadius_toBall_le_three_quarters
    exact RefinedIsolation.refineTo?_precision candidate.rep
      ((prec : Int) + 1) .nkThenPellet hrefine
  cases hback : f.toArray.back? with
  | none =>
      have hball : DyadicComplexBall.zero = ball := by
        apply Option.some.inj
        simpa [hback] using hrun
      subst ball
      simp [DyadicComplexBall.zero, DyadicComplexBall.realRadius]
  | some top =>
      have hball : f.toArray.foldr
          (fun coefficient value =>
            (coefficient.approx rep h (prec : Int)).2.add
              (candidate'.1.1.square.toBall.mul value))
          (top.approx rep h (prec : Int)).2
          (start := f.toArray.size - 1) = ball := by
        apply Option.some.inj
        simpa [hback] using hrun
      subst ball
      obtain ⟨pre, hprefix⟩ := Array.back?_eq_some_iff.mp hback
      have hlist : f.toArray.toList = pre.toList ++ [top] := by
        rw [hprefix, Array.toList_push]
      have hsize : f.toArray.size - 1 = pre.size := by
        rw [hprefix]
        simp
      have hfold :
          f.toArray.foldr
              (fun coefficient value =>
                (coefficient.approx rep h (prec : Int)).2.add
                  (candidate'.1.1.square.toBall.mul value))
              (top.approx rep h (prec : Int)).2
              (start := f.toArray.size - 1) =
            pre.toList.foldr
              (fun coefficient value =>
                (coefficient.approx rep h (prec : Int)).2.add
                  (candidate'.1.1.square.toBall.mul value))
              (top.approx rep h (prec : Int)).2 := by
        rw [hsize, Array.foldr_eq_foldr_extract]
        rw [hprefix, Array.extract_push_of_le (le_refl pre.size)]
        simp
      rw [hfold]
      let rootBound := 2 ^ cauchyExp candidate.p + 1
      let step := fun (coefficient : QAdjoin p x) (state : Nat × Nat) =>
        (state.1 * rootBound + valueMajorant coefficient,
          2 * state.1 + 2 * rootBound * state.2 + 3 * state.2 + 1)
      let state := pre.toList.foldr step (valueMajorant top, 1)
      have hbounds := hornerBall_bounds pre.toList rep h candidate.toComplex
        candidate'.1.1.square.toBall prec rootBound
        (toComplex top rep h) (top.approx rep h (prec : Int)).2
        (valueMajorant top, 1) hz (by simpa only [rootBound] using hzNorm)
        hzRadius (QAdjoin.approx_sound top rep h (prec : Int))
        (QAdjoin.norm_toComplex_le_valueMajorant top rep h)
        (by simpa using QAdjoin.approx_radius top rep h (prec : Int))
      have hradius :
          (pre.toList.foldr
            (fun coefficient value =>
              (coefficient.approx rep h (prec : Int)).2.add
                (candidate'.1.1.square.toBall.mul value))
            (top.approx rep h (prec : Int)).2).realRadius ≤
              (state.2 : ℝ) * (2 : ℝ) ^ (-(prec : Int)) := by
        simpa only [state, step, rootBound] using hbounds.2.2
      have hstate : f.toArray.foldr step (0, 0) = state := by
        rw [← Array.foldr_toList, hlist, List.foldr_append]
        simp [state, step]
      have hmajorant : state.2 ≤ evalMajorant f candidate.p := by
        unfold evalMajorant Disambiguation.evalMajorant
        dsimp only
        rw [hstate]
        exact Nat.le_max_right _ _
      exact hradius.trans (mul_le_mul_of_nonneg_right
        (by exact_mod_cast hmajorant) (by positivity))

end QAdjoin.Roots

/-- The executable radius predicate is its stated real inequality. -/
theorem evalRadiusSmall_real {q : ZPoly} {radius : Dyadic}
    (hsmall : evalRadiusSmall q radius) :
    3 * (q.evalLowerDenom : ℝ) * HexRootsMathlib.Dyadic.toReal radius < 1 := by
  unfold evalRadiusSmall at hsmall
  have hdyadic :
      (((3 * q.evalLowerDenom : Nat) : Dyadic) * radius) < 1 :=
    of_decide_eq_true hsmall
  have hreal := HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mpr hdyadic
  have hcast : HexRootsMathlib.Dyadic.toReal
      ((3 * q.evalLowerDenom : Nat) : Dyadic) =
        ((3 * q.evalLowerDenom : Nat) : ℝ) := by
    change HexRootsMathlib.Dyadic.toReal
      (.ofInt (3 * q.evalLowerDenom : Nat)) = _
    rw [HexRootsMathlib.Dyadic.toReal_ofInt]
    norm_num
  rw [HexRootsMathlib.Dyadic.toReal_mul, hcast,
    HexRootsMathlib.Dyadic.toReal_one] at hreal
  norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hreal
  exact hreal

/-- The real radius inequality implies the executable radius predicate. -/
theorem evalRadiusSmall_of_real {q : ZPoly} {radius : Dyadic}
    (hsmall :
      3 * (q.evalLowerDenom : ℝ) * HexRootsMathlib.Dyadic.toReal radius < 1) :
    evalRadiusSmall q radius := by
  unfold evalRadiusSmall
  apply decide_eq_true
  rw [← HexRootsMathlib.Dyadic.toReal_lt_toReal_iff]
  rw [HexRootsMathlib.Dyadic.toReal_mul,
    HexRootsMathlib.Dyadic.toReal_one]
  have hcast : HexRootsMathlib.Dyadic.toReal
      ((3 * q.evalLowerDenom : Nat) : Dyadic) =
        ((3 * q.evalLowerDenom : Nat) : ℝ) := by
    change HexRootsMathlib.Dyadic.toReal
      (.ofInt (3 * q.evalLowerDenom : Nat)) = _
    rw [HexRootsMathlib.Dyadic.toReal_ofInt]
    norm_num
  rw [hcast]
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  exact hsmall

/-- The prescribed endpoint has enough logarithmic slack: any ball whose
radius is bounded by `max 1 majorant` ulps at that precision satisfies the
zero-test radius predicate. -/
theorem evalDisambiguationLimit_radius_small (q : ZPoly) (majorant : Nat)
    (ball : DyadicComplexBall)
    (hradius : ball.realRadius ≤
      (Nat.max 1 majorant : ℝ) *
        (2 : ℝ) ^ (-(evalDisambiguationLimit q majorant : Int))) :
    evalRadiusSmall q ball.radius := by
  let D := q.evalLowerDenom
  let M := Nat.max 1 majorant
  let C := Hex.ceilLog2 (2 * D * M)
  have hD : 0 < D := by
    dsimp [D]
    unfold ZPoly.evalLowerDenom
    omega
  have hM : 0 < M := by
    dsimp [M]
    exact Nat.zero_lt_one.trans_le (Nat.le_max_left 1 majorant)
  have hlimit : evalDisambiguationLimit q majorant = C + 2 := by
    rfl
  rw [hlimit] at hradius
  have hceilNat : 2 * D * M ≤ 2 ^ C := by
    exact HexRootsMathlib.le_two_pow_ceilLog2 (2 * D * M)
  have hceil : (2 : ℝ) * D * M ≤ (2 : ℝ) ^ C := by
    exact_mod_cast hceilNat
  have hpowPos : 0 < (2 : ℝ) ^ C := by positivity
  have hpowEq :
      (2 : ℝ) ^ (-((C + 2 : Nat) : Int)) =
        ((4 : ℝ) * (2 : ℝ) ^ C)⁻¹ := by
    rw [zpow_neg, zpow_natCast, pow_add]
    norm_num
    ring
  have hscaled :
      3 * (D : ℝ) * (M : ℝ) *
          (2 : ℝ) ^ (-((C + 2 : Nat) : Int)) ≤ 3 / 8 := by
    rw [hpowEq, inv_eq_one_div]
    have hden : 0 < (4 : ℝ) * (2 : ℝ) ^ C := by positivity
    calc
      3 * (D : ℝ) * (M : ℝ) * (1 / ((4 : ℝ) * (2 : ℝ) ^ C)) =
          (3 * (D : ℝ) * (M : ℝ)) / ((4 : ℝ) * (2 : ℝ) ^ C) := by
        rw [div_eq_mul_inv]
        ring
      _ ≤ 3 / 8 := by
        apply (div_le_iff₀ hden).mpr
        nlinarith
  apply evalRadiusSmall_of_real
  have hDreal : 0 ≤ (D : ℝ) := by positivity
  calc
    3 * (q.evalLowerDenom : ℝ) * ball.realRadius ≤
        3 * (D : ℝ) *
          ((M : ℝ) * (2 : ℝ) ^ (-((C + 2 : Nat) : Int))) := by
      dsimp only [D, M] at hradius ⊢
      exact mul_le_mul_of_nonneg_left hradius (by positivity)
    _ = 3 * (D : ℝ) * (M : ℝ) *
          (2 : ℝ) ^ (-((C + 2 : Nat) : Int)) := by ring
    _ ≤ 3 / 8 := hscaled
    _ < 1 := by norm_num

/-- A successful bounded precision search exposes an available ball satisfying
the requested radius predicate. -/
theorem evalDisambiguationPrec_sound {q : ZPoly} {majorant prec : Nat}
    {evalAt : Nat → Option DyadicComplexBall}
    (hrun : evalDisambiguationPrec q majorant evalAt = some prec) :
    ∃ ball, evalAt prec = some ball ∧ evalRadiusSmall q ball.radius := by
  unfold evalDisambiguationPrec at hrun
  obtain ⟨candidate, _hmem, hcandidate⟩ :=
    List.exists_of_findSome?_eq_some hrun
  cases hball : evalAt candidate with
  | none => simp [hball] at hcandidate
  | some ball =>
      by_cases hsmall : evalRadiusSmall q ball.radius
      · have hcand : candidate = prec := by
          simpa [hball, hsmall] using hcandidate
        subst prec
        exact ⟨ball, hball, hsmall⟩
      · simp [hball, hsmall] at hcandidate

/-- The bounded search succeeds whenever its prescribed endpoint produces a
ball satisfying the radius predicate. -/
theorem evalDisambiguationPrec_isSome_of_endpoint (q : ZPoly) (majorant : Nat)
    (evalAt : Nat → Option DyadicComplexBall) {ball : DyadicComplexBall}
    (hball : evalAt (evalDisambiguationLimit q majorant) = some ball)
    (hsmall : evalRadiusSmall q ball.radius) :
    (evalDisambiguationPrec q majorant evalAt).isSome := by
  unfold evalDisambiguationPrec
  rw [List.findSome?_isSome_iff]
  refine ⟨evalDisambiguationLimit q majorant, ?_, ?_⟩
  · simp
  · simp [hball, hsmall]

namespace QAdjoin.Roots

variable {p : ZPoly} {x : SimpleRoot p}

private theorem evalBall_isSome [ZPoly.CheckedIrreducible p]
    (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot) (prec : Nat) :
    (evalBall? f rep h candidate prec).isSome := by
  obtain ⟨candidate', hrefine⟩ := Option.isSome_iff_exists.mp
    (RefinedIsolation.refineTo?_isSome candidate.rep ((prec : Int) + 1))
  rw [evalBall?, hrefine]
  simp only
  cases f.toArray.back? <;> simp

/-- The prescribed bounded precision search succeeds for the fixed-field ball
evaluator. -/
theorem evalPrec_isSome [ZPoly.CheckedIrreducible p]
    (q : ZPoly) (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot) :
    (evalDisambiguationPrec q (evalMajorant f candidate.p)
      (evalBall? f rep h candidate)).isSome := by
  let limit := evalDisambiguationLimit q (evalMajorant f candidate.p)
  obtain ⟨ball, hball⟩ := Option.isSome_iff_exists.mp
    (evalBall_isSome f rep h candidate limit)
  apply evalDisambiguationPrec_isSome_of_endpoint q
    (evalMajorant f candidate.p) (evalBall? f rep h candidate) hball
  apply evalDisambiguationLimit_radius_small q (evalMajorant f candidate.p) ball
  have hmajorant : 1 ≤ evalMajorant f candidate.p := by
    unfold evalMajorant Disambiguation.evalMajorant
    exact Nat.le_max_left _ _
  simpa only [limit, Nat.max_eq_right hmajorant] using
    evalBall?_radius f rep h candidate limit hball

/-- The bounded zero-retention test cannot fail for the fixed-field ball
evaluator. -/
theorem retainZero?_isSome [ZPoly.CheckedIrreducible p]
    (q : ZPoly) (f : DensePoly (QAdjoin p x)) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (candidate : AlgebraicRoot) :
    (retainZero? q (evalMajorant f candidate.p)
      (evalBall? f rep h candidate)).isSome := by
  rw [retainZero?]
  split
  · simp
  · obtain ⟨prec, hprec⟩ := Option.isSome_iff_exists.mp
      (evalPrec_isSome q f rep h candidate)
    rw [hprec]
    obtain ⟨ball, hball⟩ := Option.isSome_iff_exists.mp
      (evalBall_isSome f rep h candidate prec)
    simp [hball]

end QAdjoin.Roots

/-- Conditional correctness of the bounded zero test. Whenever the search
returns, it retains exactly the zero value represented by the eliminant root
and the certified evaluation balls. -/
theorem retainZero?_sound {q : ZPoly} {majorant : Nat}
    {evalAt : Nat → Option DyadicComplexBall} {z : ℂ} {keep : Bool}
    (hq : q ≠ 0) (hroot : (HexRootsMathlib.toPolyℂ q).IsRoot z)
    (hsound : ∀ prec ball, evalAt prec = some ball → z ∈ ball.set)
    (hrun : retainZero? q majorant evalAt = some keep) :
    keep ↔ z = 0 := by
  have hnormalize : q.normalizeEval ≠ 0 := ZPoly.normalizeEval_ne_zero hq
  have hsize : 0 < q.normalizeEval.size := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hnormalize ((DensePoly.size_eq_zero_iff _).mp hzero)
  have hisZero : q.normalizeEval.isZero = false :=
    (DensePoly.isZero_eq_false_iff _).mpr hsize
  rw [retainZero?, hisZero] at hrun
  obtain ⟨prec, hprec, hrun⟩ := Option.bind_eq_some_iff.mp hrun
  obtain ⟨ball, hball, hkeep⟩ := Option.bind_eq_some_iff.mp hrun
  have hkeep' : (!ball.excludesZero) = keep := Option.some.inj hkeep
  obtain ⟨searchBall, hsearchBall, hsmall⟩ :=
    evalDisambiguationPrec_sound hprec
  have hsbeq : searchBall = ball := by
    rw [hball] at hsearchBall
    exact (Option.some.inj hsearchBall).symm
  subst searchBall
  have hzmem : z ∈ ball.set := hsound prec ball hball
  constructor
  · intro hkeepTrue
    by_contra hz
    have hlower := ZPoly.normalizeEval_root_norm_lower hq hz hroot
    have hsmallReal := evalRadiusSmall_real hsmall
    have hexcludes := DyadicComplexBall.excludesZero_of_mem_of_lower
      (show 0 < q.evalLowerDenom by unfold ZPoly.evalLowerDenom; omega)
      hzmem hlower (by simpa [DyadicComplexBall.realRadius] using hsmallReal)
    rw [← hkeep'] at hkeepTrue
    simp [hexcludes] at hkeepTrue
  · intro hz
    subst z
    have hnot : (!ball.excludesZero) = true := by
      cases hexcludes : ball.excludesZero
      · simp
      · exact (DyadicComplexBall.excludesZero_sound hzmem hexcludes rfl).elim
    exact hkeep'.symm.trans hnot

end Hex
