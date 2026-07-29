/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexNumberFieldMathlib.AdjoinRoot

public section

/-!
# Semantics of fixed-field approximation

This module gives executable dyadic balls their ordinary closed-disc meaning
in `ℂ` and states the enclosure and requested-radius contracts for
{name}`Hex.QAdjoin.approx`.
-/

open Metric Set

namespace Hex

namespace RefinedIsolation

/-- The local refinement budget is sufficient to reach every requested
precision for an already certified simple-root atom. -/
theorem refineTo?_isSome {p : ZPoly} (rep : RefinedIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet) :
    (rep.refineTo? target strategy).isSome := by
  sorry

/-- Every successful refined result reaches the requested precision. -/
theorem refineTo?_precision {p : ZPoly} (rep : RefinedIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet)
    {out : {rep' : RefinedIsolation p //
      SimpleRoot.mk rep' = SimpleRoot.mk rep}}
    (h : rep.refineTo? target strategy = some out) :
    target ≤ out.1.1.square.prec := by
  rw [RefinedIsolation.refineTo?] at h
  cases hraw : rep.1.refineTo? (max target (mahlerPrec p : Int)) strategy with
  | none => simp [hraw] at h
  | some iso' =>
      simp only [Option.bind_eq_bind, hraw, Option.bind_some] at h
      split at h
      · rename_i hprec
        split at h
        · have hout := Option.some.inj h
          subst out
          rw [DyadicRootIsolation.refineTo?] at hraw
          exact le_trans (le_max_left _ _)
            (HexRootsMathlib.refineAtom_ready hraw)
        · contradiction
      · contradiction

end RefinedIsolation

namespace DyadicComplexBall

private theorem round_le (q : Rat) (prec : Int) :
    HexRootsMathlib.Dyadic.toReal (q.toDyadic prec) ≤ (q : ℝ) :=
  Rat.cast_le.mpr Rat.toRat_toDyadic_le

private theorem lt_round_add (q : Rat) (prec : Int) :
    (q : ℝ) < HexRootsMathlib.Dyadic.toReal (q.toDyadic prec) +
      (2 : ℝ) ^ (-prec) := by
  have hone :
      (((Dyadic.ofIntWithPrec 1 prec).toRat : Rat) : ℝ) =
        (2 : ℝ) ^ (-prec) := by
    change HexRootsMathlib.Dyadic.toReal
      (Dyadic.ofIntWithPrec 1 prec) = (2 : ℝ) ^ (-prec)
    simp
  unfold HexRootsMathlib.Dyadic.toReal
  rw [← hone]
  have hrat := Rat.lt_toRat_toDyadic_add (x := q) (prec := prec)
  rw [Dyadic.toRat_add] at hrat
  simpa only [Rat.cast_add] using (Rat.cast_lt (K := ℝ)).mpr hrat

private theorem abs_sub_round_lt (q : Rat) (prec : Int) :
    |(q : ℝ) - HexRootsMathlib.Dyadic.toReal (q.toDyadic prec)| <
      (2 : ℝ) ^ (-prec) := by
  rw [abs_of_nonneg (sub_nonneg.mpr (round_le q prec))]
  linarith [lt_round_add q prec]

private theorem round_eq_of_pow2 (q : Rat) (prec : Int) (hprec : 0 ≤ prec)
    (hpow : q.den = 2 ^ q.den.log2) (hle : q.den.log2 ≤ prec.toNat) :
    HexRootsMathlib.Dyadic.toReal (q.toDyadic prec) = (q : ℝ) := by
  cases prec with
  | negSucc n => omega
  | ofNat n =>
      let k := q.den.log2
      have hden : q.den = 2 ^ k := hpow
      have hk : k ≤ n := by simpa [hden, Nat.log2_two_pow] using hle
      have hpown : (2 : Int) ^ n = (2 : Int) ^ (n - k) * (2 : Int) ^ k := by
        rw [← Int.pow_add, Nat.sub_add_cancel hk]
      have hdiv :
          (q.num <<< n) / (q.den : Int) = q.num * (2 : Int) ^ (n - k) := by
        rw [Int.shiftLeft_eq, hden, Int.natCast_pow,
          hpown, ← Int.mul_assoc]
        exact Int.mul_ediv_cancel _ (by positivity)
      rw [Rat.toDyadic, HexRootsMathlib.Dyadic.toReal_ofIntWithPrec,
        hdiv, Rat.cast_def, hden, Nat.cast_pow, Nat.cast_ofNat,
        Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
      change (q.num : ℝ) * (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ (-(n : Int)) =
        (q.num : ℝ) / (2 : ℝ) ^ k
      rw [zpow_neg, zpow_natCast]
      have hpownR : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - k) * (2 : ℝ) ^ k := by
        rw [← pow_add, Nat.sub_add_cancel hk]
      rw [hpownR]
      field_simp

/-- The complex centre represented by a dyadic complex ball. -/
@[expose]
noncomputable def center (b : DyadicComplexBall) : ℂ :=
  HexRootsMathlib.GaussDyadic.toComplex (b.re, b.im)

/-- The real radius represented by a dyadic complex ball. -/
@[expose]
noncomputable def realRadius (b : DyadicComplexBall) : ℝ :=
  HexRootsMathlib.Dyadic.toReal b.radius

/-- The ordinary closed complex disc represented by an executable ball. -/
@[expose]
noncomputable def set (b : DyadicComplexBall) : Set ℂ :=
  closedBall b.center b.realRadius

private theorem invCenter_eq (a : DyadicComplexBall) :
    let norm := GaussDyadic.normSq (a.re, a.im)
    ({ re := ((a.re.toRat / norm.toRat : Rat) : ℝ)
       im := (((-a.im.toRat) / norm.toRat : Rat) : ℝ) } : ℂ) = a.center⁻¹ := by
  dsimp only
  apply Complex.ext
  · rw [Complex.inv_re, center,
      ← HexRootsMathlib.GaussDyadic.toReal_normSq]
    simp only [Rat.cast_div]
    rfl
  · rw [Complex.inv_im, center,
      ← HexRootsMathlib.GaussDyadic.toReal_normSq]
    simp only [Rat.cast_div, Rat.cast_neg]
    rfl

@[simp] private theorem center_add (a b : DyadicComplexBall) :
    (a.add b).center = a.center + b.center := by
  exact HexRootsMathlib.GaussDyadic.toComplex_add
    (a.re, a.im) (b.re, b.im)

@[simp] private theorem realRadius_add (a b : DyadicComplexBall) :
    (a.add b).realRadius = a.realRadius + b.realRadius := by
  exact HexRootsMathlib.Dyadic.toReal_add a.radius b.radius

@[simp] private theorem center_mul (a b : DyadicComplexBall) :
    (a.mul b).center = a.center * b.center := by
  exact HexRootsMathlib.GaussDyadic.toComplex_mul
    (a.re, a.im) (b.re, b.im)

@[simp] private theorem realRadius_mul (a b : DyadicComplexBall) :
    (a.mul b).realRadius =
      HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (a.re, a.im)) * b.realRadius +
        HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (b.re, b.im)) * a.realRadius +
          a.realRadius * b.realRadius := by
  simp [DyadicComplexBall.mul, realRadius]

/-- Minkowski addition encloses sums of enclosed values. -/
theorem add_mem {a b : DyadicComplexBall} {z w : ℂ}
    (hz : z ∈ a.set) (hw : w ∈ b.set) :
    z + w ∈ (a.add b).set := by
  rw [set, mem_closedBall] at hz hw ⊢
  rw [center_add, realRadius_add]
  calc
    dist (z + w) (a.center + b.center) =
        ‖(z - a.center) + (w - b.center)‖ := by
          rw [dist_eq_norm]
          congr 1
          ring
    _ ≤ ‖z - a.center‖ + ‖w - b.center‖ := norm_add_le _ _
    _ = dist z a.center + dist w b.center := by rw [dist_eq_norm, dist_eq_norm]
    _ ≤ a.realRadius + b.realRadius := add_le_add hz hw

/-- A rational coefficient lies in its executable rounded enclosure. -/
theorem ofRat_mem (q : Rat) (prec : Int) :
    (q : ℂ) ∈ (DyadicComplexBall.ofRat q prec).set := by
  unfold DyadicComplexBall.ofRat
  dsimp only
  split
  · rename_i hprec
    split
    · rename_i hexact
      have hpow : q.den = 2 ^ q.den.log2 :=
        (of_decide_eq_true hexact).1
      have hle : q.den.log2 ≤ prec.toNat :=
        (of_decide_eq_true hexact).2
      rw [set, mem_closedBall, dist_eq_norm, center, realRadius]
      simp only [HexRootsMathlib.GaussDyadic.toComplex,
        HexRootsMathlib.Dyadic.toReal_zero]
      change ‖(q : ℂ) -
        (HexRootsMathlib.Dyadic.toReal (q.toDyadic prec) : ℂ)‖ ≤ 0
      rw [← Complex.ofReal_ratCast]
      rw [round_eq_of_pow2 q prec hprec hpow hle]
      simp
    · rename_i hinexact
      rw [set, mem_closedBall, dist_eq_norm, center, realRadius]
      simp only [HexRootsMathlib.GaussDyadic.toComplex,
        HexRootsMathlib.Dyadic.toReal_zero]
      change ‖(q : ℂ) -
        (HexRootsMathlib.Dyadic.toReal (q.toDyadic prec) : ℂ)‖ ≤
          HexRootsMathlib.Dyadic.toReal (Dyadic.ofIntWithPrec 1 prec)
      rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs,
        HexRootsMathlib.Dyadic.toReal_ofIntWithPrec, Int.cast_one, one_mul]
      exact (abs_sub_round_lt q prec).le
  · rename_i hprec
    split
    · rename_i hexact
      have hexact' : (q.toDyadic prec).toRat = q :=
        of_decide_eq_true hexact
      rw [set, mem_closedBall, dist_eq_norm, center, realRadius]
      simp only [HexRootsMathlib.GaussDyadic.toComplex,
        HexRootsMathlib.Dyadic.toReal_zero]
      change ‖(q : ℂ) -
        (HexRootsMathlib.Dyadic.toReal (q.toDyadic prec) : ℂ)‖ ≤ 0
      have hre : HexRootsMathlib.Dyadic.toReal (q.toDyadic prec) = (q : ℝ) := by
        simp [HexRootsMathlib.Dyadic.toReal, hexact']
      rw [hre]
      rw [← Complex.ofReal_ratCast]
      simp
    · rename_i hinexact
      rw [set, mem_closedBall, dist_eq_norm, center, realRadius]
      simp only [HexRootsMathlib.GaussDyadic.toComplex,
        HexRootsMathlib.Dyadic.toReal_zero]
      change ‖(q : ℂ) -
        (HexRootsMathlib.Dyadic.toReal (q.toDyadic prec) : ℂ)‖ ≤
          HexRootsMathlib.Dyadic.toReal (Dyadic.ofIntWithPrec 1 prec)
      rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub,
        Complex.norm_real, Real.norm_eq_abs,
        HexRootsMathlib.Dyadic.toReal_ofIntWithPrec, Int.cast_one, one_mul]
      exact (abs_sub_round_lt q prec).le

private noncomputable def ratPolynomial (coeffs : List Rat) : Polynomial Rat :=
  coeffs.foldr
    (fun c value => Polynomial.C c + Polynomial.X * value) 0

private theorem coeff_ratPolynomial (coeffs : List Rat) (n : Nat) :
    (ratPolynomial coeffs).coeff n = coeffs.getD n 0 := by
  induction coeffs generalizing n with
  | nil => simp [ratPolynomial]
  | cons c coeffs ih =>
      cases n with
      | zero => simp [ratPolynomial]
      | succ n => simpa [ratPolynomial] using ih n

private theorem ratPolynomial_toPolynomial (f : DensePoly Rat) :
    ratPolynomial f.toList = HexPolyMathlib.toPolynomial f := by
  apply Polynomial.ext
  intro n
  rw [coeff_ratPolynomial, HexPolyMathlib.coeff_toPolynomial]
  change f.toArray.toList.getD n 0 = f.coeff n
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList,
    ← Array.getD_eq_getD_getElem?]
  exact DensePoly.toArray_getD f n

private theorem eval_ratPolynomial (coeffs : List Rat) (z : ℂ) :
    (ratPolynomial coeffs).eval₂ (algebraMap Rat ℂ) z =
      coeffs.foldr (fun (c : Rat) value => (c : ℂ) + z * value) 0 := by
  induction coeffs with
  | nil => simp [ratPolynomial]
  | cons c coeffs ih =>
      change
        (Polynomial.C c + Polynomial.X * ratPolynomial coeffs).eval₂
            (algebraMap Rat ℂ) z =
          (c : ℂ) + z *
            coeffs.foldr (fun (c : Rat) value => (c : ℂ) + z * value) 0
      rw [Polynomial.eval₂_add, Polynomial.eval₂_C, Polynomial.eval₂_mul,
        Polynomial.eval₂_X, ih]
      simp

private theorem eval_toPolynomial_horner (f : DensePoly Rat) (z : ℂ) :
    (HexPolyMathlib.toPolynomial f).eval₂ (algebraMap Rat ℂ) z =
      f.toList.foldr (fun (c : Rat) value => (c : ℂ) + z * value) 0 := by
  rw [← ratPolynomial_toPolynomial, eval_ratPolynomial]

/-- Executable ball multiplication encloses products of enclosed values. -/
theorem mul_mem {a b : DyadicComplexBall} {z w : ℂ}
    (hz : z ∈ a.set) (hw : w ∈ b.set) :
    z * w ∈ (a.mul b).set := by
  rw [set, mem_closedBall, dist_eq_norm] at hz hw ⊢
  rw [center_mul, realRadius_mul]
  let ahi := HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (a.re, a.im))
  let bhi := HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (b.re, b.im))
  have hahi : ‖a.center‖ ≤ ahi :=
    HexRootsMathlib.GaussDyadic.norm_le_hi (a.re, a.im)
  have hbhi : ‖b.center‖ ≤ bhi :=
    HexRootsMathlib.GaussDyadic.norm_le_hi (b.re, b.im)
  have hra : 0 ≤ a.realRadius := (norm_nonneg _).trans hz
  have hrb : 0 ≤ b.realRadius := (norm_nonneg _).trans hw
  have hac :
      ‖a.center‖ * ‖w - b.center‖ ≤ ahi * b.realRadius := by
    calc
      ‖a.center‖ * ‖w - b.center‖ ≤ ahi * ‖w - b.center‖ :=
        mul_le_mul_of_nonneg_right hahi (norm_nonneg _)
      _ ≤ ahi * b.realRadius :=
        mul_le_mul_of_nonneg_left hw ((norm_nonneg _).trans hahi)
  have hbc :
      ‖b.center‖ * ‖z - a.center‖ ≤ bhi * a.realRadius := by
    calc
      ‖b.center‖ * ‖z - a.center‖ ≤ bhi * ‖z - a.center‖ :=
        mul_le_mul_of_nonneg_right hbhi (norm_nonneg _)
      _ ≤ bhi * a.realRadius :=
        mul_le_mul_of_nonneg_left hz ((norm_nonneg _).trans hbhi)
  have herr :
      ‖z - a.center‖ * ‖w - b.center‖ ≤ a.realRadius * b.realRadius := by
    calc
      ‖z - a.center‖ * ‖w - b.center‖ ≤
          a.realRadius * ‖w - b.center‖ :=
        mul_le_mul_of_nonneg_right hz (norm_nonneg _)
      _ ≤ a.realRadius * b.realRadius :=
        mul_le_mul_of_nonneg_left hw hra
  calc
    ‖z * w - a.center * b.center‖ =
        ‖a.center * (w - b.center) + b.center * (z - a.center) +
          (z - a.center) * (w - b.center)‖ := by
      congr 1
      ring
    _ ≤ ‖a.center * (w - b.center) + b.center * (z - a.center)‖ +
          ‖(z - a.center) * (w - b.center)‖ := norm_add_le _ _
    _ ≤ (‖a.center * (w - b.center)‖ + ‖b.center * (z - a.center)‖) +
          ‖(z - a.center) * (w - b.center)‖ :=
      add_le_add (norm_add_le _ _) (le_refl _)
    _ = (‖a.center‖ * ‖w - b.center‖ +
          ‖b.center‖ * ‖z - a.center‖) +
          ‖z - a.center‖ * ‖w - b.center‖ := by simp only [norm_mul]
    _ ≤ (ahi * b.realRadius + bhi * a.realRadius) +
          a.realRadius * b.realRadius := add_le_add (add_le_add hac hbc) herr

private theorem horner_mem (coeffs : List Rat) (z : ℂ)
    (zBall initBall : DyadicComplexBall) (coeffPrec : Int) (init : ℂ)
    (hz : z ∈ zBall.set) (hinit : init ∈ initBall.set) :
    coeffs.foldr (fun (c : Rat) value => (c : ℂ) + z * value) init ∈
      (coeffs.foldr
        (fun c value => (DyadicComplexBall.ofRat c coeffPrec).add
          (zBall.mul value)) initBall).set := by
  induction coeffs with
  | nil => exact hinit
  | cons c coeffs ih =>
      exact add_mem (ofRat_mem c coeffPrec) (mul_mem hz ih)

/-- The dyadic ball view of a square contains its true circumscribed closed
disc. -/
theorem mem_toBall {s : DyadicSquare} {z : ℂ}
    (hz : z ∈ HexRootsMathlib.DyadicSquare.closedDisc s) :
    z ∈ s.toBall.set := by
  rw [HexRootsMathlib.DyadicSquare.closedDisc, mem_closedBall] at hz
  rw [set, mem_closedBall, center, realRadius]
  change
    dist z (HexRootsMathlib.DyadicSquare.center s) ≤
      HexRootsMathlib.Dyadic.toReal s.radiusHi
  exact hz.trans (HexRootsMathlib.DyadicSquare.radius_lt_radiusHi s).le

/-- Executable Horner evaluation encloses polynomial evaluation throughout
the supplied root ball. -/
theorem evalRatBall_mem (f : DensePoly Rat) (s : DyadicSquare)
    (coeffPrec : Int) {z : ℂ} (hz : z ∈ s.toBall.set) :
    (HexPolyMathlib.toPolynomial f).eval₂ (algebraMap Rat ℂ) z ∈
      (QAdjoin.evalRatBall f s coeffPrec).set := by
  rw [eval_toPolynomial_horner]
  unfold QAdjoin.evalRatBall
  dsimp only
  cases hback : f.toArray.back? with
  | none =>
      have hempty : f.toArray = #[] :=
        Array.back?_eq_none_iff.mp hback
      have hlist : f.toList = [] := by
        simp [DensePoly.toList, hempty]
      rw [hlist]
      simp [zero, set, center, realRadius]
  | some top =>
      obtain ⟨pre, hprefix⟩ := Array.back?_eq_some_iff.mp hback
      have hlist : f.toList = pre.toList ++ [top] := by
        rw [DensePoly.toList, hprefix, Array.toList_push]
      have hsize : f.toArray.size - 1 = pre.size := by
        rw [hprefix]
        simp
      have hfold :
          f.toArray.foldr
              (fun c value => (DyadicComplexBall.ofRat c coeffPrec).add
                (s.toBall.mul value))
              (DyadicComplexBall.ofRat top coeffPrec)
              (start := f.toArray.size - 1) =
            pre.toList.foldr
              (fun c value => (DyadicComplexBall.ofRat c coeffPrec).add
                (s.toBall.mul value))
              (DyadicComplexBall.ofRat top coeffPrec) := by
        rw [hsize, Array.foldr_eq_foldr_extract]
        rw [hprefix, Array.extract_push_of_le (le_refl pre.size)]
        simp
      rw [hlist, List.foldr_append]
      simp only [List.foldr_cons, List.foldr_nil, mul_zero, add_zero]
      rw [hfold]
      exact horner_mem pre.toList z s.toBall
        (DyadicComplexBall.ofRat top coeffPrec) coeffPrec top hz
        (ofRat_mem top coeffPrec)

private theorem inv_dist {a : DyadicComplexBall} {z : ℂ}
    (hz : z ∈ a.set)
    (hsep : a.radius < GaussDyadic.lo (a.re, a.im)) :
    dist z⁻¹ a.center⁻¹ ≤
      a.realRadius /
        ((HexRootsMathlib.Dyadic.toReal (GaussDyadic.lo (a.re, a.im)) -
            a.realRadius) *
          HexRootsMathlib.Dyadic.toReal (GaussDyadic.lo (a.re, a.im))) := by
  let lower := HexRootsMathlib.Dyadic.toReal (GaussDyadic.lo (a.re, a.im))
  rw [set, mem_closedBall] at hz
  have hzdist := hz
  rw [dist_eq_norm] at hz
  have hrl : a.realRadius < lower :=
    HexRootsMathlib.Dyadic.toReal_lt_toReal_iff.mpr hsep
  have hlc : lower ≤ ‖a.center‖ :=
    HexRootsMathlib.GaussDyadic.lo_le_norm (a.re, a.im)
  have hr : 0 ≤ a.realRadius := (norm_nonneg _).trans hz
  have hl : 0 < lower := lt_of_le_of_lt hr hrl
  have hc : a.center ≠ 0 := by
    exact norm_ne_zero_iff.mp (ne_of_gt (hl.trans_le hlc))
  have hcz : ‖a.center‖ ≤ ‖z - a.center‖ + ‖z‖ := by
    calc
      ‖a.center‖ = ‖-(z - a.center) + z‖ := by
        congr 1
        ring
      _ ≤ ‖-(z - a.center)‖ + ‖z‖ := norm_add_le _ _
      _ = ‖z - a.center‖ + ‖z‖ := by rw [norm_neg]
  have hzl : lower - a.realRadius ≤ ‖z‖ := by linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (sub_pos.mpr hrl) hzl
  have hz0 : z ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hzpos)
  have hsmall :
      (lower - a.realRadius) * lower ≤ ‖z‖ * ‖a.center‖ :=
    mul_le_mul hzl hlc (le_of_lt hl) (norm_nonneg _)
  rw [dist_inv_inv₀ hz0 hc]
  apply (div_le_div_iff₀ (mul_pos hzpos (norm_pos_iff.mpr hc))
    (mul_pos (sub_pos.mpr hrl) hl)).2
  calc
    dist z a.center * ((lower - a.realRadius) * lower) ≤
        a.realRadius * ((lower - a.realRadius) * lower) :=
      mul_le_mul_of_nonneg_right hzdist
        (mul_nonneg (sub_nonneg.mpr hrl.le) hl.le)
    _ ≤ a.realRadius * (‖z‖ * ‖a.center‖) :=
      mul_le_mul_of_nonneg_left hsmall hr

/-- A successful reciprocal ball encloses the reciprocal of every enclosed
value. -/
theorem inv_mem {a b : DyadicComplexBall} {z : ℂ} {prec : Int}
    (hz : z ∈ a.set) (h : a.inv? prec = some b) :
    z⁻¹ ∈ b.set := by
  unfold DyadicComplexBall.inv? at h
  dsimp only at h
  split at h
  · simp only [Option.some.injEq] at h
    subst b
    rename_i hsep
    let norm := GaussDyadic.normSq (a.re, a.im)
    let denom := (GaussDyadic.lo (a.re, a.im) - a.radius) *
      GaussDyadic.lo (a.re, a.im)
    let qre : Rat := a.re.toRat / norm.toRat
    let qim : Rat := (-a.im.toRat) / norm.toRat
    let qdist : Rat := a.radius.toRat / denom.toRat
    let ulp : ℝ := (2 : ℝ) ^ (-prec)
    let out : DyadicComplexBall :=
      { re := qre.toDyadic prec
        im := qim.toDyadic prec
        radius := qdist.toDyadic prec + Dyadic.ofIntWithPrec 1 prec +
          Dyadic.ofIntWithPrec 1 prec + Dyadic.ofIntWithPrec 1 prec }
    change z⁻¹ ∈ out.set
    have hre := abs_sub_round_lt qre prec
    have him := abs_sub_round_lt qim prec
    have hcenter : dist a.center⁻¹ out.center < 2 * ulp := by
      rw [dist_eq_norm]
      calc
        ‖a.center⁻¹ - out.center‖ ≤
            |(a.center⁻¹ - out.center).re| +
              |(a.center⁻¹ - out.center).im| :=
          Complex.norm_le_abs_re_add_abs_im _
        _ = |(qre : ℝ) - HexRootsMathlib.Dyadic.toReal (qre.toDyadic prec)| +
              |(qim : ℝ) - HexRootsMathlib.Dyadic.toReal (qim.toDyadic prec)| := by
          rw [← invCenter_eq a]
          rfl
        _ < ulp + ulp := add_lt_add hre him
        _ = 2 * ulp := by ring
    have hdist : dist z⁻¹ a.center⁻¹ ≤ (qdist : ℝ) := by
      simpa [qdist, denom, realRadius, HexRootsMathlib.Dyadic.toReal,
        Rat.cast_div, Rat.cast_sub, Rat.cast_mul] using inv_dist hz hsep
    have hround :
        (qdist : ℝ) <
          HexRootsMathlib.Dyadic.toReal (qdist.toDyadic prec) + ulp := by
      simpa [ulp] using lt_round_add qdist prec
    rw [set, mem_closedBall]
    apply le_of_lt
    calc
      dist z⁻¹ out.center ≤ dist z⁻¹ a.center⁻¹ + dist a.center⁻¹ out.center :=
        dist_triangle _ _ _
      _ < (qdist : ℝ) + 2 * ulp := add_lt_add_of_le_of_lt hdist hcenter
      _ < (HexRootsMathlib.Dyadic.toReal (qdist.toDyadic prec) + ulp) +
            2 * ulp := by linarith
      _ = out.realRadius := by
        simp [out, ulp, realRadius,
          HexRootsMathlib.Dyadic.toReal_ofIntWithPrec]
        ring
  · contradiction

end DyadicComplexBall

namespace QAdjoin

variable {p : ZPoly} {x : SimpleRoot p}

/-- Fixed-field approximation always encloses the represented complex value. -/
theorem approx_sound (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    toComplex a rep h ∈ (a.approx rep h prec).2.set := by
  unfold approx
  dsimp only
  split
  · rename_i _ out href
    have hroot := HexRootsMathlib.RefinedIsolation.refineTo_root rep
      (prec + (approxGuardBits rep.1.square a.coeffs : Int))
      .nkThenPellet href
    have hroot' :
        HexRootsMathlib.DyadicRootIsolation.root out.1.1 =
          HexRootsMathlib.DyadicRootIsolation.root rep.1 := hroot
    have hout :
        (HexPolyMathlib.toPolynomial a.coeffs).eval₂
            (algebraMap Rat ℂ) out.1.root ∈
          (evalRatBall a.coeffs out.1.1.square
            (prec + (approxGuardBits rep.1.square a.coeffs : Int))).set := by
      apply DyadicComplexBall.evalRatBall_mem
      exact DyadicComplexBall.mem_toBall
        (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc out.1)
    have heval :
        toComplex a rep h =
          (HexPolyMathlib.toPolynomial a.coeffs).eval₂
            (algebraMap Rat ℂ) out.1.root := by
      unfold toComplex
      exact (congrArg
        (fun z => (HexPolyMathlib.toPolynomial a.coeffs).eval₂
          (algebraMap Rat ℂ) z) hroot').symm
    exact heval.symm ▸ hout
  · rw [toComplex]
    apply DyadicComplexBall.evalRatBall_mem
    exact DyadicComplexBall.mem_toBall
      (HexRootsMathlib.RefinedIsolation.root_mem_closedDisc rep)

/-- The guarded approximation achieves the requested dyadic radius. -/
theorem approx_radius (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    (a.approx rep h prec).2.realRadius ≤ (2 : ℝ) ^ (-prec) := by
  sorry

end QAdjoin

end Hex
