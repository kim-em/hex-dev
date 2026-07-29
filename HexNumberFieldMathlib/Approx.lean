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
precision for an already certified simple-root atom under the default mixed
strategy. -/
theorem refineTo?_isSome {p : ZPoly} (rep : RefinedIsolation p)
    (target : Int) :
    (rep.refineTo? target .nkThenPellet).isSome := by
  exact HexRootsMathlib.RefinedIsolation.refineTo?_isSome_mixed rep target

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
          exact le_trans (le_max_left _ _)
            (HexRootsMathlib.DyadicRootIsolation.refineTo_ready hraw)
        · contradiction
      · contradiction

/-- Refinement never lowers the stored square precision. -/
private theorem refineTo?_monotone {p : ZPoly} (rep : RefinedIsolation p)
    (target : Int) (strategy : AtomStrategy := .nkThenPellet)
    {out : {rep' : RefinedIsolation p //
      SimpleRoot.mk rep' = SimpleRoot.mk rep}}
    (h : rep.refineTo? target strategy = some out) :
    rep.1.square.prec ≤ out.1.1.square.prec := by
  rw [RefinedIsolation.refineTo?] at h
  cases hraw : rep.1.refineTo? (max target (mahlerPrec p : Int)) strategy with
  | none => simp [hraw] at h
  | some iso' =>
      simp only [Option.bind_eq_bind, hraw, Option.bind_some] at h
      split at h
      · split at h
        · have hready : max target (mahlerPrec p : Int) ≤ iso'.square.prec :=
            HexRootsMathlib.DyadicRootIsolation.refineTo_ready hraw
          have hmono : rep.1.square.prec ≤ iso'.square.prec := by
            by_cases htarget :
                max target (mahlerPrec p : Int) ≤ rep.1.square.prec
            · have hiso : rep.1 = iso' := by
                rw [DyadicRootIsolation.refineTo?, if_pos htarget] at hraw
                exact Option.some.inj hraw
              exact hiso ▸ le_rfl
            · exact (le_of_not_ge htarget).trans hready
          have hout := Option.some.inj h
          subst out
          exact hmono
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

/-- Ball addition adds the represented radii. -/
@[simp] theorem realRadius_add (a b : DyadicComplexBall) :
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

/-- A convenient `l∞`-based size bound for a complex ball. -/
private noncomputable def extent (b : DyadicComplexBall) : ℝ :=
  HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (b.re, b.im)) + b.realRadius

private theorem hi_nonneg (b : DyadicComplexBall) :
    0 ≤ HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (b.re, b.im)) := by
  rw [HexRootsMathlib.GaussDyadic.toReal_hi]
  positivity

private theorem hi_add_le (a b : DyadicComplexBall) :
    HexRootsMathlib.Dyadic.toReal
        (GaussDyadic.hi ((a.add b).re, (a.add b).im)) ≤
      HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (a.re, a.im)) +
        HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (b.re, b.im)) := by
  simp only [DyadicComplexBall.add, HexRootsMathlib.GaussDyadic.toReal_hi,
    HexRootsMathlib.GaussDyadic.toComplex,
    HexRootsMathlib.Dyadic.toReal_add]
  calc
    |HexRootsMathlib.Dyadic.toReal a.re +
        HexRootsMathlib.Dyadic.toReal b.re| +
      |HexRootsMathlib.Dyadic.toReal a.im +
        HexRootsMathlib.Dyadic.toReal b.im| ≤
        (|HexRootsMathlib.Dyadic.toReal a.re| +
          |HexRootsMathlib.Dyadic.toReal b.re|) +
        (|HexRootsMathlib.Dyadic.toReal a.im| +
          |HexRootsMathlib.Dyadic.toReal b.im|) :=
      add_le_add (abs_add_le _ _) (abs_add_le _ _)
    _ = (|HexRootsMathlib.Dyadic.toReal a.re| +
          |HexRootsMathlib.Dyadic.toReal a.im|) +
        (|HexRootsMathlib.Dyadic.toReal b.re| +
          |HexRootsMathlib.Dyadic.toReal b.im|) := by ring

private theorem hi_mul_le (a b : DyadicComplexBall) :
    HexRootsMathlib.Dyadic.toReal
        (GaussDyadic.hi ((a.mul b).re, (a.mul b).im)) ≤
      HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (a.re, a.im)) *
        HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi (b.re, b.im)) := by
  simp only [DyadicComplexBall.mul, HexRootsMathlib.GaussDyadic.toReal_hi,
    Hex.GaussDyadic.mul, HexRootsMathlib.GaussDyadic.toComplex,
    HexRootsMathlib.Dyadic.toReal_sub,
    HexRootsMathlib.Dyadic.toReal_add,
    HexRootsMathlib.Dyadic.toReal_mul]
  calc
    |HexRootsMathlib.Dyadic.toReal a.re *
        HexRootsMathlib.Dyadic.toReal b.re -
      HexRootsMathlib.Dyadic.toReal a.im *
        HexRootsMathlib.Dyadic.toReal b.im| +
    |HexRootsMathlib.Dyadic.toReal a.re *
        HexRootsMathlib.Dyadic.toReal b.im +
      HexRootsMathlib.Dyadic.toReal a.im *
        HexRootsMathlib.Dyadic.toReal b.re| ≤
      (|HexRootsMathlib.Dyadic.toReal a.re *
          HexRootsMathlib.Dyadic.toReal b.re| +
        |HexRootsMathlib.Dyadic.toReal a.im *
          HexRootsMathlib.Dyadic.toReal b.im|) +
      (|HexRootsMathlib.Dyadic.toReal a.re *
          HexRootsMathlib.Dyadic.toReal b.im| +
        |HexRootsMathlib.Dyadic.toReal a.im *
          HexRootsMathlib.Dyadic.toReal b.re|) :=
      add_le_add (abs_sub _ _) (abs_add_le _ _)
    _ = (|HexRootsMathlib.Dyadic.toReal a.re| +
          |HexRootsMathlib.Dyadic.toReal a.im|) *
        (|HexRootsMathlib.Dyadic.toReal b.re| +
          |HexRootsMathlib.Dyadic.toReal b.im|) := by
      simp only [abs_mul]
      ring

private theorem extent_add_le (a b : DyadicComplexBall) :
    extent (a.add b) ≤ extent a + extent b := by
  rw [extent, extent, extent, realRadius_add]
  linarith [hi_add_le a b]

private theorem extent_mul_le (a b : DyadicComplexBall) :
    extent (a.mul b) ≤ extent a * extent b := by
  rw [extent, extent, extent, realRadius_mul]
  have hha := hi_nonneg a
  have hhb := hi_nonneg b
  nlinarith [hi_mul_le a b]

private theorem realRadius_mul_le (a b : DyadicComplexBall)
    (hra : 0 ≤ a.realRadius) (hrb : 0 ≤ b.realRadius) :
    (a.mul b).realRadius ≤
      extent a * b.realRadius + extent b * a.realRadius := by
  rw [realRadius_mul, extent, extent]
  nlinarith

private theorem extent_toBall_le (s : DyadicSquare) :
    extent s.toBall ≤ (2 : ℝ) ^ QAdjoin.rootBits s := by
  let w := GaussDyadic.hi s.center + s.radiusHi
  have hw : 0 < HexRootsMathlib.Dyadic.toReal w := by
    change 0 < HexRootsMathlib.Dyadic.toReal
      (GaussDyadic.hi s.center + s.radiusHi)
    rw [HexRootsMathlib.Dyadic.toReal_add]
    exact add_pos_of_nonneg_of_pos (by
      simpa [DyadicSquare.toBall, DyadicSquare.center] using hi_nonneg s.toBall) (by
      rw [HexRootsMathlib.DyadicSquare.radiusHi_eq]
      exact mul_pos (by
        rw [HexRootsMathlib.DyadicSquare.halfWidth_eq]
        positivity) (by
        norm_num [Hex.sqrt2Hi,
          HexRootsMathlib.Dyadic.toReal_ofIntWithPrec]))
  have hceil := HexRootsMathlib.Dyadic.toReal_le_two_pow_ceilLog2 w hw
  have hnonneg : 0 ≤ max 0 (Hex.Dyadic.ceilLog2 w) := le_max_left _ _
  have hpow :
      (2 : ℝ) ^ Hex.Dyadic.ceilLog2 w ≤
        (2 : ℝ) ^ max 0 (Hex.Dyadic.ceilLog2 w) :=
    zpow_le_zpow_right₀ (by norm_num) (le_max_right _ _)
  have hcast :
      ((max 0 (Hex.Dyadic.ceilLog2 w)).toNat : Int) =
        max 0 (Hex.Dyadic.ceilLog2 w) := by
    exact Int.toNat_of_nonneg hnonneg
  calc
    extent s.toBall = HexRootsMathlib.Dyadic.toReal w := by
      simp [extent, w, DyadicSquare.toBall, DyadicSquare.center, realRadius]
    _ ≤ (2 : ℝ) ^ Hex.Dyadic.ceilLog2 w := hceil
    _ ≤ (2 : ℝ) ^ max 0 (Hex.Dyadic.ceilLog2 w) := hpow
    _ = (2 : ℝ) ^ QAdjoin.rootBits s := by
      rw [← hcast, zpow_natCast]
      rfl

private theorem radiusHi_le_of_prec {s t : DyadicSquare}
    (hprec : s.prec ≤ t.prec) :
    HexRootsMathlib.Dyadic.toReal t.radiusHi ≤
      HexRootsMathlib.Dyadic.toReal s.radiusHi := by
  rw [HexRootsMathlib.DyadicSquare.radiusHi_eq,
    HexRootsMathlib.DyadicSquare.radiusHi_eq]
  apply mul_le_mul_of_nonneg_right _ (by
    norm_num [Hex.sqrt2Hi, HexRootsMathlib.Dyadic.toReal_ofIntWithPrec])
  rw [HexRootsMathlib.DyadicSquare.halfWidth_eq,
    HexRootsMathlib.DyadicSquare.halfWidth_eq]
  exact zpow_le_zpow_right₀ (by norm_num) (by omega)

private theorem radiusHi_pos (s : DyadicSquare) :
    0 < HexRootsMathlib.Dyadic.toReal s.radiusHi := by
  rw [HexRootsMathlib.DyadicSquare.radiusHi_eq]
  exact mul_pos (by
    rw [HexRootsMathlib.DyadicSquare.halfWidth_eq]
    positivity) (by
    norm_num [Hex.sqrt2Hi, HexRootsMathlib.Dyadic.toReal_ofIntWithPrec])

private theorem realRadius_toBall_nonneg (s : DyadicSquare) :
    0 ≤ s.toBall.realRadius := by
  simpa [DyadicSquare.toBall, realRadius] using (radiusHi_pos s).le

/-- A square refined to `prec` has a dyadic-ball radius bounded by two ulps at
that precision. -/
theorem realRadius_toBall_le {s : DyadicSquare} {prec : Int}
    (hprec : prec ≤ s.prec) :
    s.toBall.realRadius ≤ 2 * (2 : ℝ) ^ (-prec) := by
  have hpow : (2 : ℝ) ^ (-s.prec) ≤ (2 : ℝ) ^ (-prec) :=
    zpow_le_zpow_right₀ (by norm_num) (by omega)
  rw [DyadicSquare.toBall, realRadius,
    HexRootsMathlib.DyadicSquare.radiusHi_eq,
    HexRootsMathlib.DyadicSquare.halfWidth_eq]
  have hsqrt : HexRootsMathlib.Dyadic.toReal sqrt2Hi ≤ (2 : ℝ) := by
    norm_num [Hex.sqrt2Hi, HexRootsMathlib.Dyadic.toReal_ofIntWithPrec]
  calc
    (2 : ℝ) ^ (-s.prec) * HexRootsMathlib.Dyadic.toReal sqrt2Hi ≤
        (2 : ℝ) ^ (-s.prec) * 2 :=
      mul_le_mul_of_nonneg_left hsqrt (zpow_nonneg (by norm_num) _)
    _ ≤ (2 : ℝ) ^ (-prec) * 2 :=
      mul_le_mul_of_nonneg_right hpow (by norm_num)
    _ = 2 * (2 : ℝ) ^ (-prec) := by ring

private theorem refined_extent_le {p : ZPoly} (rep : RefinedIsolation p)
    (target : Int) (strategy : AtomStrategy)
    {out : {rep' : RefinedIsolation p //
      SimpleRoot.mk rep' = SimpleRoot.mk rep}}
    (hrun : rep.refineTo? target strategy = some out) :
    extent out.1.1.square.toBall ≤ 4 * extent rep.1.square.toBall := by
  let s := rep.1.square
  let t := out.1.1.square
  let cs := HexRootsMathlib.DyadicSquare.center s
  let ct := HexRootsMathlib.DyadicSquare.center t
  let hs := HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi s.center)
  let ht := HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi t.center)
  let rs := HexRootsMathlib.Dyadic.toReal s.radiusHi
  let rt := HexRootsMathlib.Dyadic.toReal t.radiusHi
  have hprec : s.prec ≤ t.prec :=
    RefinedIsolation.refineTo?_monotone rep target strategy hrun
  have hrt : rt ≤ rs := radiusHi_le_of_prec hprec
  have hrs0 : 0 ≤ rs := by
    change 0 ≤ HexRootsMathlib.Dyadic.toReal s.radiusHi
    exact (radiusHi_pos s).le
  have hrt0 : 0 ≤ rt := by
    change 0 ≤ HexRootsMathlib.Dyadic.toReal t.radiusHi
    exact (radiusHi_pos t).le
  have hroot := HexRootsMathlib.RefinedIsolation.refineTo_root rep
    target strategy hrun
  have hmems := HexRootsMathlib.RefinedIsolation.root_mem_closedDisc rep
  have hmemt := HexRootsMathlib.RefinedIsolation.root_mem_closedDisc out.1
  have hcenters : dist ct cs ≤ rs + rt := by
    rw [HexRootsMathlib.DyadicSquare.closedDisc, mem_closedBall] at hmems hmemt
    calc
      dist ct cs ≤
          dist ct (HexRootsMathlib.RefinedIsolation.root out.1) +
            dist (HexRootsMathlib.RefinedIsolation.root out.1) cs :=
        dist_triangle _ _ _
      _ = dist (HexRootsMathlib.RefinedIsolation.root out.1) ct +
          dist (HexRootsMathlib.RefinedIsolation.root rep) cs := by
        rw [dist_comm ct, hroot]
      _ ≤ HexRootsMathlib.DyadicSquare.radius t +
          HexRootsMathlib.DyadicSquare.radius s := add_le_add hmemt hmems
      _ ≤ rt + rs := add_le_add
        (HexRootsMathlib.DyadicSquare.radius_lt_radiusHi t).le
        (HexRootsMathlib.DyadicSquare.radius_lt_radiusHi s).le
      _ = rs + rt := add_comm _ _
  have hadd :
      HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi t.center) ≤
        HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi s.center) +
          HexRootsMathlib.Dyadic.toReal
            (GaussDyadic.hi (GaussDyadic.sub t.center s.center)) := by
    let a : DyadicComplexBall := ⟨s.re, s.im, 0⟩
    let d : DyadicComplexBall :=
      ⟨t.re - s.re, t.im - s.im, 0⟩
    have h := hi_add_le a d
    simpa [a, d, DyadicComplexBall.add, DyadicSquare.center] using h
  have hdiff :
      HexRootsMathlib.Dyadic.toReal
          (GaussDyadic.hi (GaussDyadic.sub t.center s.center)) ≤
        √2 * dist ct cs := by
    calc
      HexRootsMathlib.Dyadic.toReal
          (GaussDyadic.hi (GaussDyadic.sub t.center s.center)) ≤
          √2 * ‖HexRootsMathlib.GaussDyadic.toComplex
            (GaussDyadic.sub t.center s.center)‖ :=
        HexRootsMathlib.GaussDyadic.hi_le_sqrt_two_mul_norm _
      _ = √2 * dist ct cs := by
        rw [HexRootsMathlib.GaussDyadic.toComplex_sub, Complex.dist_eq]
        rfl
  have hhi : ht ≤ hs + √2 * (rs + rt) := by
    calc
      ht ≤ hs + HexRootsMathlib.Dyadic.toReal
          (GaussDyadic.hi (GaussDyadic.sub t.center s.center)) := hadd
      _ ≤ hs + √2 * dist ct cs := by
        simpa [add_comm] using add_le_add_left hdiff hs
      _ ≤ hs + √2 * (rs + rt) := by
        gcongr
  have hhs0 : 0 ≤ hs := by dsimp [hs]; exact hi_nonneg s.toBall
  have hsqrt : √(2 : ℝ) ≤ 3 / 2 := by
    have hs0 : 0 ≤ √(2 : ℝ) := Real.sqrt_nonneg _
    have hsq : √(2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    nlinarith
  change ht + rt ≤ 4 * (hs + rs)
  nlinarith

private theorem realRadius_ofRat_le (q : Rat) (prec : Int) :
    (DyadicComplexBall.ofRat q prec).realRadius ≤ (2 : ℝ) ^ (-prec) := by
  unfold DyadicComplexBall.ofRat
  dsimp only
  split <;> split <;>
    simp [realRadius, HexRootsMathlib.Dyadic.toReal_ofIntWithPrec] <;> positivity

private theorem realRadius_ofRat_nonneg (q : Rat) (prec : Int) :
    0 ≤ (DyadicComplexBall.ofRat q prec).realRadius := by
  unfold DyadicComplexBall.ofRat
  dsimp only
  split <;> split <;>
    simp [realRadius, HexRootsMathlib.Dyadic.toReal_ofIntWithPrec] <;> positivity

private theorem extent_ofRat_le (q : Rat) (prec : Int) :
    extent (DyadicComplexBall.ofRat q prec) ≤
      |(q : ℝ)| + 2 * (2 : ℝ) ^ (-prec) := by
  have hround :
      |HexRootsMathlib.Dyadic.toReal (q.toDyadic prec)| ≤
        |(q : ℝ)| + (2 : ℝ) ^ (-prec) := by
    calc
      |HexRootsMathlib.Dyadic.toReal (q.toDyadic prec)| =
          |(q : ℝ) - ((q : ℝ) -
            HexRootsMathlib.Dyadic.toReal (q.toDyadic prec))| := by ring_nf
      _ ≤ |(q : ℝ)| +
          |(q : ℝ) - HexRootsMathlib.Dyadic.toReal (q.toDyadic prec)| :=
        abs_sub _ _
      _ ≤ |(q : ℝ)| + (2 : ℝ) ^ (-prec) :=
        by simpa only [add_comm] using
          add_le_add_left (abs_sub_round_lt q prec).le |(q : ℝ)|
  have hhi :
      HexRootsMathlib.Dyadic.toReal (GaussDyadic.hi
          ((DyadicComplexBall.ofRat q prec).re,
            (DyadicComplexBall.ofRat q prec).im)) =
        |HexRootsMathlib.Dyadic.toReal (q.toDyadic prec)| := by
    simp [DyadicComplexBall.ofRat, HexRootsMathlib.GaussDyadic.toReal_hi,
      HexRootsMathlib.GaussDyadic.toComplex]
  rw [extent, hhi]
  linarith [realRadius_ofRat_le q prec]

private theorem abs_ratCast_le_numAbs (q : Rat) :
    |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := by
  have hnum : |(q.num : ℝ)| = (q.num.natAbs : ℝ) := by
    rw [← Int.cast_abs]
    exact (Nat.cast_natAbs (α := ℝ) q.num).symm
  rw [Rat.cast_def, abs_div, hnum, abs_of_pos (by positivity : (0 : ℝ) < q.den)]
  exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast q.den_pos)

private theorem coeff_le_twoPow {f : DensePoly Rat} {q : Rat}
    (hq : q ∈ f.toList) :
    |(q : ℝ)| ≤ (2 : ℝ) ^ QAdjoin.coeffBits f := by
  have hbits : Hex.ceilLog2 (q.num.natAbs + 1) ≤ QAdjoin.coeffBits f := by
    rw [QAdjoin.coeffBits, ← Array.foldl_toList]
    exact List.le_foldl_max_of_mem f.toList
      (fun r => Hex.ceilLog2 (r.num.natAbs + 1)) hq
  have hnat : q.num.natAbs + 1 ≤ 2 ^ QAdjoin.coeffBits f := by
    exact (HexRootsMathlib.le_two_pow_ceilLog2 _).trans
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hbits)
  calc
    |(q : ℝ)| ≤ (q.num.natAbs : ℝ) := abs_ratCast_le_numAbs q
    _ ≤ (q.num.natAbs + 1 : Nat) := by norm_num
    _ ≤ (2 ^ QAdjoin.coeffBits f : Nat) := by exact_mod_cast hnat
    _ = (2 : ℝ) ^ QAdjoin.coeffBits f := by norm_num

private theorem horner_bounds (coeffs : List Rat)
    (zBall initBall : DyadicComplexBall) (coeffPrec : Int) (A K : ℝ)
    (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hz0 : 0 ≤ zBall.realRadius) (hzK : extent zBall ≤ K)
    (hzUlp : zBall.realRadius ≤ 2 * (2 : ℝ) ^ (-coeffPrec))
    (hinit0 : 0 ≤ initBall.realRadius)
    (hinitExtent : extent initBall ≤ A + 2 * (2 : ℝ) ^ (-coeffPrec))
    (hinitRadius : initBall.realRadius ≤ (2 : ℝ) ^ (-coeffPrec))
    (hcoeff : ∀ q ∈ coeffs, |(q : ℝ)| ≤ A) :
    let out := coeffs.foldr
      (fun q value => (DyadicComplexBall.ofRat q coeffPrec).add
        (zBall.mul value)) initBall
    0 ≤ out.realRadius ∧
      extent out ≤
        (A + 2 * (2 : ℝ) ^ (-coeffPrec)) * (coeffs.length + 1) *
          K ^ coeffs.length ∧
      out.realRadius ≤
        (2 : ℝ) ^ (-coeffPrec) * 16 * (coeffs.length + 1) * A *
          (2 * K) ^ coeffs.length := by
  let δ : ℝ := (2 : ℝ) ^ (-coeffPrec)
  have hδ0 : 0 ≤ δ := by positivity
  induction coeffs with
  | nil =>
      dsimp only [List.foldr_nil, List.length_nil]
      refine ⟨hinit0, ?_, ?_⟩
      · simpa [δ] using hinitExtent
      · have hscale : δ ≤ δ * 16 * 1 * A * 1 := by nlinarith
        exact hinitRadius.trans (by simpa [δ] using hscale)
  | cons q coeffs ih =>
      have htail : ∀ r ∈ coeffs, |(r : ℝ)| ≤ A := by
        intro r hr
        exact hcoeff r (by simp [hr])
      obtain ⟨hacc0, haccExtent, haccRadius⟩ := ih htail
      let acc := coeffs.foldr
        (fun r value => (DyadicComplexBall.ofRat r coeffPrec).add
          (zBall.mul value)) initBall
      let c := DyadicComplexBall.ofRat q coeffPrec
      have hqA : |(q : ℝ)| ≤ A := hcoeff q (by simp)
      have hc0 : 0 ≤ c.realRadius := realRadius_ofRat_nonneg q coeffPrec
      have hcRadius : c.realRadius ≤ δ := by
        simpa [c, δ] using realRadius_ofRat_le q coeffPrec
      have hcExtent : extent c ≤ A + 2 * δ := by
        exact (extent_ofRat_le q coeffPrec).trans (by
          dsimp [δ]
          linarith)
      have hzExtent0 : 0 ≤ extent zBall := by
        rw [extent]
        exact add_nonneg (hi_nonneg zBall) hz0
      have haccExtent0 : 0 ≤ extent acc := by
        rw [extent]
        exact add_nonneg (hi_nonneg acc) hacc0
      have hzRadiusK : zBall.realRadius ≤ K := by
        have : zBall.realRadius ≤ extent zBall := by
          rw [extent]
          linarith [hi_nonneg zBall]
        exact this.trans hzK
      have hK0 : 0 ≤ K := zero_le_one.trans hK
      have hA0 : 0 ≤ A := zero_le_one.trans hA
      have hmul0 : 0 ≤ (zBall.mul acc).realRadius := by
        rw [realRadius_mul]
        exact add_nonneg
          (add_nonneg (mul_nonneg (hi_nonneg zBall) hacc0)
            (mul_nonneg (hi_nonneg acc) hz0))
          (mul_nonneg hz0 hacc0)
      have hout0 : 0 ≤ (c.add (zBall.mul acc)).realRadius := by
        rw [realRadius_add]
        positivity
      have hmulExtent :
          extent (zBall.mul acc) ≤ K *
            ((A + 2 * δ) * (coeffs.length + 1) * K ^ coeffs.length) := by
        calc
          extent (zBall.mul acc) ≤ extent zBall * extent acc :=
            extent_mul_le zBall acc
          _ ≤ K * ((A + 2 * δ) * (coeffs.length + 1) *
              K ^ coeffs.length) :=
            mul_le_mul hzK haccExtent haccExtent0 hK0
      have hpow1 : 1 ≤ K ^ (coeffs.length + 1) := one_le_pow₀ hK
      have houtExtent :
          extent (c.add (zBall.mul acc)) ≤
            (A + 2 * δ) * (coeffs.length + 2) *
              K ^ (coeffs.length + 1) := by
        calc
          extent (c.add (zBall.mul acc)) ≤
              extent c + extent (zBall.mul acc) := extent_add_le _ _
          _ ≤ (A + 2 * δ) +
              K * ((A + 2 * δ) * (coeffs.length + 1) *
                K ^ coeffs.length) := add_le_add hcExtent hmulExtent
          _ ≤ (A + 2 * δ) * (coeffs.length + 2) *
              K ^ (coeffs.length + 1) := by
            rw [pow_succ]
            have hB0 : 0 ≤ A + 2 * δ := by positivity
            calc
              (A + 2 * δ) +
                    K * ((A + 2 * δ) * (coeffs.length + 1) *
                      K ^ coeffs.length) =
                  (A + 2 * δ) * 1 +
                    (A + 2 * δ) * (coeffs.length + 1) *
                      (K ^ coeffs.length * K) := by ring
              _ ≤ (A + 2 * δ) * (K ^ coeffs.length * K) +
                    (A + 2 * δ) * (coeffs.length + 1) *
                      (K ^ coeffs.length * K) :=
                add_le_add (mul_le_mul_of_nonneg_left hpow1 hB0) le_rfl
              _ = (A + 2 * δ) * (coeffs.length + 2) *
                    (K ^ coeffs.length * K) := by
                ring
      have hmulRadius :
          (zBall.mul acc).realRadius ≤
            K * (δ * 16 * (coeffs.length + 1) * A *
              (2 * K) ^ coeffs.length) +
            ((A + 2 * δ) * (coeffs.length + 1) * K ^ coeffs.length) *
              zBall.realRadius := by
        calc
          (zBall.mul acc).realRadius ≤
              extent zBall * acc.realRadius +
                extent acc * zBall.realRadius :=
            realRadius_mul_le zBall acc hz0 hacc0
          _ ≤ K * (δ * 16 * (coeffs.length + 1) * A *
                (2 * K) ^ coeffs.length) +
              ((A + 2 * δ) * (coeffs.length + 1) * K ^ coeffs.length) *
                zBall.realRadius := by
            exact add_le_add
              (mul_le_mul hzK haccRadius hacc0 hK0)
              (mul_le_mul_of_nonneg_right haccExtent hz0)
      have hKpow : K ^ coeffs.length ≤ (2 * K) ^ coeffs.length := by
        gcongr
        nlinarith
      have hKpowK : K ^ coeffs.length ≤
          K * (2 * K) ^ coeffs.length := by
        calc
          K ^ coeffs.length ≤ (2 * K) ^ coeffs.length := hKpow
          _ ≤ K * (2 * K) ^ coeffs.length := by
            nlinarith [pow_nonneg (show 0 ≤ 2 * K by positivity) coeffs.length]
      have hKpowA : K ^ coeffs.length ≤
          A * (2 * K) ^ coeffs.length := by
        calc
          K ^ coeffs.length ≤ (2 * K) ^ coeffs.length := hKpow
          _ ≤ A * (2 * K) ^ coeffs.length := by
            nlinarith [pow_nonneg (show 0 ≤ 2 * K by positivity) coeffs.length]
      have hcross :
          ((A + 2 * δ) * (coeffs.length + 1) * K ^ coeffs.length) *
              zBall.realRadius ≤
            δ * 4 * (coeffs.length + 1) * A * K *
              (2 * K) ^ coeffs.length := by
        have hfirst :
            (A * (coeffs.length + 1) * K ^ coeffs.length) *
                zBall.realRadius ≤
              A * (coeffs.length + 1) * K ^ coeffs.length * (2 * δ) := by
          gcongr
        have hsecond :
            (2 * δ * (coeffs.length + 1) * K ^ coeffs.length) *
                zBall.realRadius ≤
              2 * δ * (coeffs.length + 1) * K ^ coeffs.length * K := by
          gcongr
        have hfirst' :
            A * (coeffs.length + 1) * K ^ coeffs.length * (2 * δ) ≤
              2 * δ * (coeffs.length + 1) * A * K *
                (2 * K) ^ coeffs.length := by
          calc
            A * (coeffs.length + 1) * K ^ coeffs.length * (2 * δ) =
                (2 * δ * (coeffs.length + 1) * A) *
                  K ^ coeffs.length := by ring
            _ ≤ (2 * δ * (coeffs.length + 1) * A) *
                  (K * (2 * K) ^ coeffs.length) :=
              mul_le_mul_of_nonneg_left hKpowK (by positivity)
            _ = 2 * δ * (coeffs.length + 1) * A * K *
                  (2 * K) ^ coeffs.length := by ring
        have hsecond' :
            2 * δ * (coeffs.length + 1) * K ^ coeffs.length * K ≤
              2 * δ * (coeffs.length + 1) * A * K *
                (2 * K) ^ coeffs.length := by
          calc
            2 * δ * (coeffs.length + 1) * K ^ coeffs.length * K =
                (2 * δ * (coeffs.length + 1) * K) *
                  K ^ coeffs.length := by ring
            _ ≤ (2 * δ * (coeffs.length + 1) * K) *
                  (A * (2 * K) ^ coeffs.length) :=
              mul_le_mul_of_nonneg_left hKpowA (by positivity)
            _ = 2 * δ * (coeffs.length + 1) * A * K *
                  (2 * K) ^ coeffs.length := by ring
        calc
          ((A + 2 * δ) * (coeffs.length + 1) * K ^ coeffs.length) *
                zBall.realRadius =
              (A * (coeffs.length + 1) * K ^ coeffs.length) *
                  zBall.realRadius +
                (2 * δ * (coeffs.length + 1) * K ^ coeffs.length) *
                  zBall.realRadius := by ring
          _ ≤ A * (coeffs.length + 1) * K ^ coeffs.length * (2 * δ) +
                2 * δ * (coeffs.length + 1) * K ^ coeffs.length * K :=
            add_le_add hfirst hsecond
          _ ≤ 2 * δ * (coeffs.length + 1) * A * K *
                  (2 * K) ^ coeffs.length +
                2 * δ * (coeffs.length + 1) * A * K *
                  (2 * K) ^ coeffs.length := by
            exact add_le_add hfirst' hsecond'
          _ ≤ δ * 4 * (coeffs.length + 1) * A * K *
                (2 * K) ^ coeffs.length := by
            ring_nf
            exact le_rfl
      have hbig :
          δ + K * (δ * 16 * (coeffs.length + 1) * A *
                (2 * K) ^ coeffs.length) +
              δ * 4 * (coeffs.length + 1) * A * K *
                (2 * K) ^ coeffs.length ≤
            δ * 16 * (coeffs.length + 2) * A *
              (2 * K) ^ (coeffs.length + 1) := by
        rw [pow_succ]
        let X : ℝ := (coeffs.length + 1 : ℝ) * A * K *
          (2 * K) ^ coeffs.length
        let Y : ℝ := (coeffs.length + 2 : ℝ) * A * K *
          (2 * K) ^ coeffs.length
        have hlen : 1 ≤ (coeffs.length + 1 : ℝ) := by norm_num
        have htwoK : 1 ≤ 2 * K := by nlinarith
        have hp : 1 ≤ (2 * K) ^ coeffs.length := one_le_pow₀ htwoK
        have hLA : 1 ≤ (coeffs.length + 1 : ℝ) * A := by
          simpa using mul_le_mul hlen hA (by norm_num : (0 : ℝ) ≤ 1)
            (zero_le_one.trans hlen)
        have hLAK : 1 ≤ (coeffs.length + 1 : ℝ) * A * K := by
          simpa using mul_le_mul hLA hK (by norm_num : (0 : ℝ) ≤ 1)
            (zero_le_one.trans hLA)
        have hbase : 1 ≤ X := by
          dsimp [X]
          simpa using mul_le_mul hLAK hp (by norm_num : (0 : ℝ) ≤ 1)
            (zero_le_one.trans hLAK)
        have hXY : X ≤ Y := by
          dsimp [X, Y]
          gcongr
          norm_num
        have hδX : δ ≤ δ * X := by
          simpa using mul_le_mul_of_nonneg_left hbase hδ0
        calc
          δ + K * (δ * 16 * (coeffs.length + 1) * A *
                  (2 * K) ^ coeffs.length) +
                δ * 4 * (coeffs.length + 1) * A * K *
                  (2 * K) ^ coeffs.length = δ + 20 * δ * X := by
              dsimp [X]
              ring
          _ ≤ 32 * δ * X := by nlinarith
          _ ≤ 32 * δ * Y := by gcongr
          _ = δ * 16 * (coeffs.length + 2) * A *
                ((2 * K) ^ coeffs.length * (2 * K)) := by
              dsimp [Y]
              ring
      have houtRadius :
          (c.add (zBall.mul acc)).realRadius ≤
            δ * 16 * (coeffs.length + 2) * A *
              (2 * K) ^ (coeffs.length + 1) := by
        rw [realRadius_add]
        calc
          c.realRadius + (zBall.mul acc).realRadius ≤
              δ + (K * (δ * 16 * (coeffs.length + 1) * A *
                  (2 * K) ^ coeffs.length) +
                ((A + 2 * δ) * (coeffs.length + 1) * K ^ coeffs.length) *
                  zBall.realRadius) := add_le_add hcRadius hmulRadius
          _ ≤ δ + K * (δ * 16 * (coeffs.length + 1) * A *
                  (2 * K) ^ coeffs.length) +
                δ * 4 * (coeffs.length + 1) * A * K *
                  (2 * K) ^ coeffs.length := by linarith
          _ ≤ _ := hbig
      refine ⟨hout0, ?_, ?_⟩
      · change extent (c.add (zBall.mul acc)) ≤
          (A + 2 * (2 : ℝ) ^ (-coeffPrec)) * ((q :: coeffs).length + 1) *
            K ^ (q :: coeffs).length
        have hlenReal : ((q :: coeffs).length : ℝ) + 1 =
            (coeffs.length : ℝ) + 2 := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
        have hlenNat : (q :: coeffs).length = coeffs.length + 1 := rfl
        rw [hlenReal, hlenNat]
        simpa only [δ] using houtExtent
      · change (c.add (zBall.mul acc)).realRadius ≤
          (2 : ℝ) ^ (-coeffPrec) * 16 * ((q :: coeffs).length + 1) * A *
            (2 * K) ^ (q :: coeffs).length
        have hlenReal : ((q :: coeffs).length : ℝ) + 1 =
            (coeffs.length : ℝ) + 2 := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
        have hlenNat : (q :: coeffs).length = coeffs.length + 1 := rfl
        rw [hlenReal, hlenNat]
        simpa only [δ] using houtRadius

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

/-- Two certified balls containing the same point meet. -/
theorem meets_of_mem {a b : DyadicComplexBall} {z : ℂ}
    (ha : z ∈ a.set) (hb : z ∈ b.set) : a.meets b = true := by
  have ha' : dist a.center z ≤ a.realRadius := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp ha
  have hb' : dist z b.center ≤ b.realRadius :=
    Metric.mem_closedBall.mp hb
  have hra : 0 ≤ a.realRadius := dist_nonneg.trans ha'
  have hrb : 0 ≤ b.realRadius := dist_nonneg.trans hb'
  have hdist : dist a.center b.center ≤ a.realRadius + b.realRadius :=
    (dist_triangle a.center z b.center).trans (add_le_add ha' hb')
  have hsq : dist a.center b.center ^ 2 ≤
      (a.realRadius + b.realRadius) ^ 2 :=
    (sq_le_sq₀ dist_nonneg (add_nonneg hra hrb)).mpr hdist
  have hreal :
      HexRootsMathlib.Dyadic.toReal
          (GaussDyadic.distSq (a.re, a.im) (b.re, b.im)) ≤
        HexRootsMathlib.Dyadic.toReal
          ((a.radius + b.radius) * (a.radius + b.radius)) := by
    simpa only [HexRootsMathlib.Dyadic.toReal_mul,
      HexRootsMathlib.Dyadic.toReal_add,
      HexRootsMathlib.DyadicSquare.toReal_distSq,
      DyadicComplexBall.center, DyadicComplexBall.realRadius,
      pow_two] using hsq
  have hdy := HexRootsMathlib.Dyadic.toReal_le_toReal_iff.mp hreal
  simpa [DyadicComplexBall.meets] using decide_eq_true hdy

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

private theorem evalRatBall_radius_le (f : DensePoly Rat) (s : DyadicSquare)
    (coeffPrec : Int) (A K : ℝ) (hA : 1 ≤ A) (hK : 1 ≤ K)
    (hs0 : 0 ≤ s.toBall.realRadius) (hsK : extent s.toBall ≤ K)
    (hsUlp : s.toBall.realRadius ≤ 2 * (2 : ℝ) ^ (-coeffPrec))
    (hcoeff : ∀ q ∈ f.toList, |(q : ℝ)| ≤ A) :
    (QAdjoin.evalRatBall f s coeffPrec).realRadius ≤
      (2 : ℝ) ^ (-coeffPrec) * 16 * f.size * A * (2 * K) ^ f.size := by
  unfold QAdjoin.evalRatBall
  dsimp only
  cases hback : f.toArray.back? with
  | none =>
      simp only
      simp [DyadicComplexBall.zero, realRadius]
      positivity
  | some top =>
      obtain ⟨pre, hprefix⟩ := Array.back?_eq_some_iff.mp hback
      have hlist : f.toList = pre.toList ++ [top] := by
        rw [DensePoly.toList, hprefix, Array.toList_push]
      have hsize : f.size = pre.size + 1 := by
        rw [← DensePoly.toArray_size, hprefix]
        simp
      have hstart : f.toArray.size - 1 = pre.size := by
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
        rw [hstart, Array.foldr_eq_foldr_extract]
        rw [hprefix, Array.extract_push_of_le (le_refl pre.size)]
        simp
      have htop : |(top : ℝ)| ≤ A := by
        apply hcoeff top
        rw [hlist]
        simp
      have hpre : ∀ q ∈ pre.toList, |(q : ℝ)| ≤ A := by
        intro q hq
        apply hcoeff q
        rw [hlist]
        simp [hq]
      have hinit0 :
          0 ≤ (DyadicComplexBall.ofRat top coeffPrec).realRadius :=
        realRadius_ofRat_nonneg top coeffPrec
      have hinitExtent :
          extent (DyadicComplexBall.ofRat top coeffPrec) ≤
            A + 2 * (2 : ℝ) ^ (-coeffPrec) :=
        (extent_ofRat_le top coeffPrec).trans (by linarith)
      have hinitRadius :
          (DyadicComplexBall.ofRat top coeffPrec).realRadius ≤
            (2 : ℝ) ^ (-coeffPrec) := realRadius_ofRat_le top coeffPrec
      have hb := horner_bounds pre.toList s.toBall
        (DyadicComplexBall.ofRat top coeffPrec) coeffPrec A K hA hK hs0 hsK
        hsUlp hinit0 hinitExtent hinitRadius hpre
      have hlen : pre.toList.length + 1 = f.size := by
        simp [hsize]
      have hlenReal : (pre.toList.length : ℝ) + 1 = f.size := by
        exact_mod_cast hlen
      have hpow : (2 * K) ^ pre.toList.length ≤ (2 * K) ^ f.size := by
        exact pow_le_pow_right₀ (by nlinarith) (by omega)
      simp only
      rw [hfold]
      calc
        (pre.toList.foldr
              (fun q value => (DyadicComplexBall.ofRat q coeffPrec).add
                (s.toBall.mul value))
              (DyadicComplexBall.ofRat top coeffPrec)).realRadius ≤
            (2 : ℝ) ^ (-coeffPrec) * 16 * (pre.toList.length + 1) * A *
              (2 * K) ^ pre.toList.length := hb.2.2
        _ = (2 : ℝ) ^ (-coeffPrec) * 16 * f.size * A *
              (2 * K) ^ pre.toList.length := by rw [hlenReal]
        _ ≤ (2 : ℝ) ^ (-coeffPrec) * 16 * f.size * A *
              (2 * K) ^ f.size := by
          gcongr

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

private theorem eval_guard_radius (a : QAdjoin p x) (rep : RefinedIsolation p)
    (prec : Int)
    {out : {rep' : RefinedIsolation p //
      SimpleRoot.mk rep' = SimpleRoot.mk rep}}
    (href : rep.refineTo?
      (prec + (approxGuardBits rep.1.square a.coeffs : Int))
      .nkThenPellet = some out) :
    (evalRatBall a.coeffs out.1.1.square
        (prec + (approxGuardBits rep.1.square a.coeffs : Int))).realRadius ≤
      (2 : ℝ) ^ (-prec) := by
  let G := approxGuardBits rep.1.square a.coeffs
  let A : ℝ := (2 : ℝ) ^ coeffBits a.coeffs
  let K : ℝ := 4 * (2 : ℝ) ^ rootBits rep.1.square
  have hA : 1 ≤ A := by
    dsimp [A]
    exact one_le_pow₀ (by norm_num)
  have hK : 1 ≤ K := by
    dsimp [K]
    have hp : 1 ≤ (2 : ℝ) ^ rootBits rep.1.square :=
      one_le_pow₀ (by norm_num)
    nlinarith
  have hs0 : 0 ≤ out.1.1.square.toBall.realRadius :=
    DyadicComplexBall.realRadius_toBall_nonneg _
  have hsK : DyadicComplexBall.extent out.1.1.square.toBall ≤ K := by
    calc
      DyadicComplexBall.extent out.1.1.square.toBall ≤
          4 * DyadicComplexBall.extent rep.1.square.toBall :=
        DyadicComplexBall.refined_extent_le rep
          (prec + (approxGuardBits rep.1.square a.coeffs : Int))
          .nkThenPellet href
      _ ≤ 4 * (2 : ℝ) ^ rootBits rep.1.square :=
        mul_le_mul_of_nonneg_left
          (DyadicComplexBall.extent_toBall_le rep.1.square) (by norm_num)
      _ = K := rfl
  have hsUlp : out.1.1.square.toBall.realRadius ≤
      2 * (2 : ℝ) ^
        (-(prec + (approxGuardBits rep.1.square a.coeffs : Int))) := by
    apply DyadicComplexBall.realRadius_toBall_le
    exact RefinedIsolation.refineTo?_precision rep
      (prec + (approxGuardBits rep.1.square a.coeffs : Int))
      .nkThenPellet href
  have hcoeff : ∀ q ∈ a.coeffs.toList, |(q : ℝ)| ≤ A := by
    intro q hq
    exact (DyadicComplexBall.coeff_le_twoPow hq).trans_eq rfl
  have heval := DyadicComplexBall.evalRatBall_radius_le a.coeffs
    out.1.1.square
    (prec + (approxGuardBits rep.1.square a.coeffs : Int)) A K hA hK
    hs0 hsK hsUlp hcoeff
  have hsizeNat : a.coeffs.size ≤
      2 ^ Hex.ceilLog2 (a.coeffs.size + 1) := by
    exact (Nat.le_add_right _ _).trans
      (HexRootsMathlib.le_two_pow_ceilLog2 (a.coeffs.size + 1))
  have hsize : (a.coeffs.size : ℝ) ≤
      (2 : ℝ) ^ Hex.ceilLog2 (a.coeffs.size + 1) := by
    exact_mod_cast hsizeNat
  have hbase :
      2 * K = (2 : ℝ) ^ (rootBits rep.1.square + 3) := by
    dsimp [K]
    rw [pow_add]
    norm_num
    ring
  have hexp :
      4 + Hex.ceilLog2 (a.coeffs.size + 1) + coeffBits a.coeffs +
          a.coeffs.size * (rootBits rep.1.square + 3) ≤ G := by
    dsimp [G, approxGuardBits]
    omega
  have hamp :
      16 * (a.coeffs.size : ℝ) * A * (2 * K) ^ a.coeffs.size ≤
        (2 : ℝ) ^ G := by
    calc
      16 * (a.coeffs.size : ℝ) * A * (2 * K) ^ a.coeffs.size ≤
          16 * (2 : ℝ) ^ Hex.ceilLog2 (a.coeffs.size + 1) * A *
            (2 * K) ^ a.coeffs.size := by
        gcongr
      _ = (2 : ℝ) ^
          (4 + Hex.ceilLog2 (a.coeffs.size + 1) + coeffBits a.coeffs +
            a.coeffs.size * (rootBits rep.1.square + 3)) := by
        rw [hbase]
        dsimp [A]
        rw [show (16 : ℝ) = (2 : ℝ) ^ 4 by norm_num]
        rw [← pow_add, ← pow_add, ← pow_mul, ← pow_add]
        congr 1
        rw [Nat.mul_comm (rootBits rep.1.square + 3) a.coeffs.size]
      _ ≤ (2 : ℝ) ^ G := pow_le_pow_right₀ (by norm_num) hexp
  calc
    (evalRatBall a.coeffs out.1.1.square
        (prec + (approxGuardBits rep.1.square a.coeffs : Int))).realRadius ≤
        (2 : ℝ) ^
            (-(prec + (approxGuardBits rep.1.square a.coeffs : Int))) *
          (16 * (a.coeffs.size : ℝ) * A * (2 * K) ^ a.coeffs.size) := by
      simpa only [mul_assoc] using heval
    _ ≤ (2 : ℝ) ^ (-(prec + (G : Int))) * (2 : ℝ) ^ G := by
      dsimp only [G]
      gcongr
    _ = (2 : ℝ) ^ (-prec) := by
      rw [← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
      congr 1
      omega

/-- The guarded approximation achieves the requested dyadic radius. -/
theorem approx_radius (a : QAdjoin p x) (rep : RefinedIsolation p)
    (h : SimpleRoot.mk rep = x) (prec : Int) :
    (a.approx rep h prec).2.realRadius ≤ (2 : ℝ) ^ (-prec) := by
  unfold approx
  dsimp only
  have hsome := RefinedIsolation.refineTo?_isSome rep
    (prec + (approxGuardBits rep.1.square a.coeffs : Int))
  cases href : rep.refineTo?
      (prec + (approxGuardBits rep.1.square a.coeffs : Int)) .nkThenPellet with
  | none => simp [href] at hsome
  | some out =>
      simp only
      exact eval_guard_radius a rep prec href

end QAdjoin

end Hex
