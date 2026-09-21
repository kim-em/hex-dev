/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFn.Oracle
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

namespace Hex.OrderedFn.Oracle

/-- Integer image of Mathlib's semantic sign. -/
noncomputable def sgn (x : ℝ) : Int := (SignType.sign x : Int)

theorem sgn_div (x y : ℝ) : sgn (x / y) = sgn x * sgn y := by
  have hi : SignType.sign y⁻¹ = SignType.sign y := by
    simp only [sign_apply, inv_pos, inv_lt_zero]
  simp [sgn, div_eq_mul_inv, sign_mul, hi]

/-- Containment refers to the actual semantic subject of a bound. -/
def Contains (a : Bounds) (x : ℝ) : Prop := (a.lower : ℝ) ≤ x ∧ x ≤ (a.upper : ℝ)

/-- Validity for the same providers and requests as the computational interface. -/
structure ApproximationCorrect {K : Type u} [Semiring K]
    (ι : K →+* ℝ) (τ : ℝ) (a : Approximation K) : Prop where
  coeff : ∀ x δ, 0 < δ → Contains (a.coeff x δ) (ι x)
  constant : ∀ δ, 0 < δ → Contains (a.constant δ) τ

namespace Contains

@[simp] theorem singleton (q : Rat) : Contains (.singleton q) (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem neg {a : Bounds} {x : ℝ} (h : Contains a x) : Contains a.neg (-x) := by
  simpa [Contains, Bounds.neg] using And.intro (neg_le_neg h.2) (neg_le_neg h.1)

theorem add {a b : Bounds} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (a.add b) (x + y) := by
  simpa [Contains, Bounds.add] using
    And.intro (add_le_add ha.1 hb.1) (add_le_add ha.2 hb.2)

private theorem mul_bounds {a b c d x y : ℝ} (hx : a ≤ x ∧ x ≤ b)
    (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y ∧
      x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have step (r : ℝ) : min (r * c) (r * d) ≤ r * y ∧ r * y ≤ max (r * c) (r * d) := by
    rcases le_total 0 r with hr | hr
    · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_left hy.1 hr),
        (mul_le_mul_of_nonneg_left hy.2 hr).trans (le_max_right _ _)⟩
    · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_left hy.2 hr),
        (mul_le_mul_of_nonpos_left hy.1 hr).trans (le_max_left _ _)⟩
  rcases le_total 0 y with hy0 | hy0
  · exact ⟨(min_le_left _ _).trans ((step a).1.trans
        (mul_le_mul_of_nonneg_right hx.1 hy0)),
      ((mul_le_mul_of_nonneg_right hx.2 hy0).trans (step b).2).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans ((step b).1.trans
        (mul_le_mul_of_nonpos_right hx.2 hy0)),
      ((mul_le_mul_of_nonpos_right hx.1 hy0).trans (step a).2).trans (le_max_left _ _)⟩

theorem mul {a b : Bounds} {x y : ℝ} (ha : Contains a x) (hb : Contains b y) :
    Contains (a.mul b) (x * y) := by
  simpa [Contains, Bounds.mul, Bounds.hull4, Rat.cast_min, Rat.cast_max] using
    mul_bounds ha hb

theorem inter {a b c : Bounds} {x : ℝ} (ha : Contains a x) (hb : Contains b x)
    (hc : a.inter b = some c) : Contains c x := by
  unfold Bounds.inter at hc
  split at hc
  · cases hc
    simpa [Contains, Rat.cast_min, Rat.cast_max] using And.intro
      (max_le ha.1 hb.1) (le_min ha.2 hb.2)
  · contradiction

theorem ne_zero {a : Bounds} {x : ℝ} (ha : Contains a x) (h : a.separated = true) :
    x ≠ 0 := by
  simp only [Bounds.separated, Bool.or_eq_true, decide_eq_true_eq] at h
  rcases h with h | h
  · have : (a.upper : ℝ) < 0 := by exact_mod_cast h
    exact (ha.2.trans_lt this).ne
  · have : (0 : ℝ) < a.lower := by exact_mod_cast h
    exact (this.trans_le ha.1).ne'

theorem div {a b c : Bounds} {x y : ℝ} (ha : Contains a x) (hb : Contains b y)
    (hc : a.div? b = some c) : Contains c (x / y) ∧ y ≠ 0 := by
  unfold Bounds.div? at hc
  split at hc
  next h =>
    cases hc
    refine ⟨?_, hb.ne_zero h⟩
    have hi : (b.upper : ℝ)⁻¹ ≤ y⁻¹ ∧ y⁻¹ ≤ (b.lower : ℝ)⁻¹ := by
      simp only [Bounds.separated, Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with hn | hp
      · have hn : (b.upper : ℝ) < 0 := by exact_mod_cast hn
        exact ⟨(inv_le_inv_of_neg hn (hb.2.trans_lt hn)).mpr hb.2,
          (inv_le_inv_of_neg (hb.2.trans_lt hn) (hb.1.trans_lt (hb.2.trans_lt hn))).mpr hb.1⟩
      · have hp : (0 : ℝ) < b.lower := by exact_mod_cast hp
        exact ⟨(inv_le_inv₀ (hp.trans_le (hb.1.trans hb.2)) (hp.trans_le hb.1)).mpr hb.2,
          (inv_le_inv₀ (hp.trans_le hb.1) hp).mpr hb.1⟩
    simpa [Contains, Bounds.hull4, Rat.cast_min, Rat.cast_max, div_eq_mul_inv,
      min_comm, max_comm] using mul_bounds ha hi
  next h => contradiction

/-- A separated bound determines the sign and excludes zero. -/
theorem sign {a : Bounds} {x : ℝ} {s : Int} (ha : Contains a x)
    (hs : a.sign? = some s) : s = sgn x ∧ x ≠ 0 := by
  unfold Bounds.sign? at hs
  split at hs
  next hp =>
    cases hs
    have hp : (0 : ℝ) < a.lower := by exact_mod_cast hp
    have hx := hp.trans_le ha.1
    exact ⟨by simp [sgn, sign_pos hx], hx.ne'⟩
  next hp =>
    split at hs
    next hn =>
      cases hs
      have hn : (a.upper : ℝ) < 0 := by exact_mod_cast hn
      have hx := ha.2.trans_lt hn
      exact ⟨by simp [sgn, sign_neg hx], hx.ne⟩
    next hn => contradiction

/-- Singleton zero is exact evidence; containment alone does not imply zero. -/
theorem exactSign {a : Bounds} {x : ℝ} {s : Int} (ha : Contains a x)
    (hs : a.exactSign? = some s) : s = sgn x := by
  unfold Bounds.exactSign? at hs
  split at hs
  next h =>
    cases hs
    have hx : x = 0 := le_antisymm
      (by simpa [h.2] using ha.2) (by simpa [h.1] using ha.1)
    simp [hx, sgn]
  next h => exact (ha.sign hs).1

end Contains
end Hex.OrderedFn.Oracle
