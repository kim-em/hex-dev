/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexOrderedFnTheory.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.GCongr

public section

/-!
Endpoint estimates and shrinking-width proofs for the actual exact-bound Horner
recurrence and quotient enclosures away from zero.
-/

namespace Hex.OrderedFn.Oracle

open Filter Topology

namespace Contains

/-- Each endpoint error is bounded by the exact interval width. -/
theorem endpoint_error {a : Bounds} {x : ℝ} (ha : Contains a x) :
    |(a.lower : ℝ) - x| ≤ (a.width : ℝ) ∧
      |(a.upper : ℝ) - x| ≤ (a.width : ℝ) := by
  have hw : (a.width : ℝ) = (a.upper : ℝ) - a.lower := by
    simp [Bounds.width]
  rw [hw]
  constructor <;> apply abs_le.mpr <;> constructor <;> linarith [ha.1, ha.2]

/-- Product endpoint errors include the simultaneous change in both factors. -/
theorem product_error {a b x y ea eb : ℝ}
    (ha : |a - x| ≤ ea) (hb : |b - y| ≤ eb) :
    |a * b - x * y| ≤ |x| * eb + |y| * ea + ea * eb := by
  have hea := (abs_nonneg (a - x)).trans ha
  have heb := (abs_nonneg (b - y)).trans hb
  calc
    |a * b - x * y| = |x * (b - y) + y * (a - x) + (a - x) * (b - y)| := by
      congr 1; ring
    _ ≤ |x * (b - y)| + |y * (a - x)| + |(a - x) * (b - y)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ |x| * eb + |y| * ea + ea * eb := by
      simp only [abs_mul]
      gcongr

/-- The width of the four-product hull is bounded by twice its endpoint error. -/
theorem mul_width_le {a b : Bounds} {x y : ℝ}
    (ha : Contains a x) (hb : Contains b y) :
    ((a.mul b).width : ℝ) ≤
      2 * (|x| * (b.width : ℝ) + |y| * (a.width : ℝ) + (a.width : ℝ) * b.width) := by
  obtain ⟨ha₁, ha₂⟩ := ha.endpoint_error
  obtain ⟨hb₁, hb₂⟩ := hb.endpoint_error
  have h₁ := abs_le.mp (product_error ha₁ hb₁)
  have h₂ := abs_le.mp (product_error ha₁ hb₂)
  have h₃ := abs_le.mp (product_error ha₂ hb₁)
  have h₄ := abs_le.mp (product_error ha₂ hb₂)
  let e := |x| * (b.width : ℝ) + |y| * (a.width : ℝ) + (a.width : ℝ) * b.width
  have hl : x * y - e ≤ ((a.mul b).lower : ℝ) := by
    simp only [Bounds.mul, Bounds.hull4, Rat.cast_min, Rat.cast_mul, le_min_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  have hu : ((a.mul b).upper : ℝ) ≤ x * y + e := by
    simp only [Bounds.mul, Bounds.hull4, Rat.cast_max, Rat.cast_mul, max_le_iff]
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩⟩
  rw [show ((a.mul b).width : ℝ) = ((a.mul b).upper : ℝ) - (a.mul b).lower by
    simp [Bounds.width]]
  dsimp only [e] at hl hu
  linarith

/-- Exact addition adds interval widths. -/
theorem add_converges {a b : Nat → Bounds}
    (ha : Tendsto (fun n => ((a n).width : ℝ)) atTop (𝓝 0))
    (hb : Tendsto (fun n => ((b n).width : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (((a n).add (b n)).width : ℝ)) atTop (𝓝 0) := by
  simpa only [Bounds.width_add, Rat.cast_add, zero_add] using ha.add hb

/-- The product width estimate tends to zero when both input widths do. -/
theorem mul_converges {a b : Nat → Bounds} {x y : ℝ}
    (hax : ∀ n, Contains (a n) x) (hby : ∀ n, Contains (b n) y)
    (ha : Tendsto (fun n => ((a n).width : ℝ)) atTop (𝓝 0))
    (hb : Tendsto (fun n => ((b n).width : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => (((a n).mul (b n)).width : ℝ)) atTop (𝓝 0) := by
  apply squeeze_zero (fun n => by exact_mod_cast ((a n).mul (b n)).width_nonneg)
    (fun n => (hax n).mul_width_le (hby n))
  simpa using (((hb.const_mul |x|).add (ha.const_mul |y|)).add (ha.mul hb)).const_mul 2

/-- Containment and shrinking width force both endpoints to the subject. -/
theorem endpoints_tendsto {b : Nat → Bounds} {x : ℝ}
    (hc : ∀ n, Contains (b n) x)
    (hw : Tendsto (fun n => ((b n).width : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => ((b n).lower : ℝ)) atTop (𝓝 x) ∧
      Tendsto (fun n => ((b n).upper : ℝ)) atTop (𝓝 x) := by
  constructor
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (show Tendsto (fun n => x - ((b n).width : ℝ)) atTop (𝓝 x) by
        simpa using tendsto_const_nhds.sub hw) tendsto_const_nhds
    · intro n
      have := (abs_le.mp (hc n).endpoint_error.1).1
      linarith
    · exact fun n => (hc n).1
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (show Tendsto (fun n => x + ((b n).width : ℝ)) atTop (𝓝 x) by
        simpa using tendsto_const_nhds.add hw)
    · exact fun n => (hc n).2
    · intro n
      have := (abs_le.mp (hc n).endpoint_error.2).2
      linarith

/-- All four quotient corners tend to the same quotient. Consequently their
exact hull narrows whenever the limiting denominator is nonzero. -/
theorem quotient_converges {a b : Nat → Bounds} {x y : ℝ}
    (hax : ∀ n, Contains (a n) x) (hby : ∀ n, Contains (b n) y)
    (ha : Tendsto (fun n => ((a n).width : ℝ)) atTop (𝓝 0))
    (hb : Tendsto (fun n => ((b n).width : ℝ)) atTop (𝓝 0)) (hy : y ≠ 0) :
    Tendsto (fun n => ((Bounds.hull4
      ((a n).lower / (b n).lower) ((a n).lower / (b n).upper)
      ((a n).upper / (b n).lower) ((a n).upper / (b n).upper)).width : ℝ))
      atTop (𝓝 0) := by
  obtain ⟨ha₁, ha₂⟩ := endpoints_tendsto hax ha
  obtain ⟨hb₁, hb₂⟩ := endpoints_tendsto hby hb
  have h₁ := ha₁.div hb₁ hy
  have h₂ := ha₁.div hb₂ hy
  have h₃ := ha₂.div hb₁ hy
  have h₄ := ha₂.div hb₂ hy
  simpa [Bounds.width, Bounds.hull4] using
    ((h₁.max h₂).max (h₃.max h₄)).sub ((h₁.min h₂).min (h₃.min h₄))

/-- Nonzero contained values are eventually strictly separated from zero. -/
theorem sign_eventually {b : Nat → Bounds} {x : ℝ}
    (hc : ∀ n, Contains (b n) x)
    (hw : Tendsto (fun n => ((b n).width : ℝ)) atTop (𝓝 0)) (hx : x ≠ 0) :
    ∀ᶠ n in atTop, ((b n).sign?).isSome = true := by
  filter_upwards [(tendsto_order.mp hw).2 |x| (abs_pos.mpr hx)] with n hn
  have he := (hc n).endpoint_error
  rcases lt_or_gt_of_ne hx with hx | hx
  · have hu : (b n).upper < 0 := by
      have := (abs_le.mp he.2).2
      rw [abs_of_neg hx] at hn
      exact_mod_cast (show ((b n).upper : ℝ) < 0 by linarith)
    simp [Bounds.sign?, hu, (lt_of_le_of_lt (b n).ordered hu).not_gt]
  · have hl : 0 < (b n).lower := by
      have := (abs_le.mp he.1).1
      rw [abs_of_pos hx] at hn
      exact_mod_cast (show (0 : ℝ) < (b n).lower by linarith)
    simp [Bounds.sign?, hl]

end Contains

end Hex.OrderedFn.Oracle

namespace Hex.OrderedFn.Real

open Oracle Filter Topology
universe u
variable {K : Type u} [Field K] [DecidableEq K]
variable {ι : K →+* ℝ} {τ : ℝ} {a : Approximation K}

/-- The executed dyadic requests tend to zero. -/
theorem precision_tendsto : Tendsto (fun n => (precision n : ℝ)) atTop (𝓝 0) := by
  simpa [precision, one_div, inv_pow] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num : (2 : ℝ)⁻¹ < 1))

/-- A provider's rational width guarantee narrows its dyadic requests. -/
theorem width_tendsto (b : Rat → Bounds) (hw : ∀ δ, 0 < δ → (b δ).width ≤ δ) :
    Tendsto (fun n => ((b (precision n)).width : ℝ)) atTop (𝓝 0) :=
  squeeze_zero (fun n => by exact_mod_cast (b (precision n)).width_nonneg)
    (fun n => by exact_mod_cast hw (precision n) (precision_pos n)) precision_tendsto

/-- The actual Horner loop narrows by the sum and product width estimates,
refining every coefficient and the argument at the same dyadic request. -/
theorem horner_converges (ha : ApproximationCorrect ι τ a) (hw : ApproximationWidth a)
    (p : DensePoly K) :
    Tendsto (fun n => ((enclose a p (precision n)).width : ℝ)) atTop (𝓝 0) := by
  let bound (l : List K) (n : Nat) := l.foldr
    (fun c acc => (a.coeff c (precision n)).add ((a.constant (precision n)).mul acc))
    (.singleton 0)
  have h (l : List K) :
      (∀ n, Contains (bound l n) (l.foldr (fun c acc => ι c + τ * acc) 0)) ∧
      Tendsto (fun n => ((bound l n).width : ℝ)) atTop (𝓝 0) := by
    induction l with
    | nil =>
      exact ⟨by simp [bound, Contains, Bounds.singleton], by simp [bound]⟩
    | cons c cs ih =>
      refine ⟨fun n => (ha.coeff c _ (precision_pos n)).add
        ((ha.constant _ (precision_pos n)).mul (ih.1 n)), ?_⟩
      exact Contains.add_converges (width_tendsto _ (hw.coeff c))
        (Contains.mul_converges (fun n => ha.constant _ (precision_pos n)) ih.1
          (width_tendsto _ hw.constant) ih.2)
  simpa only [enclose, ← Array.foldr_toList] using (h p.coeffs.toList).2

end Hex.OrderedFn.Real
