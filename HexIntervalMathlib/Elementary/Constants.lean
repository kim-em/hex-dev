/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Exact point bounds for π

Machin's identity reduces π to arctangents at 1/5 and 1/239. Finite
Taylor sums and geometric tail bounds give rational cuts at every order.
These analytic source theorems do not assume a proposed enclosure contains π.
Executable bounded certificate production and replay belong to HexInterval.
-/

namespace Hex.Interval.Pi

open Finset

/-- The first `n` terms of the arctangent series. -/
noncomputable def arctanSum (x : ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range n, (-1 : ℝ) ^ i * x ^ (2 * i + 1) / (2 * i + 1)

/-- A geometric majorant of the omitted arctangent terms, for `0 ≤ x < 1`. -/
noncomputable def arctanError (x : ℝ) (n : ℕ) : ℝ :=
  x * (x ^ 2) ^ n / (1 - x ^ 2)

theorem arctan_bound {x : ℝ} (hx : 0 ≤ x) (h1 : x < 1) (n : ℕ) :
    |arctanSum x n - Real.arctan x| ≤ arctanError x n := by
  have hx2 : x ^ 2 < 1 := by nlinarith
  have terms (i : ℕ) :
      ‖(-1 : ℝ) ^ i * x ^ (2 * i + 1) / (2 * i + 1 : ℕ)‖ ≤
        x * (x ^ 2) ^ i := by
    rw [norm_div, norm_mul, norm_pow, norm_pow]
    simp only [norm_neg, norm_one, one_pow, one_mul, Real.norm_eq_abs,
      abs_of_nonneg hx, Nat.abs_cast]
    calc
      x ^ (2 * i + 1) / (2 * i + 1 : ℕ) ≤ x ^ (2 * i + 1) :=
        div_le_self (pow_nonneg hx _) (by exact_mod_cast (show 1 ≤ 2 * i + 1 by omega))
      _ = x * (x ^ 2) ^ i := by rw [pow_succ, pow_mul]; ring
  simpa [arctanSum, arctanError, Real.norm_eq_abs, Nat.cast_add, Nat.cast_mul] using
    norm_sub_le_of_geometric_bound_of_hasSum hx2 terms
    (Real.hasSum_arctan (by simpa [Real.norm_eq_abs, abs_of_nonneg hx] using h1)) n

/-- Machin's rational approximation with a common order for both sums. -/
noncomputable def partialSum (n : ℕ) : ℝ :=
  16 * arctanSum (1 / 5) n - 4 * arctanSum (1 / 239) n

/-- Reconstruction adds the absolute errors with coefficients 16 and 4. -/
noncomputable def error (n : ℕ) : ℝ :=
  16 * arctanError (1 / 5) n + 4 * arctanError (1 / 239) n

/-- Ordinary-kernel authentication of both cuts at arbitrary approximation order. -/
theorem bounds (n : ℕ) :
    partialSum n - error n ≤ Real.pi ∧ Real.pi ≤ partialSum n + error n := by
  have h5 := arctan_bound (x := 1 / 5) (by norm_num) (by norm_num) n
  have h239 := arctan_bound (x := 1 / 239) (by norm_num) (by norm_num) n
  have machin := Real.four_mul_arctan_inv_5_sub_arctan_inv_239
  rw [abs_le] at h5 h239
  simp only [one_div] at h5 h239 ⊢
  dsimp [partialSum, error]
  simp only [one_div]
  constructor <;> linarith

/-- Rational or dyadic outward cuts can be replayed using exact inequalities. -/
theorem enclosure (n : ℕ) {lower upper : ℝ}
    (lo : lower ≤ partialSum n - error n)
    (hi : partialSum n + error n ≤ upper) :
    lower ≤ Real.pi ∧ Real.pi ≤ upper :=
  ⟨lo.trans (bounds n).1, (bounds n).2.trans hi⟩

/-- A geometric estimate giving a linear sufficient approximation order. -/
theorem error_le (n : ℕ) : error n ≤ 4 / (2 : ℝ) ^ n := by
  calc
    error n = (10 / 3 : ℝ) * (1 / 25 : ℝ) ^ n +
        (239 / 14280 : ℝ) * (1 / 57121 : ℝ) ^ n := by
      norm_num [error, arctanError]
      ring
    _ ≤ (10 / 3 : ℝ) * (1 / 2 : ℝ) ^ n +
        (239 / 14280 : ℝ) * (1 / 2 : ℝ) ^ n := by
      gcongr <;> norm_num
    _ = (10 / 3 + 239 / 14280 : ℝ) / 2 ^ n := by rw [div_pow]; ring
    _ ≤ 4 / (2 : ℝ) ^ n := by gcongr; norm_num

/-- Order `k+4` reserves half the requested width for outward rounding. -/
theorem width_le (k : ℕ) :
    (partialSum (k + 4) + error (k + 4)) -
      (partialSum (k + 4) - error (k + 4)) ≤ 1 / (2 : ℝ) ^ (k + 1) := by
  have h := error_le (k + 4)
  have power : (2 : ℝ) ^ k > 0 := by positivity
  simp only [pow_add] at h ⊢
  norm_num at h ⊢
  field_simp at h ⊢
  nlinarith

end Hex.Interval.Pi
