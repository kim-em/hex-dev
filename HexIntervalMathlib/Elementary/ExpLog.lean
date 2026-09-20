/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Exact point bounds for exp(1)

At argument one no reduction or reconstruction is necessary. The finite
factorial sum and Mathlib's explicit exponential remainder authenticate both
cuts at every positive order. These are analytic source theorems, not a
bounded runtime provider or a general exponential/logarithm range API.
-/

namespace Hex.Interval.ExpOne

open Finset

noncomputable def partialSum (n : ℕ) : ℝ :=
  ∑ i ∈ range n, 1 / (i.factorial : ℝ)

noncomputable def error (n : ℕ) : ℝ :=
  (n + 1 : ℝ) / ((n.factorial : ℝ) * n)

/-- Both Taylor cuts, with the positive-order premise required by the remainder. -/
theorem bounds {n : ℕ} (hn : 0 < n) :
    partialSum n - error n ≤ Real.exp 1 ∧
      Real.exp 1 ≤ partialSum n + error n := by
  have remainder := Real.exp_bound (x := 1) (by simp) hn
  simp only [abs_one, one_pow, one_mul, Nat.cast_succ] at remainder
  rw [abs_le] at remainder
  dsimp [partialSum, error]
  constructor <;> linarith

/-- Exact outward comparisons suffice; the proposed cuts supply no analytic premise. -/
theorem enclosure {n : ℕ} (hn : 0 < n) {lower upper : ℝ}
    (lo : lower ≤ partialSum n - error n)
    (hi : partialSum n + error n ≤ upper) :
    lower ≤ Real.exp 1 ∧ Real.exp 1 ≤ upper :=
  ⟨lo.trans (bounds hn).1, (bounds hn).2.trans hi⟩

/-- A simple geometric estimate sufficient to choose the Taylor order effectively. -/
theorem error_le (n : ℕ) : error (n + 1) ≤ 2 / (2 : ℝ) ^ n := by
  have factorial : (2 : ℝ) ^ n ≤ ((n + 1).factorial : ℝ) := by
    exact_mod_cast (show 2 ^ n ≤ (n + 1).factorial by
      simpa [Nat.add_comm] using (Nat.factorial_mul_pow_le_factorial (m := 1) (n := n)))
  have positive : (0 : ℝ) < (n + 1).factorial := by positivity
  dsimp [error]
  calc
    _ ≤ 2 / ((n + 1).factorial : ℝ) := by
      apply (div_le_iff₀ (by positivity)).2
      field_simp
      push_cast
      linarith
    _ ≤ 2 / (2 : ℝ) ^ n := by gcongr

/-- The unrounded analytic enclosure at order `k+4` uses at most half the width
budget, leaving room for two outward rounding errors on the `2^(-(k+2))` grid. -/
theorem width_le (k : ℕ) :
    (partialSum (k + 4) + error (k + 4)) -
      (partialSum (k + 4) - error (k + 4)) ≤ 1 / (2 : ℝ) ^ (k + 1) := by
  have h := error_le (k + 3)
  have power : (2 : ℝ) ^ k > 0 := by positivity
  simp only [show k + 3 + 1 = k + 4 by omega, pow_add] at h ⊢
  norm_num at h ⊢
  field_simp at h ⊢
  nlinarith

end Hex.Interval.ExpOne
