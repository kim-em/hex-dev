import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic

/-!
Finite real sum inequalities used by the BHKS bad-vector bounds.

Mathlib already provides `Finset.sum_mul_sq_le_sq_mul_sq`; this module adds
the bounded-column corollary used by the BHKS auxiliary-polynomial norm bound.
-/

namespace Finset

open scoped BigOperators

/--
Finite Cauchy-Schwarz with a uniform square bound on the second factor.
-/
theorem sum_mul_sq_le_sq_mul_card_mul_bound
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (a b : ι → ℝ) (B : ℝ)
    (hB : ∀ i ∈ s, (b i) ^ 2 ≤ B) :
    (∑ i ∈ s, a i * b i) ^ 2 ≤
      (∑ i ∈ s, (a i) ^ 2) * ((s.card : ℝ) * B) := by
  have hcs := sum_mul_sq_le_sq_mul_sq s a b
  have hb :
      (∑ i ∈ s, (b i) ^ 2) ≤ (s.card : ℝ) * B := by
    calc
      (∑ i ∈ s, (b i) ^ 2) ≤ ∑ _i ∈ s, B := by
        exact sum_le_sum hB
      _ = (s.card : ℝ) * B := by
        simp [mul_comm]
  have ha_nonneg : 0 ≤ ∑ i ∈ s, (a i) ^ 2 := by
    exact sum_nonneg fun i _ => sq_nonneg (a i)
  exact hcs.trans (mul_le_mul_of_nonneg_left hb ha_nonneg)

end Finset
