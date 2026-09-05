/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexTruncatedSeries.Precision

public section

/-!
The common precision-doubling driver for truncated-series Newton algorithms.

The driver recurses structurally on the number of doublings and passes the
target precision to every step.  There is no fuel-exhaustion branch.  `steps`
is the tight ceiling of the binary logarithm needed to reach the requested
precision from precision one.
-/

namespace Hex.TSeries

universe u

variable {R : Type u} {n : Nat}

/-- Apply a Newton step `k` times, passing target precision `2^(j+1)` at
iteration `j`. -/
@[expose]
def newton (step : TSeries R n → Nat → TSeries R n)
    (init : TSeries R n) : Nat → TSeries R n
  | 0 => init
  | j + 1 => step (newton step init j) (2 ^ (j + 1))

/-- Number of doublings needed to reach precision `n` from precision one. -/
@[expose]
def steps (n : Nat) : Nat :=
  if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- Increasing the requested precision cannot decrease the Newton step count. -/
theorem steps_mono {m n : Nat} (h : m ≤ n) : steps m ≤ steps n := by
  have log2_mono {a b : Nat} (hab : a ≤ b) : a.log2 ≤ b.log2 := by
    by_cases ha : a = 0
    · subst a
      simp
    · have hb : b ≠ 0 := by omega
      rw [Nat.le_log2 hb]
      exact Nat.le_trans (Nat.log2_self_le ha) hab
  unfold steps
  by_cases hm : m ≤ 1
  · rw [ite_eq_left hm]
    omega
  · have hn : ¬n ≤ 1 := by omega
    rw [ite_eq_right hm, ite_eq_right hn]
    exact Nat.add_le_add_right (log2_mono (Nat.sub_le_sub_right h 1)) 1

/-- If every Newton stage preserves the prefix established by the preceding
stage, any later iterate agrees with an earlier iterate throughout that
prefix. -/
theorem newton_agree [Zero R] (step : TSeries R n → Nat → TSeries R n)
    (init : TSeries R n)
    (stable : ∀ j, Agree (2 ^ j) (newton step init (j + 1))
      (newton step init j)) {j k : Nat} (hjk : j ≤ k) :
    Agree (2 ^ j) (newton step init k) (newton step init j) := by
  induction k generalizing j with
  | zero =>
      have hj : j = 0 := by omega
      subst j
      exact Agree.refl 1 (newton step init 0)
  | succ k ih =>
      by_cases hj : j = k + 1
      · subst j
        exact Agree.refl (2 ^ (k + 1)) (newton step init (k + 1))
      · have hjk' : j ≤ k := by omega
        exact ((stable k).mono
          (Nat.pow_le_pow_right (by decide : 0 < 2) hjk')).trans (ih hjk')

/-- The Newton step count reaches every requested coefficient. -/
theorem two_pow_steps_ge (n : Nat) : n ≤ 2 ^ steps n := by
  unfold steps
  split
  · simp
    omega
  · have hlt : n - 1 < 2 ^ ((n - 1).log2 + 1) := Nat.lt_log2_self
    omega

end Hex.TSeries
