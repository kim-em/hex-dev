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

/-- The Newton step count reaches every requested coefficient. -/
theorem two_pow_steps_ge (n : Nat) : n ≤ 2 ^ steps n := by
  unfold steps
  split
  · simp
    omega
  · have hlt : n - 1 < 2 ^ ((n - 1).log2 + 1) := Nat.lt_log2_self
    omega

end Hex.TSeries
