/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients
public import Mathlib.Analysis.Real.Pi.Bounds
public section

set_option debug.skipKernelTC false
set_option Elab.async false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Hex.RCF.PolynomialTactic
open RealCoefficients Hex.OrderedFn.Oracle

/-- Caller-supplied fixed bounds; no requested-width or convergence claim. -/
@[expose] def bounds : Bounds :=
  ⟨mkRat 314159265358979323846 100000000000000000000,
    mkRat 314159265358979323847 100000000000000000000, by decide⟩

@[expose] def registration : Registration Real.pi where
  version := 1
  approximation _ := bounds
  containment _ _ := by
    have lower := Real.pi_gt_d20.le
    have upper := Real.pi_lt_d20.le
    norm_num at lower upper
    norm_num [Contains, bounds, mkRat]
    exact ⟨lower, upper⟩

attribute [rcf_constant] registration

/-- The ordinary tactic constructs and checks the complete polynomial cells. -/
theorem root : ∃ x : ℝ, x ^ 2 = Real.pi ∧ 1 < x ∧ x < 2 := by
  rcf

theorem repeated : ∃ x : ℝ, (x ^ 2 - Real.pi) ^ 2 = 0 ∧ 1 < x ∧ x < 2 := by
  rcf

theorem interval : ∃ x ∈ Set.Ioc (1 : ℝ) 2, x ^ 2 = Real.pi := by
  rcf

/-- error: rcf: real-coefficient statement is false -/
#guard_msgs in
example : ∀ x : ℝ, (x ^ 2 - Real.pi) ^ 2 < 0 := by rcf

/-- error: rcf: polynomial root/sign search exhausted supplied bounds or isolation depth -/
#guard_msgs in
set_option rcf.algebraic.directDepth 0 in
example : ∃ x : ℝ, x ^ 2 = Real.pi ∧ 1 < x ∧ x < 2 := by rcf

/-- error: rcf: original closed divisor is zero -/
#guard_msgs in
example : ∃ x : ℝ, x ^ 2 = Real.pi ∧ 0 / (Real.pi - Real.pi) = 0 := by rcf

#print axioms root
#print axioms repeated
#print axioms interval
end Hex.RCF.PolynomialTactic
