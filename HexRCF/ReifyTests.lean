/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexRCF.Tactic

public section

namespace Hex.RCF

/-! # Quantifier shapes -/

example : ∀ x : ℝ, x ^ 2 ≥ 0 := by
  rcf

example : ∃ x : ℝ, x = 0 := by
  rcf

example : ∀ _x : ℝ, True := by
  rcf

example : ∃ _x : ℝ, True := by
  rcf

example : ∀ _x : ℝ, (1 : ℝ) > 0 := by
  rcf

example : ∀ x : ℝ, False → x = x := by
  rcf

example : (∀ x : ℝ, x ^ 2 ≥ 0) ∧ True := by
  constructor
  rcf
  trivial

example : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → x ≤ 1 := by
  rcf

example : ∃ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 ∧ x = 1 := by
  rcf

/-! # Comparisons, connectives, and rational normalization -/

example : ∀ x : ℝ,
    (x < 0 ∨ x ≥ 0) ∧ (x ≤ 0 ∨ x > 0) ∧ (x = 0 ∨ x ≠ 0) := by
  rcf

example : ∀ x : ℝ, ¬(x < 0 ∧ x ≥ 0) := by
  rcf

example : ∀ x : ℝ, 0 ≤ x → x ^ 3 + x ≥ 0 := by
  rcf

example : ∀ x : ℝ, 0 < x → x ^ 2 + 1 ≥ 2 * x := by
  rcf

example : ∀ x : ℝ, x ^ 2 ≤ 1 → x ^ 4 - x ^ 2 ≤ 0 := by
  rcf

example : ∀ x : ℝ, x ^ 2 + (1 : ℝ) / 2 > 0 := by
  rcf

example : ∀ x : ℝ, x ^ 2 / 3 + 1 / 5 > 0 := by
  rcf

example : ∀ x : ℝ, x ^ 2 + 2 * x + 2 ≠ 0 := by
  rcf

/-! # Roots and half-open endpoint ownership -/

example : ∃ x : ℝ, x ^ 3 - x - 1 = 0 ∧ 1 < x ∧ x < 2 := by
  rcf

example : ∃ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 2 ∧ x ^ 3 - x - 1 = 0 := by
  rcf

example : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → x > 0 := by
  rcf

example : ∃ x : ℝ, x ∈ Set.Ioc ((1 : ℝ) / 2) 1 ∧ x = 1 := by
  rcf

example : ∀ x : ℝ, x ∈ Set.Ioc ((-1 : ℝ) / 2) 0 → x ≤ 0 := by
  rcf

example : ∀ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 1 → x ^ 2 < 0 := by
  rcf

example : ∀ x : ℝ, x ∈ Set.Ioc (2 : ℝ) 1 → x ^ 2 < 0 := by
  rcf

/-! # False verdicts and clean fall-through -/

/-- error: rcf: the universal sentence is false on the root cell isolated in (-2, 2] -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 > 0 := by
  rcf

/--
error: rcf: the existential sentence is false. Every relevant decomposition
cell was checked and found false, so there is no witness
-/
#guard_msgs in
example : ∃ x : ℝ, x ^ 2 + 1 = 0 := by
  rcf

/--
error: rcf: the existential sentence is false. Every relevant decomposition
cell was checked and found false, so there is no witness
-/
#guard_msgs in
example : ∃ x : ℝ, x ∈ Set.Ioc (1 : ℝ) 1 ∧ x = x := by
  rcf

/--
error: rcf: the existential sentence is false. Every relevant decomposition
cell was checked and found false, so there is no witness
-/
#guard_msgs in
example : ∃ x : ℝ, x ∈ Set.Ioc (2 : ℝ) 1 ∧ x = x := by
  rcf

example : (0 : ℝ) < 1 := by
  first | rcf | norm_num

/-! # Out-of-fragment diagnostics -/

variable (a : ℝ)

/--
error: rcf: symbolic or non-rational coefficient
  a
-/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 + a > 0 := by
  rcf

/-- error: rcf: more than one variable or a nested quantifier is unsupported -/
#guard_msgs in
example : ∀ a x : ℝ, a * x ^ 2 + 1 > 0 := by
  rcf

/-- error: rcf: nested quantifiers are unsupported -/
#guard_msgs in
example : ∀ x : ℝ, ∃ y : ℝ, x = y := by
  rcf

/-- error: rcf: more than one variable or a nested quantifier is unsupported -/
#guard_msgs in
example : ∀ x : ℝ, ∀ _y : ℝ, x = x := by
  rcf

/-- error: rcf: non-polynomial real functions such as sin and exp are unsupported -/
#guard_msgs in
example : ∀ x : ℝ, Real.sin x = 0 := by
  rcf

/-- error: rcf: division by an expression containing the variable is not polynomial. Clear denominators by hand -/
#guard_msgs in
example : ∀ x : ℝ, x + 1 / x ≥ 2 := by
  rcf

/--
error: rcf: Set.Icc quantifiers are unsupported. Rewrite
  ∀ x ∈ Set.Icc a b, φ x
as
  (a ≤ b → φ a) ∧ ∀ x ∈ Set.Ioc a b, φ x
-/
#guard_msgs in
example : ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 → x ≤ 1 := by
  rcf

/--
error: rcf: Set.Icc quantifiers are unsupported. Rewrite
  ∃ x ∈ Set.Icc a b, φ x
as
  a ≤ b ∧ (φ a ∨ ∃ x ∈ Set.Ioc a b, φ x)
-/
#guard_msgs in
example : ∃ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 ∧ x = x := by
  rcf

/--
error: rcf: Set.Ioo quantifiers are unsupported. Rewrite
  ∀ x ∈ Set.Ioo a b, φ x
as
  ∀ x ∈ Set.Ioc a b, x ≠ b → φ x
-/
#guard_msgs in
example : ∀ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 → x ≤ 1 := by
  rcf

/--
error: rcf: Set.Ioo quantifiers are unsupported. Rewrite
  ∃ x ∈ Set.Ioo a b, φ x
as
  ∃ x ∈ Set.Ioc a b, φ x ∧ x ≠ b
-/
#guard_msgs in
example : ∃ x : ℝ, x ∈ Set.Ioo (0 : ℝ) 1 ∧ x = x := by
  rcf

/-- error: rcf: bounded endpoints must be dyadic rationals. Got 1/3 -/
#guard_msgs in
example : ∀ x : ℝ, x ∈ Set.Ioc ((1 : ℝ) / 3) 1 → x ≤ 1 := by
  rcf

end Hex.RCF
