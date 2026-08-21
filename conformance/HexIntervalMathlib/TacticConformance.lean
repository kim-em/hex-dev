/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Tactic

/-!
# Supported arithmetic tactic conformance

The public Meta bridge parses local integer cuts, reifies a shared arithmetic
expression, authenticates the supported chronology, and independently emits an
ordinary kernel proof. These canaries cover strict and closed cuts, singleton
equality, conjunction, transactional rejection, and the diagnostic surface.
-/

namespace Hex.IntervalMathlib.TacticConformance

example {x : ℝ} (lower : 1 ≤ x) (upper : x ≤ 2) : 2 ≤ x + x := by
  interval

example {x : ℝ} (lower : 1 ≤ x) (upper : x ≤ 2) : x + x ≤ 4 := by
  interval

example {x : ℝ} (lower : 1 < x) (upper : x < 2) : 2 < x + x ∧ x + x < 4 := by
  interval

example {x : ℝ} (lower : 1 ≤ x) (upper : x ≤ 2) : 0 < x ∧ 1 ≤ x := by
  interval

example {x : ℝ} (lower : -2 ≤ x) (upper : x ≤ -1) : -4 ≤ x + x ∧ |x| ≤ 2 := by
  interval

example {x y : ℝ} (hx₀ : 1 ≤ x) (hx₁ : x ≤ 2) (hy₀ : 3 ≤ y) (hy₁ : y ≤ 4) :
    -3 ≤ x - y ∧ x * y ≤ 8 := by
  interval

example : (0 : ℝ) = 0 := by
  interval


example : 0 = (0 : ℝ) := by
  interval

example {x : ℝ} (singleton : x = 1) : x = 1 := by
  interval

example {x : ℝ} (singleton : 1 = x) : 1 = x := by
  interval

example {x : ℝ} (lower : -2 ≤ x) (upper : x ≤ 2) : x ^ 2 ≤ 4 := by
  interval

example {x y : ℝ} (hx₀ : 1 ≤ x) (hx₁ : x ≤ 2) (hy₀ : 3 ≤ y) (hy₁ : y ≤ 4) :
    1 ≤ min x y ∧ max x y ≤ 4 := by
  interval

example {x : ℝ} (singleton : x = 2) : 0 ≤ x⁻¹ := by
  interval

example {x y : ℝ} (hx : x = 4) (hy : y = 2) : x / y = 2 := by
  interval

example {x : ℝ} (lower : 1 ≤ x) (upper : x ≤ 2) : 2 ≤ x + x := by
  interval?

set_option linter.unusedTactic false in
example {x : ℝ} (_lower : 1 ≤ x) (_upper : x ≤ 2) : True := by
  interval_bound x + x
  trivial

example {x : ℝ} (_lower : 1 ≤ x) (_upper : x ≤ 2) : Real.sin x ≤ 1 := by
  fail_if_success interval
  exact Real.sin_le_one x

example {x : ℝ} (_lower : 1 ≤ x) (impossible : False) : x ≤ 2 := by
  fail_if_success interval
  exact impossible.elim

set_option linter.unusedTactic false in
example : True := by
  run_tac do
    let config : Hex.Interval.Frontend.Config :=
      { Hex.Interval.Tactic.defaultConfig with
        reify := { Hex.Interval.Tactic.defaultConfig.reify with maxNodes := 0 } }
    let zero ← Hex.Interval.Tactic.realIntCast 0
    let accepted ← try
      let _ ← Hex.Interval.Tactic.deriveBound config zero
      pure true
    catch _ => pure false
    if accepted then
      throwError "zero-node tactic configuration accepted one constant node"
  trivial

set_option linter.unusedTactic false in
example : True := by
  run_tac do
    let rule := Hex.Interval.Tactic.defaultConfig.rule
    let config : Hex.Interval.Frontend.Config :=
      { Hex.Interval.Tactic.defaultConfig with
        rule := { rule with
          constant := .ofInt 2
          precisionLimits := { rule.precisionLimits with maxTemporaryBits := 0 } } }
    let two ← Hex.Interval.Tactic.realIntCast 2
    let inverse ← Lean.Meta.mkAppM ``Inv.inv #[two]
    let accepted ← try
      let _ ← Hex.Interval.Tactic.deriveBound config inverse
      pure true
    catch _ => pure false
    if accepted then
      throwError "precision-starved reciprocal recipe was accepted"
  trivial

theorem ordinary {x : ℝ} (lower : 1 ≤ x) (upper : x ≤ 2) :
    2 ≤ x + x ∧ x + x ≤ 4 := by
  interval

#print axioms ordinary

end Hex.IntervalMathlib.TacticConformance
