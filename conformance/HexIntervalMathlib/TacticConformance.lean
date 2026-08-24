/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Tactic

/-!
# Supported arithmetic tactic conformance

The public Meta bridge parses local integer cuts, reifies a shared arithmetic
expression, runs its typed runtime controller to a settled target, and emits
the sealed chronology as an ordinary kernel proof before closing the exact
caller sources and expression semantics. These canaries cover strict and
closed cuts, singleton equality, conjunction, transactional rejection, and the
diagnostic surface.
-/

namespace Hex.IntervalMathlib.TacticConformance

set_option linter.unusedTactic false in
example : True := by
  run_tac do
    let check (raw : Hex.Interval.Raw) (expected : String) : Lean.Meta.MetaM Unit := do
      let rendered := Hex.Interval.Tactic.describeSelectedCuts raw
      unless rendered == expected do
        throwError "selected-cut diagnostic changed: expected {expected}, got {rendered}"
    check (.bounds (.finite (.ofInt 2) false) (.finite (.ofInt 4) false))
      "selected cuts: 2 ≤ e and e ≤ 4"
    check (.bounds (.finite (.ofInt 2) true) (.finite (.ofInt 4) true))
      "selected cuts: 2 < e and e < 4"
    check (.bounds (.finite (.ofInt 2) true) .unbounded)
      "selected lower cut: 2 < e"
    check (.bounds .unbounded (.finite (.ofInt 4) true))
      "selected upper cut: e < 4"
    check (.bounds .unbounded .unbounded) "no finite selected cut"
    check .empty "no selected cut (empty result)"
  trivial

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

theorem reciprocalSum {x : ℝ} (singleton : x = 2) : x⁻¹ + x⁻¹ = 1 := by
  interval

-- Twelve nested arithmetic layers become twenty-four internal arithmetic and
-- regularization rows, remaining below the documented term-depth cap 32.
example {x : ℝ} (singleton : x = 1) :
    -(-(-(-(-(-(-(-(-(-(-(-x))))))))))) = 1 := by
  interval

example {x y : ℝ} (hx : x = 4) (hy : y = 2) : x / y = 2 := by
  interval

-- A scientific decimal is not an integer source cut and must not displace the
-- later authenticated integer cut for the same source expression.
example {x : ℝ} (_poison : (1.5 : ℝ) ≤ x) (valid : 1 ≤ x) : 1 ≤ x := by
  interval

example {x : ℝ} (lower : 1 ≤ x) (upper : x ≤ 2) : 2 ≤ x + x := by
  interval?

set_option linter.unusedTactic false in
example {x : ℝ} (_lower : 1 ≤ x) (_upper : x ≤ 2) : True := by
  interval_bound x + x
  guard_target = True
  trivial

example {x : ℝ} (_lower : 1 ≤ x) (_upper : x ≤ 2) : Real.sin x ≤ 1 := by
  fail_if_success interval
  exact Real.sin_le_one x

example {x : ℝ} (_lower : 1 ≤ x) (impossible : False) : x ≤ 2 := by
  fail_if_success interval
  exact impossible.elim

example {x : ℝ} (_lower : 1 ≤ x) : Real.sin x ≤ 1 := by
  fail_if_success interval?
  exact Real.sin_le_one x

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example {x : ℝ} : True := by
  run_tac do
    let config : Hex.Interval.Frontend.Config :=
      { Hex.Interval.Tactic.defaultConfig with
        reify := { Hex.Interval.Tactic.defaultConfig.reify with maxNodes := 0 } }
    let source ← Lean.Meta.getFVarFromUserName `x
    let failure ← try
      let _ ← Hex.Interval.Tactic.deriveBound config source
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    match failure with
    | none => throwError "zero-node tactic configuration accepted one constant node"
    | some message =>
        unless message ==
            "interval: reification failed: Hex.Interval.Frontend.Error.nodeLimit" do
          throwError "zero-node guard failed at the wrong boundary: {message}"
  trivial

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example {x : ℝ} (source : x = 2) : True := by
  run_tac do
    let x ← Lean.Meta.getFVarFromUserName `x
    let sum ← Lean.Meta.mkAppM ``HAdd.hAdd #[x, x]
    let withChronology (limit : Nat) : Hex.Interval.Frontend.Config :=
      { Hex.Interval.Tactic.defaultConfig with
        proof := { Hex.Interval.Tactic.defaultConfig.proof with
          maxChronology := limit } }
    let _ ← Hex.Interval.Tactic.deriveBound (withChronology 2) sum
    let failure ← try
      let _ ← Hex.Interval.Tactic.deriveBound (withChronology 1) sum
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    match failure with
    | none => throwError "one-short runtime chronology was accepted"
    | some message =>
        unless message.contains "controller run failed" do
          throwError "one-short chronology failed at the wrong boundary: {message}"
  trivial

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example {x : ℝ} (source : x = 2) : True := by
  run_tac do
    let rule := Hex.Interval.Tactic.defaultConfig.rule
    let config : Hex.Interval.Frontend.Config :=
      { Hex.Interval.Tactic.defaultConfig with
        rule := { rule with
          precisionLimits := { rule.precisionLimits with maxTemporaryBits := 0 } } }
    let x ← Lean.Meta.getFVarFromUserName `x
    let inverse ← Lean.Meta.mkAppM ``Inv.inv #[x]
    let failure ← try
      let _ ← Hex.Interval.Tactic.deriveBound config inverse
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    match failure with
    | none => throwError "precision-starved reciprocal recipe was accepted"
    | some message =>
        unless message ==
            "interval: controller stopped with 1 live offers and 2 pending actions" do
          throwError "precision-starved reciprocal failed at the wrong boundary: {message}"
  trivial

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example {x : ℝ} (lower : 1 ≤ x) (upper : x ≤ 2) : True := by
  run_tac do
    let x ← Lean.Meta.getFVarFromUserName `x
    let one ← Lean.Elab.Tactic.elabTerm (← `(term| (1 : ℝ))) (some (Lean.mkConst ``Real))
    let target ← Lean.Meta.mkAppM ``LE.le #[x, one]
    let failure ← try
      let _ ← Hex.Interval.Tactic.proveTarget Hex.Interval.Tactic.defaultConfig target
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    match failure with
    | none => throwError "incompatible target was accepted"
    | some message =>
        unless message == "interval: derived endpoint does not prove the requested target" do
          throwError "incompatible target produced the wrong diagnostic: {message}"
  trivial

set_option linter.unusedTactic false in
set_option linter.unusedVariables false in
example {x : ℝ} (source : x = 2) : True := by
  run_tac do
    let x ← Lean.Meta.getFVarFromUserName `x
    let one ← Lean.Elab.Tactic.elabTerm (← `(term| (1 : ℝ))) (some (Lean.mkConst ``Real))
    let target ← Lean.Meta.mkAppM ``Eq #[x, one]
    let failure ← try
      let _ ← Hex.Interval.Tactic.proveTarget Hex.Interval.Tactic.defaultConfig target
      pure none
    catch error => pure (some (← error.toMessageData.toString))
    match failure with
    | none => throwError "false equality target was accepted"
    | some message =>
        unless message == "interval: derived endpoint does not prove the requested target" do
          throwError "false equality produced the wrong diagnostic: {message}"
  trivial

theorem ordinary {x : ℝ} (lower : 1 ≤ x) (upper : x ≤ 2) :
    2 ≤ x + x ∧ x + x ≤ 4 := by
  interval

/--
info: 'Hex.IntervalMathlib.TacticConformance.ordinary' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms ordinary

/--
info: 'Hex.IntervalMathlib.TacticConformance.reciprocalSum' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms reciprocalSum

end Hex.IntervalMathlib.TacticConformance
