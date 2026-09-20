/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRealFormulaMathlib.Reify
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Lean.Elab.Command

/-! Reification tests check complete proofs, binder identity, and explicit parameters. -/

open Lean Meta Qq Hex.RealFormula

private meta unsafe def checkClosed (source : Expr) (binders : Nat) : MetaM Unit := do
  let r ← Reify.reify! source
  check r.proof
  unless r.binders.size == binders do throwError "incorrect binder map"
  if r.proof.hasFVar || r.source.hasFVar || r.formula.hasFVar then
    throwError "a closed result contains an escaped local constant"
  let formula ← evalExpr (Prenex 0) q(Prenex 0) r.formula
  unless formula.toView.prefix.toArray == r.prefixMap.map (·.2) do
    throwError "executable formula and binder map disagree"
  if binders == 0 then
    unless r.qfProof?.isSome do throwError "quantifier-free result missing"
  else
    unless r.qfProof?.isNone do throwError "quantified input reported quantifier-free"

run_meta do
  checkClosed q(True) 0
  checkClosed q((3 : ℝ) / -2 < 0) 0
  checkClosed q(∃ x : ℝ, x * x = 2) 1
  checkClosed q(∀ x : ℝ, ∃ y : ℝ, x = y) 2
  checkClosed q(∀ x : ℝ, x = x ∧ ∃ x : ℝ, x > 0) 2
  checkClosed q((∃ x : ℝ, x < 0) ∧ (∀ x : ℝ, x = x)) 2
  checkClosed q((∃ x : ℝ, x = 0) ↔ (∀ x : ℝ, x ≤ 1)) 2
  checkClosed q(¬ ∃ x : ℝ, x > 0 ∧ x ≤ 0) 1
  checkClosed q((3 : ℝ) ≠ 4 ∧ (1 : ℝ) ≤ 2) 0
  checkClosed q((1.5 : ℝ) > 0 ∧ ((-3 / 2 : ℚ) : ℝ) < 0) 0
  checkClosed q(∀ x ∈ Set.Ioc (0 : ℝ) (3 / 2), x ≥ 0) 1
  checkClosed q(∃ x ∈ Set.Icc (-1 : ℝ) 2, x < 0) 1

run_meta do
  withLocalDeclD `a q(ℝ) fun a => do
    let a : Q(ℝ) := a
    let tutorial ← Reify.reify! q(∃ x : ℝ, x ^ 2 / 2 + $a * x ≤ 3 / 2) #[a]
    checkWithKernel tutorial.proof
    unless tutorial.sealedMap == #[1, 0] || tutorial.sealedMap == #[0, 1] do
      throwError "tutorial coordinate map contains an unexpected atom"
    pure ()

run_meta do
  withLocalDeclD `a q(ℝ) fun a => do
    let a : Q(ℝ) := a
    let source := q(∀ x : ℝ, x > $a → x / 2 ≥ $a / 3)
    let r ← Reify.reify! source #[a]
    check r.proof
    if r.proof.hasFVar || r.source.hasFVar then
      throwError "proof was not generalized over the free valuation"
    unless r.parameters == #[a] do throwError "parameter order changed"
    unless r.prefixMap.size == 1 do throwError "incorrect normalized prefix"
    withLocalDeclD `h q($a > 0) fun h => do
      let r ← Reify.reify! q($a ≥ 0) #[a] #[h]
      check r.proof
      if r.proof.hasFVar then throwError "selected assumption became a hidden hypothesis"
      pure ()

run_meta do
  let r ← Reify.reify! q(∀ x : ℝ, x > 0 → ∃ x : ℝ, x < 0)
  unless r.sealedMap == #[0, 1] do throwError "shadowed binders were identified"
  unless r.prefixMap == #[(0, .forallReal), (1, .existsReal)] do
    throwError "binder order was changed"
  let r ← Reify.reify! q((∃ x : ℝ, x = 0) ↔ (∀ y : ℝ, y ≤ 1))
  unless r.prefixMap == #[(0, .forallReal), (1, .forallReal),
      (1, .existsReal), (0, .existsReal)] do
    throwError "biconditional binder copies lost their identities"

private meta def expectUnsupported (source : Expr) (params : Array Expr := #[]) : MetaM Unit := do
  match ← Reify.reify source params with
  | .error ⟨_, .unsupported _ _⟩ => pure ()
  | .error d => throwError "unexpected decline: {d.reason.toMessageData}"
  | .ok _ => throwError "unsupported input was accepted"

run_meta do
  expectUnsupported q((1 : Nat) < 2)
  expectUnsupported q(∀ _x : Nat, True)
  expectUnsupported q(∀ x : ℝ, ∀ _y : { y : ℝ // y > x }, True)
  withLocalDeclD `x q(ℝ) fun x => do
    let x : Q(ℝ) := x
    expectUnsupported q(Real.sin $x > 0) #[x]
    expectUnsupported q(1 / $x = 0) #[x]
    expectUnsupported q($x / 0 = 0) #[x]
    expectUnsupported q($x > 0) -- Undeclared free parameter.
    expectUnsupported q($x ∈ setOf (fun _ : ℝ => True)) #[x]
    withLocalDeclD `s q(Set ℝ) fun s => do
      let s : Q(Set ℝ) := s
      expectUnsupported q($x ∈ $s) #[x]
    withLocalDeclD `k q(ℕ) fun k => do
      let k : Q(ℕ) := k
      expectUnsupported q($x ^ $k = 0) #[x]
  withLetDecl `a q(ℝ) q((1 : ℝ)) fun a => do
    let a : Q(ℝ) := a
    expectUnsupported q($a = 1) #[a]
  withLocalDeclD `P q(ℝ → Prop) fun p => do
    let p : Q(ℝ → Prop) := p
    expectUnsupported q(∃ x : ℝ, $p x)

private meta def expectBudget (source : Expr) (params : Array Expr) (cfg : Reify.Config)
    (dimension : Hex.Reflect.BudgetDimension) : MetaM Unit := do
  match ← Reify.reify source params #[] cfg with
  | .error ⟨_, .budget b⟩ =>
    unless b.dimension == dimension do throwError "wrong budget dimension"
  | .error ⟨_, .providerDeclined (.budgetExhausted b) _ _⟩ =>
    unless b.dimension == dimension do throwError "wrong provider budget dimension"
  | .error d => throwError "unexpected decline: {d.reason.toMessageData}"
  | .ok _ => throwError "budget-exceeding input was accepted"

run_meta do
  let _ ← Reify.reify! q(True) #[] #[]
    { ring := { budget := Hex.Reflect.Budget.default.set .sourceNodes 1 } }
  expectBudget q(True) #[] { ring := { budget := Hex.Reflect.Budget.default.set .sourceNodes 0 } } .sourceNodes
  expectBudget q(True) #[] { ring := { budget := Hex.Reflect.Budget.default.set .proofNodes 0 } } .proofNodes
  expectBudget q((12345 : ℝ) < 0) #[] { ring := { budget := Hex.Reflect.Budget.default.set .coefficientBits 4 } } .coefficientBits
  withLocalDeclD `x q(ℝ) fun x => do
    let x : Q(ℝ) := x
    expectBudget q($x ^ 3 = 0) #[x] { ring := { budget := Hex.Reflect.Budget.default.set .exponent 2 } } .exponent
    expectBudget q(($x + 1) ^ 3 = 0) #[x] { ring := { budget := Hex.Reflect.Budget.default.set .terms 1 } } .terms
  expectBudget q(((2 ^ 100 : ℚ) : ℝ) > 0) #[]
    { ring := { budget := Hex.Reflect.Budget.default.set .exponent 10 } } .exponent
  expectBudget q((1e100 : ℝ) > 0) #[]
    { ring := { budget := Hex.Reflect.Budget.default.set .exponent 10 } } .exponent
  let .error ⟨_, .formulaBudget _ _⟩ ← Reify.reify q(True ∧ False) #[] #[] { formulaNodes := 2 }
    | throwError "formula expansion budget was ignored"
  pure ()
