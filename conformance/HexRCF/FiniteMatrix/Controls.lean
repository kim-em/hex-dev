/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteMatrix.Quote
open Hex Hex.RealClosure.Algebraic Hex.RealClosure.Algebraic.KernelReplay
open Lean Meta Elab Command
namespace Hex.RCF.RealCoefficients.FiniteMatrixTests.Controls
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
private def requireRefusal (label : String) (action : MetaM Expr) (quiet : Bool := false) : MetaM Unit := do
  let before ← getMCtx
  let env ← getEnv
  let refused ← try
    let _ ← action
    pure false
  catch error =>
    unless quiet do logInfo m!"{label}: {error.toMessageData}"
    pure true
  unless refused do throwError "altered source accepted: {label}"
  let after ← getMCtx
  unless env.constants.map₂.toList.length == (← getEnv).constants.map₂.toList.length do
    throwError "failure changed the environment: {label}"
  unless after.mvarCounter == before.mvarCounter && after.lmvarCounter == before.lmvarCounter &&
      after.depth == before.depth && after.eAssignment.toList == before.eAssignment.toList &&
      after.lAssignment.toList == before.lAssignment.toList do
    throwError "failure changed metavariable state: {label}"
elab "#finite_quote_controls" : command => liftTermElabM do
  let queries ← mkAppM ``Schema.queries #[mkConst ``Packings.facts]
  let checker ← mkAppM ``Hex.RCF.RealCoefficients.FiniteSigns.check
    #[mkConst ``FiniteJoint.next, ← mkListLit (← inferType (mkConst ``FiniteTower.generator)) [],
      queries, mkConst ``Selected.canonical, mkConst ``Schema.formula]
  let unit ← mkAppM ``Hex.RealClosure.Transport.Closed.read_one #[mkConst ``Semantics.closed]
  let bind ← mkAppM ``Binding.bind #[mkConst ``Packings.facts]
  let replay ← mkAppM ``Data.replay #[toExpr false]
  let quote (target checker accepted identity : Expr) := Hex.RCF.RealCoefficients.FiniteQuote.finish
    target checker accepted (mkConst ``Semantics.read) (mkConst ``Semantics.zero)
    unit (mkConst ``Data.descriptor) replay
    (mkConst ``Binding.valuation) bind identity
  let original ← Term.elabType (← `(∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2))
  let wrongQuantifier ← Term.elabType (← `(∀ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2))
  let missing ← Term.elabType (← `(∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x / (2 - 1) ∧ x < 2))
  let cancelled ← Term.elabType (← `(∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 ∧
    0 / (Real.sqrt 2 - Real.sqrt 2) = 0))
  Term.synthesizeSyntheticMVarsNoPostponing
  let original ← instantiateMVars original
  let accepted ← mkAppM ``Data.accepted #[toExpr false]
  let identity := mkConst ``Binding.valuation_eq
  let deferred ← mkFreshExprMVar (← inferType checker)
  requireRefusal "unresolved checker" (quote original deferred accepted identity)
  requireRefusal "partial checker" (quote original checker.getAppFn accepted identity)
  requireRefusal "checker head" (quote original (mkConst ``Bool.true) accepted identity)
  requireRefusal "wrong acceptance proof" (quote original checker (mkConst ``True.intro) identity)
  requireRefusal "wrong quantifier" (quote (← instantiateMVars wrongQuantifier) checker accepted identity)
  requireRefusal "missing divisor" (quote (← instantiateMVars missing) checker accepted identity)
  requireRefusal "cancelled zero divisor" (quote (← instantiateMVars cancelled) checker accepted identity)
  requireRefusal "wrong valuation identity" (quote original checker accepted (mkConst ``True.intro))
  let falseChecker ← mkAppM ``FiniteSigns.check
    #[mkConst ``FiniteJoint.next, ← mkListLit (← inferType (mkConst ``FiniteTower.generator)) [],
      queries, mkConst ``Selected.canonical, ← mkAppM ``Hex.RealFormula.QF.not #[mkConst ``Schema.formula]]
  requireRefusal "false point" (quote original falseChecker (mkConst ``Data.falseAccepted) identity)
  let guardedChecker ← mkAppM ``FiniteSigns.check
    #[mkConst ``FiniteJoint.next,
      ← mkAppM ``Schema.guards #[toExpr true, mkConst ``Packings.facts], queries,
      ← mkAppM ``Data.selected #[toExpr true], mkConst ``Schema.formula]
  let guardedAccepted ← mkAppM ``Data.accepted #[toExpr true]
  let guardedReplay ← mkAppM ``Data.replay #[toExpr true]
  let quoteGuarded (target : Expr) (identities : Array Expr) := FiniteQuote.finish
    target guardedChecker guardedAccepted (mkConst ``Semantics.read) (mkConst ``Semantics.zero)
    unit (mkConst ``Data.descriptor) guardedReplay (mkConst ``Binding.valuation) bind identity identities
  let missing ← instantiateMVars missing
  requireRefusal "popped identity" (quoteGuarded missing #[])
  requireRefusal "wrong guard identity" (quoteGuarded missing #[mkConst ``Semantics.zero])
  requireRefusal "extra guard identity" (quoteGuarded missing #[mkConst ``Data.guardIdentity, mkConst ``Data.guardIdentity])
  requireRefusal "extra guard" (quoteGuarded original #[])
/--
info: unresolved checker: rcf: FiniteQuote.checker contains unresolved metavariables
---
info: partial checker: rcf: incorrect finite-sign checker arity
---
info: checker head: rcf: expected the canonical finite-sign checker
---
info: wrong acceptance proof: rcf: handler FiniteQuote.accepted proposed a proof of a different goal
---
info: wrong quantifier: rcf: checked formula has a different source syntax
---
info: missing divisor: rcf: finite checker has a different original divisor identity count
---
info: cancelled zero divisor: rcf: finite checker has a different original divisor identity count
---
info: wrong valuation identity: rcf: handler FiniteQuote.valuationIdentity proposed a proof of a different goal
---
info: false point: rcf: handler FiniteQuote.accepted proposed a proof of a different goal
---
info: popped identity: rcf: finite checker has a different original divisor identity count
---
info: wrong guard identity: rcf: handler FiniteQuote.guardIdentity proposed a proof of a different goal
---
info: extra guard identity: rcf: finite checker has a different original divisor identity count
---
info: extra guard: rcf: finite checker has a different original divisor count
-/
#guard_msgs (whitespace := lax) in
#finite_quote_controls

elab "#finite_formula_controls" : command => liftTermElabM do
  for sourceSyntax in [← `(∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x ≤ 2),
      ← `(∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x ∧ x < 3)] do
    let target ← Term.elabType sourceSyntax
    Term.synthesizeSyntheticMVarsNoPostponing
    requireRefusal "formula leaf" (Quote.prove (← instantiateMVars target) false) true
  let target ← Term.elabType (← `(∃ x : ℝ, x ^ 2 = Real.sqrt 2 ∧ 1 < x / (2 - 1) ∧ x < 2))
  Term.synthesizeSyntheticMVarsNoPostponing
  let entries := mkConst ``Packings.facts
  let checker ← mkAppM ``FiniteSigns.check #[mkConst ``FiniteJoint.next,
    ← mkAppM ``Schema.guards #[toExpr false, entries],
    ← mkAppM ``Schema.queries #[entries], ← mkAppM ``Data.selected #[toExpr false], mkConst ``Schema.formula]
  let unit ← mkAppM ``Hex.RealClosure.Transport.Closed.read_one #[mkConst ``Semantics.closed]
  requireRefusal "guard count with matching identity count"
    (FiniteQuote.finish (← instantiateMVars target) checker (← mkAppM ``Data.accepted #[toExpr false])
      (mkConst ``Semantics.read) (mkConst ``Semantics.zero) unit (mkConst ``Data.descriptor)
      (← mkAppM ``Data.replay #[toExpr false]) (mkConst ``Binding.valuation)
      (← mkAppM ``Binding.bind #[entries]) (mkConst ``Binding.valuation_eq) #[mkConst ``Data.guardIdentity]) true
#finite_formula_controls
end Hex.RCF.RealCoefficients.FiniteMatrixTests.Controls
