/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexRCF.HandlerTests.Support

public section

namespace Hex.RCF.HandlerTests

open Lean Meta Elab Tactic

-- These tactics intentionally observe restored state without changing the goal.
set_option linter.unusedTactic false
-- The observational IO references are shared across test declarations.
set_option Elab.async false

-- Repeated registration must not duplicate an attempt.
attribute [rcf_handler] aDecline

run_elab do
  let names ← handlerNames
  unless names == #[``aDecline, ``bResult, ``zLast] do
    throwError "unexpected registry order: {names}"

/-- Run the real tactic, inspecting state directly after failure rather than
relying on `first` or another tactic combinator to backtrack for it. -/
private meta def runCase (mode : Nat) (expected : Option String) : TacticM Unit := do
  let original ← getGoals
  let probe ← mkFreshExprMVar (mkConst ``Nat)
  probes.set #[probe.mvarId!, ← getMainGoal]
  calls.set #[]
  let error? ← tryCatchRuntimeEx
    (do
      withOptions (rcf.testMode.set · mode) do
        evalRCFTac (← `(tactic| rcf))
      pure none)
    (fun error => pure (some error))
  unless (← probe.mvarId!.isAssigned) == false do
    throwError "probe assignment leaked"
  let expectedCalls := if mode == 8 then #[1, 2, 3] else #[1, 2]
  unless (← calls.get) == expectedCalls do
    throwError "incorrect attempts: {← calls.get}"
  match expected, error? with
  | none, none =>
      unless (← getGoals).isEmpty do throwError "success left goals"
  | some text, some error =>
      unless (← getGoals) == original do throwError "failure changed goal list"
      assertRestored
      if mode == 7 then
        unless error.isMaxHeartbeat do throwError "exhaustion was reclassified"
      else
        unless (← error.toMessageData.toString).contains text do
          throwError "unexpected failure: {error.toMessageData}"
  | _, _ => throwError "unexpected success/failure"
  probes.set #[]

/-- Fresh kernel theorem emitted through registered dispatch. -/
theorem identity : ∀ x : ℝ, x + Real.pi = x + Real.pi := by
  run_tac runCase 0 none

/-- info: 'Hex.RCF.HandlerTests.identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms identity

example : ∀ x : ℝ, x + Real.pi = x + Real.pi := by
  run_tac runCase 1 (some "proposed a proof of a different goal")
  run_tac runCase 2 (some "returned an unresolved proof")
  run_tac runCase 3 (some "checked false verdict")
  run_tac runCase 4 (some "coefficient budget exhausted")
  run_tac runCase 5 (some "literal replay rejected")
  run_tac runCase 6 (some "unexpected handler exception")
  run_tac runCase 7 (some "")
  run_tac runCase 8 (some "symbolic or non-rational coefficient")
  run_tac runCase 9 (some "Application type mismatch")
  run_tac runCase 11 (some "forbidden axiom sorryAx")
  run_tac runCase 14 (some "forbidden axiom sorryAx")
  run_tac runCase 15 (some "forbidden axiom Lean.")
  exact fun _ => rfl

example : ∃ x : ℝ, x + Real.pi = x + Real.pi := by
  run_tac runCase 12 none

example : ∀ x : ℝ, x ∈ Set.Ioc (0 : ℝ) 1 → x + Real.pi = x + Real.pi := by
  run_tac runCase 12 none

/-- Assert that rational success and terminal frontend/solver errors do not
consult any optional handler. -/
private meta def noDispatch (shouldSucceed : Bool) (runtime := false) : TacticM Unit := do
  calls.set #[]
  let goals ← getGoals
  let error? ← tryCatchRuntimeEx
    (do evalRCFTac (← `(tactic| rcf)); pure none)
    (fun error => pure (some error))
  let succeeded := error?.isNone
  if runtime then
    unless error?.any (·.isMaxHeartbeat) do throwError "runtime failure was reclassified"
  unless succeeded == shouldSucceed do throwError "unexpected rational result"
  unless (← calls.get).isEmpty do throwError "unexpected handler dispatch"
  unless succeeded do
    unless (← getGoals) == goals do throwError "failure changed goals"
    for goal in goals do
      if ← goal.isAssigned then throwError "failure assigned goal"

-- Rational proofs still use certificate construction/replay with handlers present.
theorem rational : ∀ x : ℝ, x ^ 2 + (1 : ℝ) / 2 > 0 := by
  run_tac noDispatch true

/-- info: 'Hex.RCF.HandlerTests.rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rational

/-- error: unsolved goals
⊢ ∀ (x : ℝ), x ^ 2 > 0 -/
#guard_msgs in
example : ∀ x : ℝ, x ^ 2 > 0 := by
  run_tac noDispatch false

example (a : ℝ) : ∀ x : ℝ, x + a = x + a := by
  run_tac noDispatch false
  exact fun _ => rfl

example : ∀ x : ℝ, Real.sin x = Real.sin x := by
  run_tac noDispatch false
  exact fun _ => rfl

example : ∀ x : ℝ, x / x = x / x := by
  run_tac noDispatch false
  exact fun _ => rfl

example : ∀ x : ℝ, x ∈ Set.Ioc Real.pi 4 → x ≤ 4 := by
  run_tac noDispatch false
  exact fun _ h => h.2

example (a : ℝ) (_h : a = Real.pi) : ∀ x ∈ Set.Ioc a 4, x ≤ 4 := by
  run_tac noDispatch false
  exact fun _ h => h.2

run_elab do
  withLetDecl `a (mkConst ``Real) (mkConst ``Real.pi) fun a => do
    withLocalDeclD `h (← mkEq a (mkConst ``Real.pi)) fun _ => do
      let some closed ← Reify.closeCoefficient? a | throwError "let alias not recognized"
      checkWithKernel closed.proof

example : ∀ x : ℝ, x + budgetCoefficient = x + budgetCoefficient := by
  run_tac noDispatch false true
  exact fun _ => rfl

-- A handler cannot specialize an existing target metavariable to make its
-- otherwise well-typed proof fit. Check restoration without tactic backtracking.
run_elab do
  let unknown ← mkFreshExprMVar (mkConst ``Real)
  let body ← mkAppM ``Eq #[mkConst ``Real.pi, unknown]
  let target := mkForall `x .default (mkConst ``Real) body
  calls.set #[]
  let error? ← try
      withOptions (rcf.testMode.set · 10) do
        let _ ← proveGoal target
      pure none
    catch error => pure (some error)
  let some error := error? | throwError "accepted a changed target"
  unless (← error.toMessageData.toString).contains "proposed a proof of a different goal" do
    throwError "unexpected failure: {error.toMessageData}"
  if ← unknown.mvarId!.isAssigned then throwError "changed target leaked"
  unless (← calls.get) == #[1, 2] do throwError "incorrect attempts"

/-- Explicit local equalities permit dispatch, with the original goal intact. -/
theorem aliasForward (a : ℝ) (h : a = Real.pi) : ∀ x : ℝ, x + a = x + Real.pi := by
  run_tac runCase 13 none

example (a : ℝ) (h : Real.pi = a) : ∀ x : ℝ, x + a = x + Real.pi := by
  run_tac runCase 13 none

example (a b : ℝ) (ha : a = Real.pi) (hb : Real.exp 1 = b) :
    ∀ x : ℝ, x + a * b = x + Real.pi * Real.exp 1 := by
  run_tac runCase 1 (some "proposed a proof of a different goal")
  run_tac runCase 4 (some "coefficient budget exhausted")
  run_tac runCase 13 none

example (a b : ℝ) (_h : a = b) : ∀ x : ℝ, x + a = x + a := by
  run_tac noDispatch false
  exact fun _ => rfl

example (a b : ℝ) (_ha : a = b) (_hb : b = a) : ∀ x : ℝ, x + a = x + a := by
  run_tac noDispatch false
  exact fun _ => rfl

example (a b : ℝ) (_h : a = Real.pi + b) : ∀ x : ℝ, x + a = x + a := by
  run_tac noDispatch false
  exact fun _ => rfl

example (a : ℝ) (_h : a = Real.pi - Real.pi) : True := by
  run_tac do
    let a ← getFVarFromUserName `a
    let zero ← Term.elabTerm (← `(term| (0 : ℝ))) none
    let source ← mkAppM ``HDiv.hDiv #[zero, a]
    let source ← instantiateMVars source
    let some closed ← Reify.closeCoefficient? source | throwError "alias not recognized"
    unless closed.value.isAppOfArity ``HDiv.hDiv 6 &&
        closed.value.appArg!.isAppOfArity ``HSub.hSub 6 do
      throwError "division syntax was changed"
    checkWithKernel closed.proof
  trivial

/-- info: 'Hex.RCF.HandlerTests.aliasForward' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms aliasForward

/-- error: Cannot add attribute `[rcf_handler]`: Declaration `badSignature` has type
  ℕ
but `[rcf_handler]` can only be added to declarations of type
  Handler -/
#guard_msgs in
@[rcf_handler] meta def badSignature : Nat := 0

/-- error: Cannot add attribute `[rcf_handler]`: Declaration `badArity` has type
  ℕ → Handler
but `[rcf_handler]` can only be added to declarations of type
  Handler -/
#guard_msgs in
@[rcf_handler] meta def badArity : Nat → Handler := fun _ _ => return .declined

/-- error: Cannot add attribute `[rcf_handler]`: Declaration `nonMeta` must be marked as `meta` -/
#guard_msgs in
@[rcf_handler] def nonMeta : Nat := 0

/-- error: Invalid attribute scope: Attribute `[rcf_handler]` must be global, not `local` -/
#guard_msgs in
attribute [local rcf_handler] aDecline

/-- error: rcf_handler: Hex.RCF.HandlerTests.polymorphic must be monomorphic -/
#guard_msgs in
@[rcf_handler] meta def polymorphic.{u} : (α : Type u) → Handler := fun _ _ => return .declined

-- A handler cannot register a local declaration with the bridge's name and
-- use that name to smuggle an unrelated admission through the audit.
run_meta do
  let spoof : Name :=
    .str (.str (.str .anonymous "HexRealRootsMathlib") "Tarski") "check_rootSum"
  let saved ← saveState
  let _ ← tryFinally' (do
    let admitted ← mkSorry (mkConst ``True) false
    addDecl (.thmDecl { name := spoof, levelParams := [], type := mkConst ``True, value := admitted })
    let outcome ← observing? (checkAxioms (Name.mkSimple "spoofProbe") (mkConst spoof))
    unless outcome.isNone do throwError "a local bridge-name spoof passed the axiom audit")
    (fun _ => saved.restore)
  if (← getEnv).find? spoof |>.isSome then
    throwError "the temporary spoof escaped the test"

end Hex.RCF.HandlerTests
