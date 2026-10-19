/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup
meta import HexPermGroup.Tactic
meta import Lean
public section

namespace Hex.PermGroup.Tests

-- The identity residual stops immediately, but the full check still rejects
-- a malformed level even when every input is the identity.
example : Kernel.sift 4 (Kernel.width 4) (Kernel.ident 4 (Kernel.width 4))
    [default] (Kernel.ident 4 (Kernel.width 4)) = true := by decide +kernel
example : Kernel.check 4 [Kernel.ident 4 (Kernel.width 4)] [default] = false :=
  by decide +kernel

private def cycle : Perm 3 := Perm.mk #v[1, 2, 0]
private def swap : Perm 3 := Perm.mk #v[1, 0, 2]
private def gens : Array (Perm 3) := #[cycle, swap]

example : HasOrder gens 6 := by perm_group
example : Generated #[cycle] (cycle.comp cycle) := by perm_group
example : ¬ Generated #[cycle] swap := by perm_group
example : GeneratesAll gens := by perm_group
example : ∀ p : Perm 3, Generated gens p := by perm_group
example : HasOrder (#[] : Array (Perm 0)) 1 := by perm_group
example : HasOrder (#[] : Array (Perm 1)) 1 := by perm_group
example : Generated (#[] : Array (Perm 0)) (Perm.id 0) := by perm_group
example : ¬ Generated (#[] : Array (Perm 3)) swap := by perm_group
example : GeneratesAll (#[] : Array (Perm 0)) := by perm_group
example : GeneratesAll (#[] : Array (Perm 1)) := by perm_group
example : HasOrder #[Perm.id 3, cycle, cycle, cycle.inv] 3 := by perm_group


example : Generated #[Perm.ofImages 3 [0, 0, 1]] (Perm.id 3) := by perm_group
example : HasOrder #[Perm.ofImages 3 [0, 3, 1]] 1 := by perm_group
example : HasOrder #[Perm.ofImages 3 []] 1 := by perm_group

def symmetric11 : Array (Perm 11) := #[
  Perm.ofImages 11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0],
  Perm.ofImages 11 [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10]]

theorem symmetric11_all : GeneratesAll symmetric11 := by perm_group
theorem symmetric11_forall : ∀ p : Perm 11, Generated symmetric11 p := by perm_group

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.symmetric11_all' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms symmetric11_all
set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.symmetric11_forall' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms symmetric11_forall

/-- error: perm_group: full coverage check needs 100 estimated operations, exceeding maxChunkWork := 1 -/
#guard_msgs in
example : GeneratesAll (#[] : Array (Perm 100)) := by
  perm_group (maxChunkWork := 1)

def m11 : Array (Perm 11) := #[
  Perm.ofImages 11 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 0],
  Perm.ofImages 11 [0, 1, 6, 9, 5, 3, 10, 2, 8, 4, 7]]

theorem m11_order : HasOrder m11 7920 := by perm_group
theorem m11_mem : Generated m11 ((m11[0]'(by decide)).comp (m11[1]'(by decide))) := by perm_group
theorem m11_not_mem : ¬ Generated m11
    (Perm.ofImages 11 [1, 0, 2, 3, 4, 5, 6, 7, 8, 9, 10]) := by perm_group

/-- error: perm_group: the certified order is 7920, not 7921 -/
#guard_msgs in
example : HasOrder m11 7921 := by perm_group

/-- error: perm_group: the certified group does not generate every permutation -/
#guard_msgs in
example : GeneratesAll m11 := by perm_group

example : True := by
  fail_if_success have : Generated #[cycle] swap := by perm_group
  -- On generators not certified earlier in this file: `m11_order` already
  -- recorded a certificate for `m11`, which would emit no level check.
  fail_if_success have : HasOrder #[cycle.comp cycle, swap] 6 := by perm_group (maxChunkWork := 1)
  trivial

#guard_msgs (drop info) in
#perm_group_certificate symmetricThree for gens

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.m11_order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_order
set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.m11_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_mem
set_option pp.width 200 in
/-- info: 'Hex.PermGroup.Tests.m11_not_mem' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms m11_not_mem


/-! Checked certificates are reused within a file. A certificate made inside an
`example` is discarded with the example's declarations, so the first theorem
below certifies again, and the next goal on the same generators reuses it. -/

example : HasOrder #[swap.comp cycle] 2 := by perm_group

private theorem reuse_order : HasOrder #[swap.comp cycle] 2 := by perm_group

/--
trace: [perm_group] degree 3, order 2, orbit sizes [2], chunks per level []
[perm_group] reusing the checked certificate _private.HexPermGroup.Tests.0.Hex.PermGroup.Tests.reuse_order._perm_group.cert_1
-/
#guard_msgs in
set_option trace.perm_group true in
example : ¬ Generated #[swap.comp cycle] cycle := by perm_group

-- A budget too small for a transposition's level check fails without a cached
-- certificate, but a cached one emits no level check, so the budget is not
-- applied to it.
example : HasOrder #[swap] 2 := by
  fail_if_success perm_group (maxChunkWork := 20)
  perm_group
example : ¬ Generated #[swap.comp cycle] cycle := by perm_group (maxChunkWork := 20)

-- A certificate recorded by a call that is then backtracked over is discarded
-- with its declarations: the second call certifies again.
/--
trace: [perm_group] degree 3, order 3, orbit sizes [3], chunks per level [1]
[perm_group] level 0: pairs [0, 3)
---
trace: [perm_group] degree 3, order 3, orbit sizes [3], chunks per level [1]
[perm_group] level 0: pairs [0, 3)
-/
#guard_msgs in
set_option trace.perm_group true in
private theorem backtracked : HasOrder #[cycle] 3 := by
  first
  | (perm_group; fail "discard")
  | perm_group

end Hex.PermGroup.Tests

namespace Hex.PermGroup.InterfaceTests

open Lean Elab Meta Lean.Elab.Tactic

/-- Exercise the supported API without the tactic's goal dispatcher. -/
elab "perm_group_public" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← instantiateMVars (← goal.getType)
  let (S, request) ← if target.isAppOfArity ``HasOrder 3 then do
      let some N ← (evalNat (target.getArg! 2)).run | throwError "expected numeral"
      pure (target.getArg! 1, Tactic.Goal.card N)
    else if target.isAppOfArity ``Generated 3 then
      pure (target.getArg! 1, Tactic.Goal.mem { term := target.getArg! 2 })
    else if target.isAppOfArity ``Not 1 then
      let body := target.getArg! 0
      pure (body.getArg! 1, Tactic.Goal.notMem { term := body.getArg! 2 })
    else if target.isAppOfArity ``GeneratesAll 2 then
      pure (target.getArg! 1, Tactic.Goal.all)
    else throwError "unexpected interface test goal"
  let some generators ← getArrayLit? S | throwError "expected array literal"
  let inputs ← generators.toList.mapM fun term => do
    pure ({ term, canonical? := some (term, ← mkEqRefl term) } : Tactic.Input)
  let prepared ← Tactic.prepare {} 2 inputs
  goal.assign (← Tactic.replay prepared request)
  replaceMainGoal []

theorem order : HasOrder #[Perm.ofImages 2 [1, 0]] 2 := by perm_group_public
theorem member : Generated #[Perm.ofImages 2 [1, 0]] (Perm.id 2) := by perm_group_public
theorem nonmember : ¬ Generated (#[] : Array (Perm 2)) (Perm.ofImages 2 [1, 0]) := by
  perm_group_public
theorem full : GeneratesAll #[Perm.ofImages 2 [1, 0]] := by perm_group_public

private meta def expectFailure (fragment : String) (action : TacticM α) : TacticM Unit := do
  -- Do not let the exception handler restore state: these tests must exercise
  -- the replay transaction itself.
  let failed ← Tactic.tryCatch (do
    let _ ← action
    pure false) fun ex => do
    let message ← ex.toMessageData.toString
    unless message.contains fragment do
      throwError "unexpected interface failure: {message}"
    pure true
  unless failed do throwError "expected interface failure"

elab "check_perm_group_failures" : tactic => withMainContext do
  let goal ← getMainGoal
  let images ← mkListLit (mkConst ``Nat) [mkNatLit 1, mkNatLit 0]
  let swap ← mkAppM ``Perm.ofImages #[mkNatLit 2, images]
  let identity ← mkAppM ``Perm.id #[mkNatLit 2]
  let bad : Tactic.Input := { term := swap, canonical? := some (identity, ← mkEqRefl identity) }
  expectFailure "canonical input equality has the wrong type" (Tactic.prepare {} 2 [bad])
  let wrongDegree ← mkAppM ``Perm.id #[mkNatLit 3]
  let wrongProof ← mkEqRefl wrongDegree
  let badDegree : Tactic.Input := { term := swap, canonical? := some (wrongDegree, wrongProof) }
  expectFailure "canonical input has the wrong degree" (Tactic.prepare {} 2 [badDegree])
  let unresolved ← mkFreshExprMVar (← inferType swap)
  expectFailure "closed terms" (Tactic.prepare {} 2 [{ term := unresolved }])
  let prepared ← Tactic.prepare {} 2 [{ term := swap }]
  let marker ← Kernel.Tactic.auxName "level_0"
  -- `inferType` does not validate application arguments. Replay must kernel-check
  -- the supplied equality, even when its inferred result type looks correct.
  let equalityType ← mkEq swap swap
  let malformed := mkApp4 (mkConst ``Eq.mpr [0]) equalityType equalityType
    (← mkEqRefl equalityType) (mkConst ``True.intro)
  let badEquality ← Tactic.prepare {} 2
    [{ term := swap, canonical? := some (swap, malformed) }]
  expectFailure "mismatch" (Tactic.replay badEquality (.card 2))
  if (← getEnv).contains marker then throwError "bad equality leaked declarations"
  expectFailure "mismatch" (Tactic.replay { prepared with images := [[0, 1]] } (.card 2))
  if (← getEnv).contains marker then throwError "failed replay leaked declarations"
  let canonical ← Tactic.prepare {} 2
    [{ term := swap, canonical? := some (swap, ← mkEqRefl swap) }]
  expectFailure "mismatch" (Tactic.replay { canonical with images := [[0, 1]] } (.card 2))
  if (← getEnv).contains marker then throwError "canonical replay leaked declarations"
  -- The old callback API remains supported and must also restore assigned goals.
  expectFailure "injected packing failure" (Kernel.Tactic.prove {} 2 [swap] (.card 2) fun _ _ _ _ => do
    goal.assign (mkConst ``True.intro)
    throwError "injected packing failure")
  if (← getEnv).contains marker then throwError "compatibility replay leaked declarations"
  if ← goal.isAssigned then throwError "failed replay assigned the original goal"
  unless (← getGoals) == [goal] do throwError "failed replay changed the goal list"
  -- Runtime exceptions bypass ordinary `catch`; finalizers must still roll back.
  for heartbeat in [true, false] do
    let failed ← tryCatchRuntimeEx (do
      let _ ← Kernel.Tactic.prove {} 2 [swap] (.card 2) fun _ _ _ _ => do
        goal.assign (mkConst ``True.intro)
        if heartbeat then
          Lean.Core.throwMaxHeartbeat `perm_group `maxHeartbeats 1
          throwError "unreachable"
        else
          throwMaxRecDepthAt (← getRef)
      pure false) fun ex => do
        unless ex.isMaxHeartbeat || ex.isMaxRecDepth do
          throwError "unexpected runtime exception"
        pure true
    unless failed do throwError "expected a runtime exception"
    if (← getEnv).contains marker then throwError "runtime failure leaked declarations"
    if ← goal.isAssigned then throwError "runtime failure assigned the original goal"
    unless (← getGoals) == [goal] do throwError "runtime failure changed the goal list"
  evalTactic (← `(tactic| trivial))

example : True := by check_perm_group_failures

set_option pp.width 200 in
/-- info: 'Hex.PermGroup.InterfaceTests.order' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms order

end Hex.PermGroup.InterfaceTests
