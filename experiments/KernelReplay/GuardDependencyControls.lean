/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.FramePublic
import KernelReplay.GuardDependencyAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDependencyControls
open Lean Meta Elab

set_option maxRecDepth 32768 in
set_option maxHeartbeats 1500000 in
private theorem cachedBody : True :=
  Eq.mp (congrArg (fun _ : Element FrameOwners.second => True)
    FrameOperand.request_coeff) True.intro

meta section

/-- Reject for the cached module itself, rather than accepting an unrelated
budget, missing-body or whole-field error as a successful negative control. -/
def expectRejected (name : Name) : MetaM Unit := do
  let began ← IO.getNumHeartbeats
  let result : Except String GuardDependencyAudit.Result ← try
      pure (.ok (← GuardDependencyAudit.walk began #[mkConst name]))
    catch error => pure (.error (← error.toMessageData.toString))
  match result with
  | .ok _ => throwError "cached operand dependency was accepted: {name}"
  | .error error =>
    unless error.startsWith "cached operand dependency from KernelReplay.FrameOperand:" do
      throwError "cached operand control failed for another reason: {error}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let .thmInfo body ← getConstInfo ``cachedBody | throwError "missing body-only control"
  unless body.type.isConstOf ``True && body.value.getUsedConstants.contains ``FrameOperand.request_coeff do
    throwError "body-only control lost its cached proof dependency"
  expectRejected ``FramePublic.product
  expectRejected ``cachedBody
  let env ← getEnv
  let records := env.checked.get.constants.fold (fun found name info =>
    if GuardDependencyAudit.fromModule env `KernelReplay.FrameOperand name &&
        isPrivateName name && info.type.getAppFn.isConstOf ``SignFact then
      found.push name else found) (#[] : Array Name)
  unless !records.isEmpty do throwError "missing actual private cached scalar record"
  for name in records do expectRejected name
  let generic ← GuardDependencyAudit.walk began #[mkConst ``FrameOperand.constant]
  unless generic.declarations > 0 do throwError "generic constant control did not inspect any declarations"
  logInfo m!"cached operand controls: directType=true proofBody=true privateRecords={records.size} genericConstant=true"

end
end Hex.RealClosure.Algebraic.KernelReplay.GuardDependencyControls
