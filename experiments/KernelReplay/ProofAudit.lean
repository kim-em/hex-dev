/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.FiniteBase
public meta import HexRealClosureTheory.KernelReplay
import all HexRealClosureTheory.KernelReplay
import all KernelReplay.FiniteBase

public meta section
namespace Hex.RealClosure.Algebraic.KernelReplay.ProofAudit
open Lean Meta Elab Command

private def uncached (proof type : Expr) : MetaM (Array Name) := do
  let mut result := #[]
  for name in proof.getUsedConstants ++ type.getUsedConstants do
    for dependency in ← collectAxioms name do
      unless result.contains dependency do result := result.push dependency
  return result.qsort Name.lt

private def check (proof type : Expr) : MetaM (Array Name) := do
  let expected ← uncached proof type
  let actual := (← auditProof proof type).qsort Name.lt
  unless actual == expected do throwError "reused proof audit changed the actual axiom set"
  kernelCheck `__proofAudit type proof
  return actual

private def restoration : MetaM Unit := do
  let name ← mkFreshUserName `auditBranch
  let dependency ← mkFreshUserName `auditDependency
  let saved ← Meta.saveState
  try
    addDecl (.thmDecl {
      name := dependency, levelParams := [], type := mkConst ``True, value := mkConst ``True.intro })
    addDecl (.thmDecl {
      name, levelParams := [], type := mkConst ``True, value := mkConst dependency })
    unless (← check (mkConst name) (mkConst ``True)).isEmpty do
      throwError "constructive branch acquired an axiom"
    unless (auditedConstants.getState (← getEnv) |>.find? name) == some #[] do
      throwError "local constructive audit was not retained"
    unless (← check (mkConst name) (mkConst ``True)).isEmpty do
      throwError "reused constructive audit changed dependencies"
    saved.restore
    unless (auditedConstants.getState (← getEnv) |>.find? name).isNone do
      throwError "environment restoration kept another branch's audit"
    let witness ← mkAppM ``Nonempty.intro #[mkConst ``True.intro]
    let chosen ← mkAppM ``Classical.choice #[witness]
    addDecl (.thmDecl {
      name := dependency, levelParams := [], type := mkConst ``True, value := chosen })
    -- This declaration is identical in both branches; its dependency changed.
    addDecl (.thmDecl {
      name, levelParams := [], type := mkConst ``True, value := mkConst dependency })
    unless (← check (mkConst name) (mkConst ``True)) == #[`Classical.choice] do
      throwError "unchanged declaration reused another branch's dependency audit"
    unless (auditedConstants.getState (← getEnv) |>.find? name) == some #[`Classical.choice] do
      throwError "changed dependency audit was not retained"
    unless (← check (mkConst name) (mkConst ``True)) == #[`Classical.choice] do
      throwError "reused dependency audit changed its actual axioms"
    for imported in #[``True, ``Transport.Product.of_closed] do
      let info ← getConstInfo imported
      let value := mkConst imported (info.levelParams.map Level.param)
      let _ ← auditProof value (← inferType value)
      unless (auditedConstants.getState (← getEnv) |>.find? imported).isNone do
        throwError "imported declaration acquired a local audit entry"
    -- A dependency occurring only in the proposition must also be audited.
    let type ← mkEq chosen (mkConst ``True.intro)
    let proof ← mkEqRefl (mkConst ``True.intro)
    unless (← check proof type) == #[`Classical.choice] do
      throwError "proof audit omitted a proposition dependency"
    let incomplete ← mkFreshExprMVar (mkConst ``True)
    let rejected ← try
      let _ ← auditProof incomplete (mkConst ``True)
      pure false
    catch error =>
      unless (← error.toMessageData.toString) == "incomplete proof" do throw error
      pure true
    unless rejected && !(← incomplete.mvarId!.isAssigned) do
      throwError "proof audit accepted or assigned an incomplete proof"
  finally saved.restore

private def compare (proof type : Expr) (cached : Bool) : MetaM Unit := do
  let saved ← Meta.saveState
  try
    let began ← IO.getNumHeartbeats
    let mut last := #[]
    for _ in [:8] do
      last ← if cached then auditProof proof type else uncached proof type
    let cost := ((← IO.getNumHeartbeats) - began) / 1000
    unless last.qsort Name.lt == (← uncached proof type) do
      throwError "measured proof audit changed dependencies"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"proof audit comparison: cached={cached} repetitions=8 heartbeats={cost}"
        handle.flush
  finally saved.restore

private def application (name theoremName : Name) (count : Nat) (direct : Bool) : MetaM Unit := do
  let saved ← Meta.saveState
  try
    let .thmInfo original ← getConstInfo name | throwError "finite-base theorem body missing"
    unless original.value.getAppFn.isConstOf theoremName do
      throwError "finite-base proof changed its theorem application"
    let arguments := original.value.getAppArgs
    let explicit := arguments.extract (arguments.size - count - 3) arguments.size
    let began ← IO.getNumHeartbeats
    let mut proof := original.value
    for _ in [:8] do
      proof ← withTransparency .all do
        if direct then
          let guarded ← mkAppM theoremName (explicit.extract 0 3)
          return mkAppN guarded (explicit.extract 3 explicit.size)
        else mkAppM theoremName explicit
    let constructed ← IO.getNumHeartbeats
    unless ← withTransparency .all (isDefEq (← inferType proof) original.type) do
      throwError "direct base theorem application changed its conclusion"
    let _ ← check proof original.type
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"base application comparison: theorem={theoremName} direct={direct} repetitions=8 constructionHB={(constructed - began) / 1000} validationHB={((← IO.getNumHeartbeats) - constructed) / 1000}"
        handle.flush
  finally saved.restore

private def rejectArgument : MetaM Unit := do
  let .thmInfo original ← getConstInfo ``FiniteBaseProbe.product |
    throwError "finite-base product theorem body missing"
  let arguments := original.value.getAppArgs
  let bad := mkAppN original.value.getAppFn
    (arguments.set! (arguments.size - 1) (mkConst ``True.intro))
  let name ← mkFreshUserName `corruptedBaseArgument
  let options := (← getOptions).setBool `debug.skipKernelTC false
  let declaration := Declaration.thmDecl {
    name, levelParams := original.levelParams, type := original.type, value := bad }
  match (← getEnv).toKernelEnv.addDecl options declaration with
  | .error (.appTypeMismatch ..) => pure ()
  | .error error => throwKernelException error
  | .ok _ => throwError "ordinary kernel accepted a corrupted base membership argument"

private def production (name : Name) : MetaM Unit := do
  let .thmInfo original ← getConstInfo name | throwError "finite-base theorem body missing"
  let base ← FiniteData.Base.ofClosed (mkConst ``FiniteBaseProbe.closed)
  let domains := FiniteData.agreementSupplier (mkConst ``FiniteBaseProbe.agreement)
  forallTelescope original.type fun binders target => do
    let some proof ← base.supply domains domains target |
      throwError "production base supplier rejected an existing finite-base operation"
    let expected := (mkAppN original.value binders).headBeta
    unless proof == expected do
      throwError "production base supplier changed its existing finite-base proof"
    let statement ← mkForallFVars binders target
    let closed ← mkLambdaFVars binders proof
    let _ ← check closed statement

syntax (name := proofAudit) "#proof_audit" : command
@[command_elab proofAudit]
def elaborate : CommandElab := fun _ => liftTermElabM do
  restoration
  rejectArgument
  let name ← mkFreshUserName `auditProduct
  let .thmInfo original ← getConstInfo ``FiniteBaseProbe.product |
    throwError "actual finite-base product theorem missing"
  -- Audit the actual generated finite-base proof as a local declaration.
  addDecl (.thmDecl {
    name, levelParams := original.levelParams, type := original.type, value := original.value })
  let proof := mkConst name
  let fresh ← Meta.saveState
  let _ ← check proof original.type
  fresh.restore
  let comparisons := (← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE").isSome
  if comparisons then
    for order in #[#[false, true], #[true, false]] do
      for cached in order do compare proof original.type cached
  for (name, theoremName, count) in #[
      (``FiniteBaseProbe.product, ``Transport.Product.of_closed, 4),
      (``FiniteBaseProbe.sum, ``Transport.Sum.of_closed, 4),
      (``FiniteBaseProbe.difference, ``Transport.Difference.of_closed, 4),
      (``FiniteBaseProbe.scaling, ``Transport.Scaling.of_closed, 4),
      (``FiniteBaseProbe.derivative, ``Transport.Differentiation.of_closed, 2),
      (``FiniteBaseProbe.evaluation, ``Transport.Evaluation.of_closed, 4)] do
    production name
    if comparisons then
      for order in #[#[false, true], #[true, false]] do
        for direct in order do application name theoremName count direct
  production ``FiniteBaseProbe.power
  logInfo "proof audits agree with uncached dependencies and preserve environment restoration, proposition dependencies and incomplete-proof rejection"

end Hex.RealClosure.Algebraic.KernelReplay.ProofAudit

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
/-- info: proof audits agree with uncached dependencies and preserve environment restoration, proposition dependencies and incomplete-proof rejection -/
#guard_msgs in
#proof_audit
