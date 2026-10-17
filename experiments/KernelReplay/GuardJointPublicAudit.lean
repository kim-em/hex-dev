/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardJointPublic
import KernelReplay.GuardJointUse
import KernelReplay.GuardJointAudit
import KernelReplay.GuardDependencyControls

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardJointPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

private def withWitnesses (count : Nat) (type : Expr)
    (action : Array Expr → Expr → MetaM Unit) : MetaM Unit := do
  match count with
  | 0 => action #[] type
  | count + 1 =>
    unless type.getAppFn.isConstOf ``Exists do throwError "joint statement lost an outer witness"
    let .lam name domain body _ := type.getAppArgs[1]! |
      throwError "joint witness predicate is not explicit"
    withLocalDeclD name domain fun value =>
      withWitnesses count (body.instantiate1 value) fun later predicate =>
        action (#[value] ++ later) predicate

/-- Inspect the exact balanced conjunction used by the original constructor.
A guard that itself contains conjunctions remains a single original clause. -/
private def clauses (began : Nat) (body : Expr) : MetaM (Array Expr) := do
  let mut pending := [(body, 3778)]
  let mut result : Array Expr := #[]
  for _ in [:10000] do
    let _ ← bounded began
    let (term, count) :: rest := pending | break
    pending := rest
    if count == 1 then result := result.push term
    else
      unless count > 1 && term.getAppFn.isConstOf ``And do
        throwError "joint statement changed its original balanced clause tree"
      let args := term.getAppArgs
      unless args.size == 2 do throwError "joint conjunction changed its arity"
      let mut left : Nat := 1
      while left*2 < count do left := left*2
      pending := (args[0]!, left) :: (args[1]!, count-left) :: pending
  unless pending.isEmpty && result.size == 3778 do
    throwError "joint statement omitted or added an original clause"
  return result

private def same (actual expected : Expr) (label : String) : MetaM Unit := do
  let expected ← instantiateMVars expected
  if expected.hasMVar || actual.hasMVar then throwError "incomplete joint audit target: {label}"
  unless ← withTransparency .all (isDefEq actual expected) do
    throwError "joint statement changed its original {label}"

private def evaluation (context read point : Expr) : MetaM Expr := do
  let carrier ← mkAppM ``Element #[context]
  withLocalDeclD `value carrier fun value => do
    let polynomial ← mkAppM ``Element.polynomial #[value]
    mkLambdaFVars #[value] (← mkAppM ``Packing.eval #[read, point, polynomial])

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta do
  let began ← IO.getNumHeartbeats
  let joint ← getConstInfo ``GuardJoint.exists_points
  unless joint.isTheorem && joint.levelParams.isEmpty do
    throwError "complete original joint theorem is unavailable"
  let exported ← getConstInfo ``GuardJointExport.exists_points
  unless exported.isTheorem && exported.levelParams.isEmpty do
    throwError "public joint theorem is unavailable"
  let .defnInfo statement ← getConstInfo ``GuardJointExport.Statement |
    throwError "public joint statement is not a transparent checked proposition"
  unless statement.levelParams.isEmpty && statement.value == exported.type do
    throwError "public joint alias changed the exact original existential"
  same exported.type joint.type "original joint proposition"
  let setup ← GuardDescriptorInputs.prepare
  let first := setup.first
  let second ← Prefix.ofData (mkConst ``GuardSecondData.data)
    (mkConst ``GuardDescriptorPoint.zero) (mkConst ``GuardDescriptorPoint.unit)
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let actualReaders := #[origin.read, first.reader, second.reader]
  let originals := GuardFrontier.templates.getState (← getEnv)
  unless originals.size == 3773 do throwError "original discovery template count changed"
  let baseExists := (← getConstInfo ``GuardInventoryReplay.baseExists).type
  let existence := baseExists.getAppArgs
  withWitnesses 3 exported.type fun witnesses predicate => do
    unless witnesses.size == 3 do throwError "joint witness count changed"
    same (← inferType witnesses[0]!) existence[0]! "base interpretation type"
    for index in [1:3] do
      same (← inferType witnesses[index]!) (mkConst ``Real) "ordinary real point type"
    for chosen in #[mkConst ``GuardInventoryReplay.interpretation, first.point, second.point] ++ actualReaders do
      if predicate.find? (· == chosen) |>.isSome then
        throwError "public joint predicate retains a chosen interpretation, point or reader"
    let leaves ← clauses began predicate
    let chosen := mkConst ``GuardInventoryReplay.interpretation
    let agreement := (← getConstInfo ``GuardAgreementPublic.agreement).type
    let expected := agreement.replace fun term =>
      if term == chosen then some witnesses[0]! else none
    same leaves[0]! expected "complete ordered coefficient agreement"
    let inherited ← whnf (mkApp existence[1]! witnesses[0]!)
    unless inherited.getAppFn.isConstOf ``And do throwError "provider predicate changed"
    same leaves[1]! inherited.getAppArgs[1]! "inherited provider clause"
    let read ← mkAppM ``BaseContext.Context.partialRead
      #[mkConst ``FiniteBaseProbe.base, witnesses[0]!]
    let mut previous := read
    let mut readers := #[read]
    for index in [:2] do
      let name := #[``GuardInventoryReplay.firstData, ``GuardSecondData.data][index]!
      let data := (← getConstInfo name).type
      unless data.getAppFn.isConstOf ``Packing.Inventory.Data do
        throwError "original inventory data changed"
      let args := data.getAppArgs
      let fields := args.extract (args.size-5) (args.size-1)
      let expected ← mkAppM ``Packing.Inventory.Conditions
        (fields ++ #[previous, witnesses[index+1]!])
      same leaves[index+2]! expected "complete inventory at the same point"
      previous ← evaluation fields[0]! previous witnesses[index+1]!
      readers := readers.push previous
    for index in [:3773] do
      let _ ← bounded began
      let mut expected := originals[index]!
      for reader in readers do
        let .lam _ _ body _ := expected | throwError "original discovery reader binder changed"
        expected := body.instantiate1 reader
      same leaves[index+4]! expected s!"complete guard {index} at the shared readers"
    let product ← mkAppM ``Transport.Product
      #[previous, mkConst ``FrameOwners.requestPoly, mkConst ``FrameOwners.requestPoly]
    same leaves[3777]! product "original native product at the second reader"
  logInfo m!"public joint statement audit: witnesses=3 originalGuards=3773 completeClauses=3778 completeOriginalAlias=true fullOrderedBaseAgreement=true inheritedProviderValuesFixed=true bothOriginalInventories=true allGuardClausesAtSharedReaders=true originalNativeProduct=true chosenWitnessesAbsentFromStatement=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let result ← GuardDependencyAudit.walk began #[mkConst ``GuardJointPublic.exists_points,
    mkConst ``GuardJointUse.coordinates,
    mkConst ``GuardJointExport.exists_points,
    mkConst ``GuardJointExport.Statement, mkConst ``GuardJoint.exists_points,
    mkConst ``GuardJoint.Statement]
  unless result.axioms == GuardDependencyAudit.standard do
    throwError "public joint axiom closure changed"
  let count := result.declarations
  logInfo m!"public joint full body audit: ordinaryPublicImports=true witnesses=3 originalGuards=3773 completeClauses=3778 exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let env ← getEnv
  let bindings := env.checked.get.constants.fold (fun found name info =>
    if info.isTheorem && GuardDependencyAudit.fromModule env `KernelReplay.GuardNativeFrontier name &&
        info.type.getUsedConstants.any (fun dependency =>
          isPrivateName dependency && GuardDependencyAudit.fromModule env `KernelReplay.FrameOperand dependency) then
      found.push name else found) (#[] : Array Name)
  unless !bindings.isEmpty do throwError "missing original cached scalar binding control"
  for name in bindings do GuardDependencyControls.expectRejected name
  let _ ← bounded began
  logInfo m!"public cached operand negative control: rejected=true originalBindings={bindings.size}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardJointPublicAudit
