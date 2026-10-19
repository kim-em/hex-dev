/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingInput00
public meta import KernelReplay.GuardRemainingInput00
import all KernelReplay.GuardRemainingInput00
import all KernelReplay.GuardRemainingInputs
import all KernelReplay.GuardCoefficientReduce
import all KernelReplay.GuardCoefficientIndex
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientReduceControl
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := reducedCoefficientControl) "#reduced_coefficient_control" : command
@[command_elab reducedCoefficientControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let agreement := mkConst ``GuardInventoryReplay.agreement
  let arguments := (← inferType agreement).getAppArgs
  let inventory := arguments.back!
  let domain := arguments[arguments.size - 4]!
  let first ← withTransparency .all (whnf inventory)
  unless first.getAppFn.isConstOf ``List.cons do throwError "actual coefficient inventory is empty"
  let wanted := first.getAppArgs[1]!
  let type := mkApp domain wanted
  let supplier ← GuardCoefficientReduce.prepare began agreement
  let some proof ← supplier type | throwError "reduced hint did not find the first original coefficient"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientReduceControl
  let typed ← withTransparency .all do mkAppOptM ``id #[some type, some proof]
  let _proof ← retain began (root ++ `correct) typed
  let mut rest := inventory
  let mut size := 0
  for _ in [:20000] do
    let _ ← bounded began
    let literal ← withTransparency .all (whnf rest)
    if literal.getAppFn.isConstOf ``List.nil then break
    unless literal.getAppFn.isConstOf ``List.cons do throwError "coefficient inventory is not literal"
    size := size + 1
    rest := literal.getAppArgs[2]!
  unless (← withTransparency .all (whnf rest)).getAppFn.isConstOf ``List.nil do
    throwError "coefficient control inventory bound exhausted"
  let invalid ← GuardCoefficientIndex.positionProof agreement type size
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  match (← getEnv).toKernelEnv.addDecl options (.thmDecl {
      name := `__incorrectReducedCoefficientPosition, levelParams := [], type, value := invalid }) with
  | .ok _ => throwError "kernel accepted an out-of-range coefficient hint"
  | .error (.appTypeMismatch ..) => pure ()
  | .error (.declTypeMismatch ..) => pure ()
  | .error (.exprTypeMismatch ..) => pure ()
  | .error error => ofExceptKernelException (Except.error error)
  logInfo m!"reduced coefficient hint control module export: originalInventorySize={size} correctPositionAccepted=true sameOriginalRequestWithOutOfRangePositionRejected=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#reduced_coefficient_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientReduceControl
