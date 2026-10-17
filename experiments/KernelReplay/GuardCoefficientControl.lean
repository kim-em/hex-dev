/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardDescriptorReductions
public meta import KernelReplay.GuardDescriptorReductions
import all KernelReplay.GuardDescriptorReductions
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientControl
open Lean Meta Elab Command GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let agreement := mkConst ``GuardInventoryReplay.agreement
  let arguments := (← inferType agreement).getAppArgs
  let inventory := arguments.back!
  let domain := arguments[arguments.size - 4]!
  let first ← withTransparency .all (whnf inventory)
  unless first.getAppFn.isConstOf ``List.cons do throwError "actual coefficient inventory is empty"
  let wanted := first.getAppArgs[1]!
  let type := mkApp domain wanted
  let proof ← GuardCoefficientIndex.positionProof agreement type 0
  let proof ← retain began
    `Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientControl.first proof
  kernelCheck `__originalCoefficientRequest type proof
  let mut rest := inventory
  let mut size := 0
  for _ in [:20000] do
    let _ ← bounded began
    let literal ← withTransparency .all (whnf rest)
    if literal.getAppFn.isConstOf ``List.nil then break
    unless literal.getAppFn.isConstOf ``List.cons do throwError "nonliteral coefficient inventory"
    size := size + 1
    rest := literal.getAppArgs[2]!
  unless (← withTransparency .all (whnf rest)).getAppFn.isConstOf ``List.nil do
    throwError "coefficient control inventory bound exhausted"
  let invalid ← GuardCoefficientIndex.positionProof agreement type size
  let remaining ← bounded began
  let options := maxHeartbeats.set ((← getOptions).setBool `debug.skipKernelTC false) remaining
  match (← getEnv).toKernelEnv.addDecl options (.thmDecl {
      name := `__incorrectCoefficientPosition, levelParams := [], type, value := invalid }) with
  | .ok _ => throwError "kernel accepted an out-of-range native coefficient hint"
  | .error (.appTypeMismatch ..) => pure ()
  | .error (.declTypeMismatch ..) => pure ()
  | .error (.exprTypeMismatch ..) => pure ()
  | .error error => ofExceptKernelException (Except.error error)
  logInfo m!"actual coefficient index module control: originalInventorySize={size} correctPositionAccepted=true sameOriginalRequestWithOutOfRangePositionRejected=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardCoefficientControl
