/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardDescriptorInputs
public import KernelReplay.GuardRecordExt
public meta import KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardRecordReplay
import all KernelReplay.GuardRecordExt
import all KernelReplay.FrameJoint

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardReplayBindings
open Lean Meta Elab GuardDescriptorInputs

private def subject (field : Expr) : MetaM Expr := do
  if let .proj _ _ value := field then return value
  unless field.isApp do throwError "record field lost its subject"
  return field.getAppArgs.back!

private def parts (type proof : Expr) (fuel : Nat := 8) : MetaM (Array Expr) := do
  let fuel + 1 := fuel | throwError "record field conjunction exceeds its bound"
  if type.getAppFn.isConstOf ``And then
    let args := type.getAppArgs
    let left := mkAppN (mkConst ``And.left) #[args[0]!, args[1]!, proof]
    let right := mkAppN (mkConst ``And.right) #[args[0]!, args[1]!, proof]
    return #[left] ++ (← parts args[1]! right fuel)
  return #[proof]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let environment := (← getEnv).checked.get
  let names := environment.constants.fold (fun found name info =>
    if name.toString.startsWith "_private.KernelReplay.GuardRecordReplay." &&
        (name.toString.splitOn "__recordSource").length > 1 && info.isTheorem then
      found.push name else found) (#[] : Array Name)
  unless names.size == 35 do throwError "original record provenance count changed"
  let mut sources : NameSet := {}
  for (name, index) in names.zipIdx do
    let info ← getConstInfo name
    let equation := if info.type.getAppFn.isConstOf ``And then
        info.type.getAppArgs[0]! else info.type
    unless equation.getAppFn.isConstOf ``Eq do throwError "record provenance lost equality"
    let args := equation.getAppArgs
    let fresh ← subject args[1]!
    let original ← subject args[2]!
    let some source := original.constName? | throwError "original record is not named"
    if sources.contains source then throwError "duplicate original replay record"
    sources := sources.insert source
    let type ← inferType original
    let projection ← if type.getAppFn.isConstOf ``Algebraic.Packing then
        pure ``Algebraic.Packing.signs
      else if type.getAppFn.isConstOf ``Algebraic.ValueSign then
        pure ``Algebraic.ValueSign.signs
      else throwError "original record kind changed"
    let oldSigns ← mkAppM projection #[original]
    let freshSigns ← mkAppM projection #[fresh]
    logInfo m!"original full replay binding begins: index={index} source={source}"
    let mut replayProofs := #[]
    for field in #[``SignDet.SelectedSigns.values, ``SignDet.SelectedSigns.evidence] do
      let actual ← mkAppM field #[freshSigns]
      let expected ← mkAppM field #[oldSigns]
      let remaining ← bounded began
      withOptions (maxHeartbeats.set · remaining) do
        kernelCheck `__originalFullReplayBinding (← mkEq actual expected) (← mkEqRefl expected)
      replayProofs := replayProofs.push (← mkEqRefl expected)
    let fieldProofs ← parts info.type (mkConst name)
    let isPacking := type.getAppFn.isConstOf ``Algebraic.Packing
    unless fieldProofs.size == (if isPacking then 4 else 1) do
      throwError "original record data field count changed"
    let rule := if isPacking then ``GuardRecordExt.packing_eq else ``GuardRecordExt.valueSign_eq
    let proof := mkAppN (mkConst rule type.getAppFn.constLevels!)
      (type.getAppArgs ++ #[fresh, original] ++ fieldProofs ++ replayProofs)
    let remaining ← bounded began
    withOptions (maxHeartbeats.set · remaining) do
      kernelCheck `__originalWholeRecordBinding (← mkEq fresh original) proof
    logInfo m!"original full replay binding checked: index={index} completeClaimedVector=true completeOriginalReplay=true entireRecordKernelEqual=true"
  logInfo m!"original replay provenance result: records={sources.size} fullReplayAndClaimedVectorsKernelChecked=true wholeRecordsKernelEqual=true comparisonsOnly=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardReplayBindings
