/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingNodes
public meta import KernelReplay.GuardRemainingNodes
import all KernelReplay.GuardRemainingNodes
import all KernelReplay.GuardRemainingShape
import all KernelReplay.GuardCoefficientFence
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecords
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

private def typed (type value : Expr) : MetaM Expr := withTransparency .all do
  mkAppOptM ``id #[some type, some value]

/-- Expand the checked census entries before native coefficient evaluation. -/
private def expandEntries (value : Expr) : MetaM Expr := do
  let mut value := value
  for name in #[``GuardRemainingShape.record1.entry, ``GuardRemainingShape.record2.entry] do
    let .defnInfo info ← getConstInfo name | throwError "packing entry is not checked data"
    value := value.replace fun expression =>
      if expression.isConstOf name then some info.value else none
  return value

private def tree (type : Expr) (proofs : Array Expr) (cursor : Nat := 0)
    (fuel : Nat := 64) : MetaM (Expr × Nat) := do
  let fuel + 1 := fuel | throwError "remaining packing replay assembly bound exhausted"
  let reduced ← withOptions (smartUnfolding.set · true) do
    withTransparency .all (whnf type)
  if reduced.getAppFn.isConstOf ``Packing.NodeData then
    let some proof := proofs[cursor]? | throwError "missing original remaining node proof"
    kernelCheck `__remainingOriginalReplayNode reduced proof
    return (← typed type proof, cursor + 1)
  unless reduced.getAppFn.isConstOf ``And do throwError "unexpected original remaining replay predicate"
  let args := reduced.getAppArgs
  let (left, cursor) ← tree args[0]! proofs cursor fuel
  let (right, cursor) ← tree args[1]! proofs cursor fuel
  return (← typed type (← mkAppM ``And.intro #[left, right]), cursor)

syntax (name := remainingRecordControl) "#remaining_packing_record " num : command
@[command_elab remainingRecordControl]
unsafe def elaborate : CommandElab := fun stx => liftTermElabM <| withExporting (isExporting := false) do
  let some record := stx[1].isNatLit? | throwError "remaining packing record index is not literal"
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
  let first := supply.setup.first
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let domains ← GuardCoefficientFence.prepare began origin (mkConst ``GuardInventoryReplay.agreement)
    (compileValue := expandEntries)
  let fallback : Supplier := fun type => do
    if type.getAppFn == origin.domain.getAppFn then domains type else supply.supplier type
  let supplier := first.supplyAll (origin.supply domains fallback)
  let recordName := Name.mkSimple s!"record{record}"
  let source := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape ++ recordName
  let target ← withTransparency .all (whnf (mkConst (source ++ `target)))
  let parts ← fields target ``Packing.Data.mk
  unless parts.size == 2 do throwError "actual remaining packing record fields changed"
  let allNodes := (Array.range 5).map fun nodeIndex => mkConst
    (`Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingNodes ++ recordName ++
      Name.mkSimple s!"node{nodeIndex}" ++ `data)
  let original := mkConst (source ++ `nativeReplayType)
  let (native, consumed) ← tree original allNodes
  unless consumed == allNodes.size do throwError "remaining packing replay did not use all five nodes"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecords ++ recordName
  let native ← retain began (root ++ `nativeReplay) (← typed original native)
  let args := parts[0]!.getAppArgs
  unless parts[0]!.getAppFn.isConstOf ``Transport.Finite.ReplayData do
    throwError "actual remaining packing lost its transport replay"
  let replay ← mkAppM ``Packing.lift_replay
    (#[first.entries, first.records, first.read, first.zero, first.unit,
      first.descriptor, first.packings, first.signs] ++ args.extract (args.size - 5) args.size ++ #[native])
  let replay ← retain began (root ++ `replay) (← typed parts[0]! replay)
  let remaining ← bounded began
  let difference ← withOptions (maxHeartbeats.set · remaining) do
    build parts[1]! supplier
  let difference ← retain began (root ++ `difference) (← typed parts[1]! difference)
  let value := mkAppN (mkConst ``Packing.Data.mk target.getAppFn.constLevels!)
    (target.getAppArgs ++ #[replay, difference])
  let _complete ← retain began (root ++ `data) (← typed target value)
  logInfo m!"actual complete remaining packing record module export: originalSecondInventoryIndex={record} fullOriginalReplayNodes=5 everyOriginalSplitChildRetained=true replayAndOriginalDifferenceChecked=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#remaining_packing_record 1

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRecords
