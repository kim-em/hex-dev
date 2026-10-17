/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRight
public meta import KernelReplay.GuardPackingRight
import all KernelReplay.GuardPackingRight
import all KernelReplay.GuardPackingRoot
import all KernelReplay.GuardPackingBranch
import all KernelReplay.GuardPackingLeaf
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRecord
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

private def typed (type value : Expr) : MetaM Expr := withTransparency .all do
  mkAppOptM ``id #[some type, some value]

/-- Rebuild the original full conjunction tree, checking every node in its
original position. No split child or moment family is omitted. -/
private def tree (type : Expr) (proofs : Array Expr) (cursor : Nat := 0)
    (fuel : Nat := 64) : MetaM (Expr × Nat) := do
  let fuel + 1 := fuel | throwError "actual packing replay assembly bound exhausted"
  let reduced ← withOptions (smartUnfolding.set · true) do
    withTransparency .all (whnf type)
  if reduced.getAppFn.isConstOf ``Packing.NodeData then
    let some proof := proofs[cursor]? | throwError "missing original packing node proof"
    kernelCheck `__actualPackingReplayNode reduced proof
    return (← typed type proof, cursor + 1)
  unless reduced.getAppFn.isConstOf ``And do
    throwError "unexpected original packing replay predicate"
  let args := reduced.getAppArgs
  let (left, cursor) ← tree args[0]! proofs cursor fuel
  let (right, cursor) ← tree args[1]! proofs cursor fuel
  return (← typed type (← mkAppM ``And.intro #[left, right]), cursor)

syntax (name := packingRecordControl) "#packing_record_control" : command
@[command_elab packingRecordControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
  let first := supply.setup.first
  let target ← withTransparency .all (whnf (mkConst ``GuardPackingShape.target))
  let parts ← fields target ``Packing.Data.mk
  unless parts.size == 2 do throwError "actual first packing record fields changed"
  let allNodes := #[mkConst ``GuardPackingRoot.data, mkConst ``GuardPackingBranch.data,
    mkConst ``GuardPackingLeaf.data, mkConst ``GuardPackingRight.node3.data,
    mkConst ``GuardPackingRight.node4.data]
  let original := mkConst ``GuardPackingShape.nativeReplayType
  let (native, consumed) ← tree original allNodes
  unless consumed == allNodes.size do throwError "actual packing replay did not use all five nodes"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRecord
  let native ← retain began (root ++ `nativeReplay) (← typed original native)
  let args := parts[0]!.getAppArgs
  unless parts[0]!.getAppFn.isConstOf ``Transport.Finite.ReplayData do
    throwError "actual first packing record lost its transport replay"
  let replay ← mkAppM ``Packing.lift_replay
    (#[first.entries, first.records, first.read, first.zero, first.unit,
      first.descriptor, first.packings, first.signs] ++ args.extract (args.size - 5) args.size ++ #[native])
  let replay ← retain began (root ++ `replay) (← typed parts[0]! replay)
  let remaining ← bounded began
  let difference ← withOptions (maxHeartbeats.set · remaining) do
    build parts[1]! (first.supplyAll supply.supplier)
  let difference ← retain began (root ++ `difference) (← typed parts[1]! difference)
  let value := mkAppN (mkConst ``Packing.Data.mk target.getAppFn.constLevels!)
    (target.getAppArgs ++ #[replay, difference])
  let _complete ← retain began (root ++ `data) (← typed target value)
  logInfo m!"actual complete first packing record module export: originalSecondInventoryIndex=0 fullOriginalReplayNodes=5 everyOriginalSplitChildRetained=true replayAndOriginalDifferenceChecked=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_record_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRecord
