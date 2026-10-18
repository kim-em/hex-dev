/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardDescriptorPoint
public meta import KernelReplay.GuardDescriptorPoint
import all KernelReplay.GuardDescriptorPoint
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingShape
open Lean Meta Elab FiniteData GuardDescriptorInputs

private def natural (value : Expr) (fuel : Nat := 64) : MetaM Nat := do
  let fuel + 1 := fuel | throwError "actual packing moment count head bound exhausted"
  let value ← withTransparency .all (whnf value)
  if let some result ← getNatValue? value then return result
  if value.getAppFn.isConstOf ``Nat.succ then
    return (← natural value.getAppArgs.back! fuel) + 1
  throwError "unsupported packing moment count head {value.getAppFn.constName?}"

private def nodes (type : Expr) (fuel : Nat := 64) : MetaM (Array Expr) := do
  let fuel + 1 := fuel | throwError "actual packing replay tree bound exhausted"
  let reduced ← withOptions (smartUnfolding.set · true) do
    withTransparency .all (whnf type)
  if reduced.getAppFn.isConstOf ``Packing.NodeData then return #[reduced]
  unless reduced.getAppFn.isConstOf ``And do
    throwError "unexpected actual packing replay predicate {reduced.getAppFn.constName?}"
  let args := reduced.getAppArgs
  return (← nodes args[0]! fuel) ++ (← nodes args[1]! fuel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← prepare
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingShape
  let original := mkConst ``GuardInventoryReplay.second.entries
  let mut rest := original
  let mut entries := #[]
  for _ in [:128] do
    let _ ← bounded began
    let literal ← withTransparency .all (whnf rest)
    if literal.getAppFn.isConstOf ``List.nil then break
    unless literal.getAppFn.isConstOf ``List.cons do throwError "nonliteral second packing inventory"
    entries := entries.push literal.getAppArgs[1]!
    rest := literal.getAppArgs[2]!
  unless (← withTransparency .all (whnf rest)).getAppFn.isConstOf ``List.nil do
    throwError "second packing inventory census bound exhausted"
  let some entry := entries[0]? | throwError "actual second packing inventory is empty"
  let entry ← retain began (root ++ `entry) entry
  let target ← mkAppM ``Packing.Data #[entry, setup.first.reader]
  let _ ← retain began (root ++ `target) target
  let parts ← fields target ``Packing.Data.mk
  unless parts.size == 2 do throwError "actual packing fields changed"
  let args := parts[0]!.getAppArgs
  unless parts[0]!.getAppFn.isConstOf ``Transport.Finite.ReplayData do
    throwError "actual packing lost its original transport replay"
  let native ← mkAppM ``Packing.ReplayData
    (#[setup.first.entries, setup.first.records, setup.first.read] ++ args.extract (args.size - 5) args.size)
  let _ ← retain began (root ++ `nativeReplayType) native
  let nodeTypes ← nodes native
  let mut proofs := #[]
  let mut counts := #[]
  for (node, index) in nodeTypes.zipIdx do
    let name := root ++ Name.mkSimple s!"node{index}"
    let _ ← retain began name node
    let fields ← fields node ``Packing.NodeData.mk
    let .forallE _ domain _ _ := fields[4]! | throwError "actual packing moment family has no index"
    unless domain.getAppFn.isConstOf ``Fin do throwError "actual packing moment index changed"
    let bound := domain.getAppArgs.back!
    let count ← natural bound
    let equation ← mkEq bound (toExpr count)
    let proof ← withTransparency .all do
      mkAppOptM ``id #[some equation, some (← mkEqRefl (toExpr count))]
    let proof ← retain began (name ++ `count_eq) proof
    proofs := proofs.push proof
    counts := counts.push count
  logInfo m!"actual first packing replay census module export: originalSecondPackingEntries={entries.size} nativeReplayNodes={nodeTypes.size} momentsPerNode={counts} everyOriginalMomentBoundKernelChecked=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingShape
