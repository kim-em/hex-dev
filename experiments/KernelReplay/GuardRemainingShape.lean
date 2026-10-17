/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRecord
public meta import KernelReplay.GuardPackingRecord
import all KernelReplay.GuardPackingRecord
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape
open Lean Meta Elab FiniteData GuardDescriptorInputs

private def natural (value : Expr) (fuel : Nat := 64) : MetaM Nat := do
  let fuel + 1 := fuel | throwError "remaining packing moment count head bound exhausted"
  let value ← withTransparency .all (whnf value)
  if let some result ← getNatValue? value then return result
  if value.getAppFn.isConstOf ``Nat.succ then
    return (← natural value.getAppArgs.back! fuel) + 1
  throwError "unsupported remaining packing count head"

private def nodes (type : Expr) (fuel : Nat := 64) : MetaM (Array Expr) := do
  let fuel + 1 := fuel | throwError "remaining packing replay tree bound exhausted"
  let reduced ← withOptions (smartUnfolding.set · true) do
    withTransparency .all (whnf type)
  if reduced.getAppFn.isConstOf ``Packing.NodeData then return #[reduced]
  unless reduced.getAppFn.isConstOf ``And do throwError "unexpected remaining replay predicate"
  let args := reduced.getAppArgs
  return (← nodes args[0]! fuel) ++ (← nodes args[1]! fuel)

private def list (began : Nat) (value : Expr) : MetaM (Array Expr) := do
  let mut rest := value
  let mut values := #[]
  for _ in [:128] do
    let _ ← bounded began
    let literal ← withTransparency .all (whnf rest)
    if literal.getAppFn.isConstOf ``List.nil then return values
    unless literal.getAppFn.isConstOf ``List.cons do throwError "remaining inventory is not literal"
    values := values.push literal.getAppArgs[1]!
    rest := literal.getAppArgs[2]!
  throwError "remaining inventory census bound exhausted"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← prepare
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape
  let mut proofs := #[]
  let mut inventories := #[]
  for (tag, source) in #[(`entries, ``GuardInventoryReplay.second.entries),
      (`records, ``GuardInventoryReplay.second.records), (`facts, ``GuardInventoryReplay.second.facts)] do
    let values ← list began (mkConst source)
    let length ← mkAppM ``List.length #[mkConst source]
    let equation ← mkEq length (toExpr values.size)
    let proof ← withTransparency .all do
      mkAppOptM ``id #[some equation, some (← mkEqRefl (toExpr values.size))]
    let proof ← retain began (root ++ tag ++ `length_eq) proof
    proofs := proofs.push proof
    inventories := inventories.push values
  let entries := inventories[0]!
  unless entries.size == 3 do throwError "original second packing inventory changed"
  for index in #[1, 2] do
    let name := root ++ Name.mkSimple s!"record{index}"
    let entry ← retain began (name ++ `entry) entries[index]!
    let target ← mkAppM ``Packing.Data #[entry, setup.first.reader]
    let targetAlias ← retain began (name ++ `target) target
    let parts ← fields target ``Packing.Data.mk
    unless parts.size == 2 do throwError "actual remaining packing fields changed"
    let args := parts[0]!.getAppArgs
    unless parts[0]!.getAppFn.isConstOf ``Transport.Finite.ReplayData do
      throwError "actual remaining packing lost its transport replay"
    let native ← mkAppM ``Packing.ReplayData
      (#[setup.first.entries, setup.first.records, setup.first.read] ++ args.extract (args.size - 5) args.size)
    let nativeAlias ← retain began (name ++ `nativeReplayType) native
    proofs := proofs ++ #[entry, targetAlias, nativeAlias]
    let nodeTypes ← nodes native
    let mut counts := #[]
    for (node, nodeIndex) in nodeTypes.zipIdx do
      let nodeName := name ++ Name.mkSimple s!"node{nodeIndex}"
      let nodeAlias ← retain began nodeName node
      let parts ← fields node ``Packing.NodeData.mk
      let .forallE _ domain _ _ := parts[4]! | throwError "remaining node has no moment index"
      unless domain.getAppFn.isConstOf ``Fin do throwError "remaining moment index changed"
      let bound := domain.getAppArgs.back!
      let count ← natural bound
      let equation ← mkEq bound (toExpr count)
      let proof ← withTransparency .all do
        mkAppOptM ``id #[some equation, some (← mkEqRefl (toExpr count))]
      let proof ← retain began (nodeName ++ `count_eq) proof
      proofs := proofs ++ #[nodeAlias, proof]
      counts := counts.push count
    logInfo m!"actual remaining packing census: originalInventoryIndex={index} nativeReplayNodes={nodeTypes.size} momentsPerNode={counts} everyOriginalMomentBoundKernelChecked=true"
  logInfo m!"actual second inventory census module export: packings={entries.size} cachedSigns={inventories[1]!.size} inverseFacts={inventories[2]!.size} originalLengthsKernelChecked=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape
