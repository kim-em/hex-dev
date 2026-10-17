/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingShape
public meta import KernelReplay.GuardPackingShape
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingNodeInputs
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

def node (index : Nat) : MetaM (Expr × Array Expr) := do
  let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingShape ++
    Name.mkSimple s!"node{index}"
  let type ← withTransparency .all (whnf (mkConst name))
  unless type.getAppFn.isConstOf ``Packing.NodeData do
    throwError "actual first packing node changed"
  let parts ← fields type ``Packing.NodeData.mk
  unless parts.size == 5 do throwError "actual first packing node fields changed"
  return (type, parts)

def query (nodeIndex index : Nat) : MetaM Expr := do
  let (_, parts) ← node nodeIndex
  let .forallE _ domain body _ := parts[4]! | throwError "packing moment family lost its index"
  unless domain.getAppFn.isConstOf ``Fin do throwError "packing moment index is not finite"
  let bound := domain.getAppArgs.back!
  let equation ← mkAppM ``Nat.lt #[toExpr index, bound]
  let dictionary ← mkAppM ``Nat.decLt #[toExpr index, bound]
  let decision := mkAppN (mkConst ``decide) #[equation, dictionary]
  let checked ← mkEqRefl (toExpr true)
  let positive ← mkAppOptM ``of_decide_eq_true #[some equation, some dictionary, some checked]
  let positive ← withTransparency .all do mkAppOptM ``id #[some equation, some positive]
  kernelCheck `__actualPackingMomentIndex (← mkEq decision (toExpr true)) checked
  let position ← mkAppOptM ``Fin.mk #[some bound, some (toExpr index), some positive]
  let type := body.instantiate1 position
  unless type.getAppFn.isConstOf ``Packing.QueryData do throwError "actual packing query changed"
  return type

syntax (name := packingNodeInputControl) "#packing_node_inputs" : command
@[command_elab packingNodeInputControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
  let (_, parts) ← node 0
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingNodeInputs
  let mut proofs := supply.facts
  for (tag, part) in #[`head, `preparation, `products, `reductions].zip (parts.extract 0 4) do
    let remaining ← bounded began
    logInfo m!"actual first packing root input begins: field={tag} heartbeat={1500000 - remaining}"
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
  logInfo m!"actual first packing root inputs module export: fields=4 allOriginalGuardsRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_node_inputs

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingNodeInputs
