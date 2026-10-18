/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingShape
public import KernelReplay.GuardCoefficientReduce
public meta import KernelReplay.GuardRemainingShape
public meta import KernelReplay.GuardCoefficientReduce
import all KernelReplay.GuardRemainingShape
import all KernelReplay.GuardCoefficientReduce
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingInputs
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

def node (record index : Nat) : MetaM (Expr × Array Expr) := do
  let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape ++
    Name.mkSimple s!"record{record}" ++ Name.mkSimple s!"node{index}"
  let type ← withTransparency .all (whnf (mkConst name))
  unless type.getAppFn.isConstOf ``Packing.NodeData do throwError "remaining packing node changed"
  let parts ← fields type ``Packing.NodeData.mk
  unless parts.size == 5 do throwError "remaining packing node fields changed"
  return (type, parts)

def query (record nodeIndex index : Nat) : MetaM Expr := do
  let (_, parts) ← node record nodeIndex
  let .forallE _ domain body _ := parts[4]! | throwError "remaining packing query lost its index"
  unless domain.getAppFn.isConstOf ``Fin do throwError "remaining packing moment index changed"
  let bound := domain.getAppArgs.back!
  let equation ← mkAppM ``Nat.lt #[toExpr index, bound]
  let dictionary ← mkAppM ``Nat.decLt #[toExpr index, bound]
  let decision := mkAppN (mkConst ``decide) #[equation, dictionary]
  let checked ← mkEqRefl (toExpr true)
  let positive ← mkAppOptM ``of_decide_eq_true #[some equation, some dictionary, some checked]
  let positive ← withTransparency .all do mkAppOptM ``id #[some equation, some positive]
  kernelCheck `__remainingPackingMomentIndex (← mkEq decision (toExpr true)) checked
  let position ← mkAppOptM ``Fin.mk #[some bound, some (toExpr index), some positive]
  let type := body.instantiate1 position
  unless type.getAppFn.isConstOf ``Packing.QueryData do throwError "remaining packing query changed"
  return type

syntax (name := remainingInputControl) "#remaining_packing_inputs " num num : command
@[command_elab remainingInputControl]
unsafe def elaborate : CommandElab := fun stx => liftTermElabM <| withExporting (isExporting := false) do
  let some record := stx[1].isNatLit? | throwError "remaining record index is not literal"
  let some nodeIndex := stx[2].isNatLit? | throwError "remaining node index is not literal"
  let began ← IO.getNumHeartbeats
  let setup ← GuardDescriptorInputs.prepare
  let origin ← Base.ofClosed (mkConst ``GuardInventoryReplay.closed)
  let indexed ← GuardCoefficientReduce.prepare began (mkConst ``GuardInventoryReplay.agreement)
  let domains := origin.domains indexed
  let known ← IO.mkRef (#[] : Array KnownLookup)
  let supplier := origin.supply domains (lookupSupplier known FiniteDataProbe.supply)
  let (_, parts) ← node record nodeIndex
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingInputs ++
    Name.mkSimple s!"record{record}" ++ Name.mkSimple s!"node{nodeIndex}"
  let mut proofs := #[]
  for (tag, part) in #[`head, `preparation, `products, `reductions].zip (parts.extract 0 4) do
    let remaining ← bounded began
    logInfo m!"actual remaining packing input begins: record={record} node={nodeIndex} field={tag} heartbeat={1500000 - remaining}"
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supplier
    let proof ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
  logInfo m!"actual remaining packing inputs module export: originalRecordIndex={record} originalNodeIndex={nodeIndex} fields=4 allOriginalGuardsRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingInputs
