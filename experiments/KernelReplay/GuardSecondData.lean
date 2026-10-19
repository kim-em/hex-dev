/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingRecord2
public meta import KernelReplay.GuardRemainingRecord2
import all KernelReplay.GuardRemainingRecord2
import all KernelReplay.GuardRemainingRecords
import all KernelReplay.GuardRemainingShape
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardPackingRecord
import all KernelReplay.GuardDescriptorPoint
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardInventoryReplay

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardSecondData

private theorem three {α : Type u} {p : α → Prop} {a b c : α}
    (ha : p a) (hb : p b) (hc : p c) : ∀ x ∈ [a, b, c], p x := by
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx
  · exact ha
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hb
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hc
  cases hx

private theorem empty {α : Type u} {p : α → Prop} : ∀ x ∈ ([] : List α), p x := by
  intro x hx
  cases hx

end Hex.RealClosure.Algebraic.KernelReplay.GuardSecondData

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardSecondData
open Lean Meta Elab FiniteData GuardDescriptorInputs


private def typed (type value : Expr) : MetaM Expr := withTransparency .all do
  mkAppOptM ``id #[some type, some value]

private def emptyProof (type : Expr) : MetaM Expr := forallTelescope type fun args result => do
  unless args.size == 2 do throwError "empty inventory predicate changed"
  let predicate ← mkLambdaFVars #[args[0]!] result
  mkAppOptM ``empty #[some (← inferType args[0]!), some predicate]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let setup ← GuardDescriptorInputs.prepare
  let target ← mkAppM ``Packing.Inventory.Data
    #[setup.context, mkConst ``GuardInventoryReplay.second.entries,
      mkConst ``GuardInventoryReplay.second.records,
      mkConst ``GuardInventoryReplay.second.facts, setup.first.reader]
  let parts ← fields target ``Packing.Inventory.Data.mk
  unless parts.size == 4 do throwError "original second inventory fields changed"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardSecondData
  let descriptor ← retain began (root ++ `descriptor)
    (← typed parts[0]! (mkConst ``GuardDescriptorPoint.descriptorData))
  let packings ← forallTelescope parts[1]! fun args result => do
    unless args.size == 2 do throwError "original packing inventory predicate changed"
    let predicate ← mkLambdaFVars #[args[0]!] result
    withTransparency .all do
      mkAppOptM ``three #[some (← inferType args[0]!), some predicate,
        some (mkConst ``GuardPackingShape.entry),
        some (mkConst ``GuardRemainingShape.record1.entry),
        some (mkConst ``GuardRemainingShape.record2.entry),
        some (mkConst ``GuardPackingRecord.data),
        some (mkConst ``GuardRemainingRecords.record1.data),
        some (mkConst ``GuardRemainingRecords.record2.data)]
  let packings ← retain began (root ++ `packings) (← typed parts[1]! packings)
  let signs ← retain began (root ++ `signs) (← typed parts[2]! (← emptyProof parts[2]!))
  let inverses ← retain began (root ++ `inverses) (← typed parts[3]! (← emptyProof parts[3]!))
  let proofs := #[descriptor, packings, signs, inverses]
  let value := mkAppN (mkConst ``Packing.Inventory.Data.mk target.getAppFn.constLevels!)
    (target.getAppArgs ++ proofs)
  let data ← retain began (root ++ `data) (← typed target value)
  let second ← Prefix.ofData data (mkConst ``GuardDescriptorPoint.zero)
    (mkConst ``GuardDescriptorPoint.unit)
  let point ← retain began (root ++ `point) second.point
  let pointBinding ← retain began (root ++ `pointBinding)
    (← typed (← mkEq point (mkConst ``GuardDescriptorPoint.point))
      (← mkEqRefl (mkConst ``GuardDescriptorPoint.point)))
  let reader ← retain began (root ++ `reader) second.reader
  let equations ← retain began (root ++ `equations) second.equations
  logInfo m!"actual complete second inventory module export: originalOrderedPackings=3 allOriginalPackingReplayNodes=15 cachedSigns=0 inverseFacts=0 completeOriginalDescriptor=true sameFirstReader=true sameSelectedSecondPointKernelChecked=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardSecondData
