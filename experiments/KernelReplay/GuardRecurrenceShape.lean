/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardLastRemainderStart
public meta import KernelReplay.GuardLastRemainderStart
import all KernelReplay.GuardLastRemainderStart
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceShape
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

private def phase (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn s!"recurrence shape: {message}"
      handle.flush

private def natural (value : Expr) (fuel : Nat := 64) : MetaM Nat := do
  let fuel + 1 := fuel | throwError "actual recurrence count head bound exhausted"
  let value ← withTransparency .all (whnf value)
  if let some result ← getNatValue? value then return result
  if value.getAppFn.isConstOf ``Nat.succ then
    return (← natural value.getAppArgs.back! fuel) + 1
  throwError "actual recurrence count has unsupported head {value.getAppFn.constName?}"

/-- The exact bounded recurrence family from the third remainder chain. -/
def family (setup : Setup) : MetaM (Expr × Expr × Nat) := do
  phase "select actual third remainder chain"
  let (_, parts) ← GuardLastRemainderStart.view setup
  let type := parts[5]!
  let .forallE _ domain body _ := type | throwError "actual recurrences have no index"
  unless domain.isConstOf ``Nat do throwError "actual recurrence index is not natural"
  let .forallE _ inequality _ _ := body | throwError "actual recurrence index lost its bound"
  let bound := inequality.getAppArgs.back!
  if bound.hasLooseBVars then throwError "actual recurrence bound depends on its index"
  phase "read actual step-count head"
  let size ← natural bound
  phase s!"step count read: {size}"
  return (type, bound, size)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
run_meta withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  phase "prepare original first reader"
  let setup ← GuardDescriptorInputs.prepare
  let (type, bound, size) ← family setup
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceShape
  phase "retain original family"
  let _ ← retain began (root ++ `statement) type
  let value ← retain began (root ++ `count) (toExpr size)
  let equation ← mkEq bound value
  phase "construct kernel count binding"
  let proof ← withTransparency .all do
    mkAppOptM ``id #[some equation, some (← mkEqRefl (toExpr size))]
  let proof ← retain began (root ++ `count_eq) proof
  phase "count binding kernel checked"
  let .forallE _ _ body _ := type | throwError "actual recurrence index disappeared"
  let mut fieldCounts : Array Nat := #[]
  for index in [:size] do
    let indexed := body.instantiate1 (toExpr index)
    let .forallE _ _ body _ := indexed | throwError "actual recurrence guard disappeared"
    if body.hasLooseBVars then throwError "actual recurrence data depends on its proof guard"
    unless body.getAppFn.isConstOf ``Packing.RecurrenceData do
      throwError "actual recurrence data changed its predicate"
    let parts ← fields body ``Packing.RecurrenceData.mk
    fieldCounts := fieldCounts.push parts.size
  logInfo m!"actual third remainder recurrence census module export: originalFamilyBound={size} fieldsPerRecurrence={fieldCounts} kernelCountBindingChecked=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceShape
