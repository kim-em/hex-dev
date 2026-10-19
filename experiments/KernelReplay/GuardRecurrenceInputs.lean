/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRecurrenceShape
public meta import KernelReplay.GuardRecurrenceShape
import all KernelReplay.GuardRecurrenceShape
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceInputs
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

/-- The actual recurrence at index zero of the checked one-step family. -/
def view (setup : Setup) : MetaM (Expr × Array Expr) := do
  let (family, bound, size) ← GuardRecurrenceShape.family setup
  unless size == 1 do throwError "actual third remainder no longer has exactly one recurrence"
  kernelCheck `__oneActualRecurrence (← mkEq bound (toExpr (1 : Nat)))
    (mkConst ``GuardRecurrenceShape.count_eq)
  let .forallE _ _ body _ := family | throwError "actual recurrence index disappeared"
  let .forallE _ _ data _ := body.instantiate1 (toExpr (0 : Nat)) |
    throwError "actual recurrence index guard disappeared"
  if data.hasLooseBVars || data.hasFVar || data.hasMVar then
    throwError "actual recurrence data depends on an unresolved guard"
  unless data.getAppFn.isConstOf ``Packing.RecurrenceData do throwError "actual recurrence data changed"
  let parts ← fields data ``Packing.RecurrenceData.mk
  unless parts.size == 5 do throwError "actual recurrence fields changed"
  return (data, parts)

syntax (name := recurrenceInputsControl) "#recurrence_inputs_control" : command
@[command_elab recurrenceInputsControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart,
      `KernelReplay.GuardRemainderStart, `KernelReplay.GuardLastChainStart,
      `KernelReplay.GuardLastRemainderStart]
  let (type, parts) ← view supply.setup
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceInputs
  let _ ← retain began (root ++ `statement) type
  let mut proofs := supply.facts.push (mkConst ``GuardRecurrenceShape.count_eq)
  for (tag, part) in (#[`leftScale, `quotientProduct]).zip (parts.extract 0 2) do
    let remaining ← bounded began
    logInfo m!"actual unique recurrence begins: field={tag} heartbeat={1500000 - remaining}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"actual unique recurrence begins: field={tag} heartbeat={1500000 - remaining}"
        handle.flush
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    logInfo m!"actual unique recurrence checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  logInfo m!"actual unique recurrence input module export: index=0 totalRecurrences=1 fields=2 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#recurrence_inputs_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceInputs
