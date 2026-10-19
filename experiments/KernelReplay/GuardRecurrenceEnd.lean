/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRecurrenceInputs
public meta import KernelReplay.GuardRecurrenceInputs
import all KernelReplay.GuardRecurrenceInputs
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier
import all KernelReplay.GuardRecurrenceShape
import all KernelReplay.GuardLastRemainderStart

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceEnd

private theorem single {p : Nat → Prop} (atZero : p 0) : ∀ i, i < 1 → p i := by
  intro i bound
  have equal : i = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
  cases equal
  exact atZero

end Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceEnd

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceEnd
open Lean Meta Elab Command FiniteData GuardDescriptorInputs


syntax (name := recurrenceEndControl) "#recurrence_end_control" : command
@[command_elab recurrenceEndControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart,
      `KernelReplay.GuardRemainderStart, `KernelReplay.GuardLastChainStart,
      `KernelReplay.GuardLastRemainderStart, `KernelReplay.GuardRecurrenceInputs]
  let (type, parts) ← GuardRecurrenceInputs.view supply.setup
  kernelCheck `__sameActualUniqueRecurrence
    (← mkEq type (mkConst ``GuardRecurrenceInputs.statement)) (← mkEqRefl type)
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceEnd
  let mut proofs := supply.facts
  let mut result := mkAppN (mkConst ``Packing.RecurrenceData.mk type.getAppFn.constLevels!) type.getAppArgs
  result := mkApp2 result (mkConst ``GuardRecurrenceInputs.leftScale)
    (mkConst ``GuardRecurrenceInputs.quotientProduct)
  for (tag, part) in (#[`rightScale, `remainder, `identity]).zip (parts.extract 2 5) do
    let remaining ← bounded began
    logInfo m!"actual unique recurrence begins: field={tag} heartbeat={1500000 - remaining}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"actual unique recurrence ending begins: field={tag} heartbeat={1500000 - remaining}"
        handle.flush
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    result := mkApp result proof
    logInfo m!"actual unique recurrence checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let atZero ← retain began (root ++ `data) result
  let (family, _, size) ← GuardRecurrenceShape.family supply.setup
  unless size == 1 do throwError "actual third remainder recurrence count changed"
  let .forallE _ domain body _ := family | throwError "actual recurrence index disappeared"
  let predicate ← withLocalDeclD `index domain fun index => do
    let .forallE _ _ data _ := body.instantiate1 index | throwError "actual recurrence guard disappeared"
    if data.hasLooseBVars then throwError "actual recurrence data depends on its guard proof"
    mkLambdaFVars #[index] data
  let all ← mkAppOptM ``single #[some predicate, some atZero]
  let all ← withTransparency .all do mkAppOptM ``id #[some family, some all]
  let all ← retain began (root ++ `recurrences) all
  logInfo m!"actual full third remainder recurrence module export: originalFamilyCount=1 completeRecurrenceFields=5 allOriginalIndicesAndGuards=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#recurrence_end_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardRecurrenceEnd
