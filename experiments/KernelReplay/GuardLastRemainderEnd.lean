/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRecurrenceEnd
public meta import KernelReplay.GuardRecurrenceEnd
import all KernelReplay.GuardRecurrenceEnd
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier
import all KernelReplay.GuardRecurrenceShape
import all KernelReplay.GuardLastRemainderStart

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderEnd
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := lastRemainderEndControl) "#last_remainder_end_control" : command
@[command_elab lastRemainderEndControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart,
      `KernelReplay.GuardRemainderStart, `KernelReplay.GuardLastChainStart,
      `KernelReplay.GuardLastRemainderStart]
  let (type, parts) ← GuardLastRemainderStart.view supply.setup
  kernelCheck `__sameActualThirdRemainderChain
    (← mkEq type (mkConst ``GuardLastRemainderStart.statement)) (← mkEqRefl type)
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderEnd
  let mut proofs := supply.facts
  let mut result := mkAppN (mkConst ``Packing.ChainData.mk type.getAppFn.constLevels!) type.getAppArgs
  for field in #[``GuardLastRemainderStart.head, ``GuardLastRemainderStart.rows,
      ``GuardLastRemainderStart.initial, ``GuardLastRemainderStart.initialLeft,
      ``GuardLastRemainderStart.initialRight] do result := mkApp result (mkConst field)
  let recurrence ← withTransparency .all do
    mkAppOptM ``id #[some parts[5]!, some (mkConst ``GuardRecurrenceEnd.recurrences)]
  let recurrence ← retain began (root ++ `recurrences) recurrence
  proofs := proofs.push recurrence
  result := mkApp result recurrence
  logInfo "actual third remainder recurrence family reused at its full original target"
  for (tag, part) in (#[`stepLeft, `stepRight, `terminal, `terminalSign]).zip
      (parts.extract 6 10) do
    let remaining ← bounded began
    logInfo m!"actual third remainder chain begins: field={tag} heartbeat={1500000 - remaining}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"actual third remainder ending begins: field={tag} heartbeat={1500000 - remaining}"
        handle.flush
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    result := mkApp result proof
    logInfo m!"actual third remainder chain checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let complete ← retain began (root ++ `chain) result
  logInfo m!"actual third complete remainder chain module export: index=2 totalMoments=3 fields=10 sameOriginalChainChecked=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#last_remainder_end_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderEnd
