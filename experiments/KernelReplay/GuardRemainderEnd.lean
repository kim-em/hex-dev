/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainderStart
public meta import KernelReplay.GuardRemainderStart
import all KernelReplay.GuardRemainderStart
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainderEnd
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := remainderEndControl) "#remainder_end_control" : command
@[command_elab remainderEndControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart,
      `KernelReplay.GuardRemainderStart]
  let (type, parts) ← GuardRemainderStart.view supply.setup
  kernelCheck `__sameActualRemainderChain
    (← mkEq type (mkConst ``GuardRemainderStart.statement)) (← mkEqRefl type)
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainderEnd
  let mut proofs := supply.facts
  let mut result := mkAppN (mkConst ``Packing.ChainData.mk type.getAppFn.constLevels!) type.getAppArgs
  for field in #[``GuardRemainderStart.head, ``GuardRemainderStart.rows,
      ``GuardRemainderStart.initial, ``GuardRemainderStart.initialLeft,
      ``GuardRemainderStart.initialRight] do result := mkApp result (mkConst field)
  for (tag, part) in (#[`recurrences, `stepLeft, `stepRight, `terminal, `terminalSign]).zip
      (parts.extract 5 10) do
    let remaining ← bounded began
    logInfo m!"actual second remainder chain begins: field={tag} heartbeat={1500000 - remaining}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"actual remainder ending begins: field={tag} heartbeat={1500000 - remaining}"
        handle.flush
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    result := mkApp result proof
    logInfo m!"actual second remainder chain checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let complete ← retain began (root ++ `chain) result
  logInfo m!"actual second remainder chain module export: index=1 fields=10 sameOriginalChainChecked=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#remainder_end_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainderEnd
