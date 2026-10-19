/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardLastChainStart
public meta import KernelReplay.GuardLastChainStart
import all KernelReplay.GuardLastChainStart
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardMomentSecond
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardLastChainEnd
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := lastChainEndControl) "#last_chain_end_control" : command
@[command_elab lastChainEndControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart,
      `KernelReplay.GuardRemainderStart, `KernelReplay.GuardLastChainStart]
  let (type, parts) ← GuardLastChainStart.view supply.setup
  kernelCheck `__sameActualThirdSignedChain
    (← mkEq type (mkConst ``GuardLastChainStart.statement)) (← mkEqRefl type)
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardLastChainEnd
  let mut proofs := supply.facts
  let mut result := mkAppN (mkConst ``Packing.ChainData.mk type.getAppFn.constLevels!) type.getAppArgs
  for field in #[``GuardLastChainStart.head, ``GuardLastChainStart.rows,
      ``GuardLastChainStart.initial, ``GuardLastChainStart.initialLeft,
      ``GuardLastChainStart.initialRight] do result := mkApp result (mkConst field)
  for (tag, part) in (#[`recurrences, `stepLeft, `stepRight, `terminal, `terminalSign]).zip
      (parts.extract 5 10) do
    let remaining ← bounded began
    logInfo m!"actual third signed chain begins: field={tag} heartbeat={1500000 - remaining}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"actual third chain ending begins: field={tag} heartbeat={1500000 - remaining}"
        handle.flush
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    result := mkApp result proof
    logInfo m!"actual third signed chain checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let complete ← retain began (root ++ `chain) result
  logInfo m!"actual third signed chain module export: index=2 totalMoments=3 fields=10 sameOriginalChainChecked=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#last_chain_end_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardLastChainEnd
