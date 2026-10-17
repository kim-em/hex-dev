/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardLastChainEnd
public meta import KernelReplay.GuardLastChainEnd
import all KernelReplay.GuardLastChainEnd
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderStart
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

def view (setup : Setup) : MetaM (Expr × Array Expr) := do
  let query ← GuardMomentFirst.query setup 2
  let parts ← fields query ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual third moment query fields changed"
  let type := parts[1]!
  unless type.getAppFn.isConstOf ``Packing.ChainData do throwError "missing actual third remainder chain"
  let parts ← fields type ``Packing.ChainData.mk
  unless parts.size == 10 do throwError "actual third remainder chain fields changed"
  return (type, parts)

syntax (name := lastRemainderStartControl) "#last_remainder_start_control" : command
@[command_elab lastRemainderStartControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart,
      `KernelReplay.GuardRemainderStart, `KernelReplay.GuardLastChainStart]
  let (type, parts) ← view supply.setup
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderStart
  let _ ← retain began (root ++ `statement) type
  let mut proofs := supply.facts
  for (tag, part) in (#[`head, `rows, `initial, `initialLeft, `initialRight]).zip (parts.extract 0 5) do
    let remaining ← bounded began
    logInfo m!"actual third remainder chain begins: field={tag} heartbeat={1500000 - remaining}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"actual third remainder begins: field={tag} heartbeat={1500000 - remaining}"
        handle.flush
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    logInfo m!"actual third remainder chain checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  logInfo m!"actual third remainder chain module export: index=2 totalMoments=3 fields=5 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#last_remainder_start_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderStart
