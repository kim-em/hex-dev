/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardNextChainEnd
public meta import KernelReplay.GuardNextChainEnd
import all KernelReplay.GuardNextChainEnd
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainderStart
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

/-- The actual second moment's retained query remainder chain. -/
def view (setup : Setup) : MetaM (Expr × Array Expr) := do
  let query ← GuardMomentFirst.query setup 1
  let parts ← fields query ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual second moment query fields changed"
  let type := parts[1]!
  unless type.getAppFn.isConstOf ``Packing.ChainData do throwError "missing actual second remainder chain"
  let parts ← fields type ``Packing.ChainData.mk
  unless parts.size == 10 do throwError "actual second remainder chain fields changed"
  return (type, parts)

syntax (name := remainderStartControl) "#remainder_start_control" : command
@[command_elab remainderStartControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart]
  let (type, parts) ← view supply.setup
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainderStart
  let _ ← retain began (root ++ `statement) type
  let mut proofs := supply.facts
  for (tag, part) in (#[`head, `rows, `initial, `initialLeft, `initialRight]).zip (parts.extract 0 5) do
    let remaining ← bounded began
    logInfo m!"actual second remainder chain begins: field={tag} heartbeat={1500000 - remaining}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"actual second remainder begins: field={tag} heartbeat={1500000 - remaining}"
        handle.flush
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    logInfo m!"actual second remainder chain checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  logInfo m!"actual second remainder chain module export: index=1 fields=5 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#remainder_start_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainderStart
