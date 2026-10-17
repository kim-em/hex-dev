/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardMomentFirst
public meta import KernelReplay.GuardMomentFirst
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardNextChainStart
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

/-- The next actual query's own squarefree chain. No comparison with a
different query's certificate is needed to construct its finite premises. -/
def view (setup : Setup) : MetaM (Expr × Array Expr) := do
  let type ← GuardMomentFirst.query setup 1
  let parts ← fields type ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual second query fields changed"
  let chain := parts[0]!
  unless chain.getAppFn.isConstOf ``Packing.ChainData do throwError "missing actual second squarefree chain"
  let fields ← GuardDescriptorInputs.fields chain ``Packing.ChainData.mk
  unless fields.size == 10 do throwError "actual next signed chain fields changed"
  return (chain, fields)

syntax (name := nextChainStartControl) "#next_chain_start_control" : command
@[command_elab nextChainStartControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  -- The retained complete first chain is deliberately absent from this search.
  let supply ← GuardDescriptorSupplier.prepare began #[`KernelReplay.GuardChainStart]
  let (type, parts) ← view supply.setup
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardNextChainStart
  let _ ← retain began (root ++ `statement) type
  let mut proofs := supply.facts
  for (tag, part) in (#[`head, `rows, `initial, `initialLeft, `initialRight]).zip (parts.extract 0 5) do
    let remaining ← bounded began
    logInfo m!"actual second signed chain begins: field={tag} heartbeat={1500000 - remaining}"
    if let some path ← IO.getEnv "HEX_NATIVE_ASSEMBLY_TRACE" then
      IO.FS.withFile path .append fun handle => do
        handle.putStrLn s!"actual next chain begins: field={tag} heartbeat={1500000 - remaining}"
        handle.flush
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    logInfo m!"actual second signed chain checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  logInfo m!"actual second signed chain module export: index=1 fields=5 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#next_chain_start_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardNextChainStart
