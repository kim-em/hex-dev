/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardDescriptorSupplier
public meta import KernelReplay.GuardDescriptorSupplier
import all KernelReplay.GuardDescriptorSupplier
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardChainStart
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

/-- The first actual query's complete squarefree chain, with its original
finite index and certificate. Other query indices remain separate obligations. -/
def view (setup : Setup) : MetaM (Expr × Array Expr) := do
  let .forallE _ indexType body _ := setup.nodeFields[4]! |
    throwError "actual moment family has no finite index"
  unless indexType.getAppFn.isConstOf ``Fin do throwError "actual moment index is not finite"
  let bound := indexType.getAppArgs.back!
  let some size ← withTransparency .all (getNatValue? (← reduce bound)) |
    throwError "actual moment index bound is not closed"
  unless size > 0 do throwError "actual descriptor has no first moment"
  let positive ← mkAppM ``Nat.zero_lt_succ #[toExpr (size - 1)]
  let first ← mkAppOptM ``Fin.mk #[some bound, some (toExpr (0 : Nat)), some positive]
  let queryType := body.instantiate1 first
  unless queryType.getAppFn.isConstOf ``Packing.QueryData do
    throwError "actual moment changed its query predicate"
  let queries ← fields queryType ``Packing.QueryData.mk
  unless queries.size == 7 do throwError "actual query fields changed"
  let type := queries[0]!
  unless type.getAppFn.isConstOf ``Packing.ChainData do
    throwError "actual query has no squarefree chain premise"
  let parts ← fields type ``Packing.ChainData.mk
  unless parts.size == 10 do throwError "actual signed chain fields changed"
  return (type, parts)

syntax (name := chainStartControl) "#chain_start_control" : command
@[command_elab chainStartControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
  let (type, parts) ← view supply.setup
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardChainStart
  let _ ← retain began (root ++ `statement) type
  let mut proofs := supply.facts
  for (tag, part) in (#[`head, `rows, `initial, `initialLeft, `initialRight]).zip (parts.extract 0 5) do
    let remaining ← bounded began
    logInfo m!"actual first signed chain begins: field={tag} heartbeat={1500000 - remaining}"
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    logInfo m!"actual first signed chain checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  logInfo m!"actual first signed chain module export: fields=5 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#chain_start_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardChainStart
