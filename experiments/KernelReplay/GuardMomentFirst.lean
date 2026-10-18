/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardChainEnd
public meta import KernelReplay.GuardChainEnd
import all KernelReplay.GuardChainEnd
import all KernelReplay.GuardChainStart
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentFirst
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

/-- Select an actual moment query with an ordinary checked finite index. -/
def query (setup : Setup) (index : Nat) : MetaM Expr := do
  let .forallE _ indexType body _ := setup.nodeFields[4]! |
    throwError "actual moment family has no finite index"
  unless indexType.getAppFn.isConstOf ``Fin do throwError "actual moment index is not finite"
  let bound := indexType.getAppArgs.back!
  let equation ← mkAppM ``Nat.lt #[toExpr index, bound]
  let dictionary ← mkAppM ``Nat.decLt #[toExpr index, bound]
  let decision := mkAppN (mkConst ``decide) #[equation, dictionary]
  let checked ← mkEqRefl (toExpr true)
  let positive ← mkAppOptM ``of_decide_eq_true #[some equation, some dictionary, some checked]
  -- Fix the actual inequality before using the finite constructor.
  let positive ← withTransparency .all do mkAppOptM ``id #[some equation, some positive]
  kernelCheck `__actualMomentIndex (← mkEq decision (toExpr true)) checked
  let position ← mkAppOptM ``Fin.mk #[some bound, some (toExpr index), some positive]
  let type := body.instantiate1 position
  unless type.getAppFn.isConstOf ``Packing.QueryData do throwError "actual moment query changed"
  return type

syntax (name := firstMomentControl) "#first_moment_control" : command
@[command_elab firstMomentControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  -- Exclude ChainEnd from automatic search: its proof is used only at the
  -- two original first-query fields, with explicit kernel subject checks.
  let supply ← GuardDescriptorSupplier.prepare began #[`KernelReplay.GuardChainStart]
  let type ← query supply.setup 0
  let parts ← fields type ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual first query fields changed"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardMomentFirst
  let _ ← retain began (root ++ `statement) type
  let mut result := mkAppN (mkConst ``Packing.QueryData.mk type.getAppFn.constLevels!) type.getAppArgs
  let mut proofs := supply.facts
  for (tag, part) in (#[`squarefree, `remainders, `order, `lower, `upper, `lowerRows, `upperRows]).zip parts do
    let remaining ← bounded began
    logInfo m!"actual first query begins: field={tag} heartbeat={1500000 - remaining}"
    let proof ← if tag == `squarefree || tag == `remainders then do
        let original := mkConst ``GuardChainEnd.chain
        withOptions (maxHeartbeats.set · remaining) do
          kernelCheck `__actualFirstQueryChain part original
        pure original
      else withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let typed ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
    let proof ← retain began (root ++ tag) typed
    proofs := proofs.push proof
    result := mkApp result proof
    logInfo m!"actual first query checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let complete ← retain began (root ++ `data) result
  logInfo m!"actual first moment query module export: index=0 fields=7 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#first_moment_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentFirst
