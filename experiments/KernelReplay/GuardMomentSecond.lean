/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainderEnd
public meta import KernelReplay.GuardRemainderEnd
import all KernelReplay.GuardRemainderEnd
import all KernelReplay.GuardNextChainEnd
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentSecond
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := secondMomentControl) "#second_moment_control" : command
@[command_elab secondMomentControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart,
      `KernelReplay.GuardRemainderStart]
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardMomentSecond
  let .forallE _ indexType _ _ := supply.setup.nodeFields[4]! |
    throwError "actual moment family has no index"
  unless indexType.getAppFn.isConstOf ``Fin do throwError "actual moment index is not finite"
  let bound := indexType.getAppArgs.back!
  let some size ← withTransparency .all (getNatValue? (← reduce bound)) |
    throwError "actual moment index bound is not a closed natural number"
  let count ← retain began (root ++ `momentCount) (toExpr size)
  let countEquation ← mkEq bound count
  let countProof ← withTransparency .all do
    mkAppOptM ``id #[some countEquation, some (← mkEqRefl (toExpr size))]
  let countProof ← retain began (root ++ `momentCount_eq) countProof
  logInfo m!"actual moment family size kernel checked: count={size}"
  let type ← GuardMomentFirst.query supply.setup 1
  let parts ← fields type ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual second query fields changed"
  let _ ← retain began (root ++ `statement) type
  let mut result := mkAppN (mkConst ``Packing.QueryData.mk type.getAppFn.constLevels!) type.getAppArgs
  let mut proofs := supply.facts.push countProof
  for (tag, part) in (#[`squarefree, `remainders, `order, `lower, `upper, `lowerRows, `upperRows]).zip parts do
    let remaining ← bounded began
    logInfo m!"actual second query begins: field={tag} heartbeat={1500000 - remaining}"
    let proof ← if tag == `squarefree || tag == `remainders then do
        let original := if tag == `squarefree then mkConst ``GuardNextChainEnd.chain
          else mkConst ``GuardRemainderEnd.chain
        withOptions (maxHeartbeats.set · remaining) do
          kernelCheck `__actualSecondQueryChain part original
        pure original
      else withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let typed ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
    let proof ← retain began (root ++ tag) typed
    proofs := proofs.push proof
    result := mkApp result proof
    logInfo m!"actual second query checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let complete ← retain began (root ++ `data) result
  logInfo m!"actual complete second moment query module export: index=1 fields=7 actualMomentCount={size} sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#second_moment_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentSecond
