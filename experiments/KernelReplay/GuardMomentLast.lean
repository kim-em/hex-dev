/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardLastRemainderEnd
public meta import KernelReplay.GuardLastRemainderEnd
import all KernelReplay.GuardLastRemainderEnd
import all KernelReplay.GuardLastChainEnd
import all KernelReplay.GuardMomentFirst
import all KernelReplay.GuardMomentSecond
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentLast
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := lastMomentControl) "#last_moment_control" : command
@[command_elab lastMomentControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
    #[`KernelReplay.GuardChainStart, `KernelReplay.GuardNextChainStart,
      `KernelReplay.GuardRemainderStart, `KernelReplay.GuardLastChainStart,
      `KernelReplay.GuardLastRemainderStart, `KernelReplay.GuardRecurrenceInputs]
  let type ← GuardMomentFirst.query supply.setup 2
  let parts ← fields type ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual third query fields changed"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardMomentLast
  let _ ← retain began (root ++ `statement) type
  let mut result := mkAppN (mkConst ``Packing.QueryData.mk type.getAppFn.constLevels!) type.getAppArgs
  let mut proofs := supply.facts.push (mkConst ``GuardMomentSecond.momentCount_eq)
  for (tag, part) in (#[`squarefree, `remainders, `order, `lower, `upper, `lowerRows, `upperRows]).zip parts do
    let remaining ← bounded began
    logInfo m!"actual third query begins: field={tag} heartbeat={1500000 - remaining}"
    let proof ← if tag == `squarefree || tag == `remainders then do
        let original := if tag == `squarefree then mkConst ``GuardLastChainEnd.chain
          else mkConst ``GuardLastRemainderEnd.chain
        withOptions (maxHeartbeats.set · remaining) do
          kernelCheck `__actualThirdQueryChain part original
        pure original
      else withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let typed ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
    let proof ← retain began (root ++ tag) typed
    proofs := proofs.push proof
    result := mkApp result proof
    logInfo m!"actual third query checked: field={tag} heartbeat={((← IO.getNumHeartbeats) - began) / 1000}"
  let complete ← retain began (root ++ `data) result
  logInfo m!"actual complete third moment query module export: index=2 totalMoments=3 fields=7 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#last_moment_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentLast
