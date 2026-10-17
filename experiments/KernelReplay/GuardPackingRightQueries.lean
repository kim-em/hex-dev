/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRightInputs
public meta import KernelReplay.GuardPackingRightInputs
import all KernelReplay.GuardPackingRightInputs
import all KernelReplay.GuardPackingNodeInputs
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightQueries
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := packingRightQueryControl) "#packing_right_query " num num : command
@[command_elab packingRightQueryControl]
unsafe def elaborate : CommandElab := fun stx => liftTermElabM <| withExporting (isExporting := false) do
  let some nodeIndex := stx[1].isNatLit? | throwError "packing node index is not literal"
  let some index := stx[2].isNatLit? | throwError "packing query index is not literal"
  unless nodeIndex == 3 || nodeIndex == 4 do throwError "expected an original right packing node"
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
  let target ← GuardPackingNodeInputs.query nodeIndex index
  let parts ← fields target ``Packing.QueryData.mk
  unless parts.size == 7 do throwError "actual first packing right query fields changed"
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightQueries ++
    Name.mkSimple s!"node{nodeIndex}" ++ Name.mkSimple s!"query{index}"
  let mut value := mkAppN (mkConst ``Packing.QueryData.mk target.getAppFn.constLevels!) target.getAppArgs
  let mut proofs := supply.facts
  for (tag, part) in #[`squarefree, `remainders, `order, `lower, `upper, `lowerRows, `upperRows].zip parts do
    let remaining ← bounded began
    logInfo m!"actual first packing right query begins: node={nodeIndex} index={index} field={tag} heartbeat={1500000 - remaining}"
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
    value := mkApp value proof
  let _complete ← retain began (root ++ `data) value
  logInfo m!"actual complete first packing right query module export: originalNodeIndex={nodeIndex} index={index} fields=7 sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_right_query 3 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_right_query 3 1

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_right_query 3 2

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_right_query 4 0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_right_query 4 1

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_right_query 4 2

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightQueries
