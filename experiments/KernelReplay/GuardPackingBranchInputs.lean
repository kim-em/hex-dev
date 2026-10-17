/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingLeaf
public meta import KernelReplay.GuardPackingLeaf
import all KernelReplay.GuardPackingLeaf
import all KernelReplay.GuardPackingNodeInputs
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranchInputs
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := packingBranchInputControl) "#packing_branch_inputs" : command
@[command_elab packingBranchInputControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
  let (_, parts) ← GuardPackingNodeInputs.node 1
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranchInputs
  let mut proofs := supply.facts
  for (tag, part) in #[`head, `preparation, `products, `reductions].zip (parts.extract 0 4) do
    let remaining ← bounded began
    logInfo m!"actual first packing branch input begins: node=1 field={tag} heartbeat={1500000 - remaining}"
    let proof ← withOptions (maxHeartbeats.set · remaining) do build part supply.supplier
    let proof ← withTransparency .all do mkAppOptM ``id #[some part, some proof]
    let proof ← retain began (root ++ tag) proof
    proofs := proofs.push proof
  logInfo m!"actual first packing branch inputs module export: originalNodeIndex=1 fields=4 allOriginalGuardsRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_branch_inputs

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranchInputs
