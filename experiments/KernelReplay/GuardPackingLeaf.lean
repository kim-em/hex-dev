/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRoot
public meta import KernelReplay.GuardPackingRoot
import all KernelReplay.GuardPackingRoot
import all KernelReplay.GuardPackingNodeInputs
import all KernelReplay.GuardPackingShape
import all KernelReplay.GuardDescriptorInputs
import all KernelReplay.GuardDescriptorSupplier

public meta section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingLeaf
open Lean Meta Elab Command FiniteData GuardDescriptorInputs

syntax (name := packingLeafControl) "#packing_leaf_control" : command
@[command_elab packingLeafControl]
unsafe def elaborate : CommandElab := fun _ => liftTermElabM <| withExporting (isExporting := false) do
  let began ← IO.getNumHeartbeats
  let supply ← GuardDescriptorSupplier.prepare began
  let (target, _) ← GuardPackingNodeInputs.node 2
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingLeaf
  let remaining ← bounded began
  let value ← withOptions (maxHeartbeats.set · remaining) do build target supply.supplier
  let value ← withTransparency .all do mkAppOptM ``id #[some target, some value]
  let _complete ← retain began (root ++ `data) value
  logInfo m!"actual first packing leaf node module export: originalNodeIndex=2 fields=5 allOriginalMomentsAndGuardsRetained=true sameFirstReader=true dependencyAuditPending=true aggregateHeartbeat={((← IO.getNumHeartbeats) - began) / 1000}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
set_option smartUnfolding false in
#packing_leaf_control

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingLeaf
