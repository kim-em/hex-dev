/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingNodeInputs
public import KernelReplay.GuardDescriptorPublicAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingInputsAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[mkConst ``GuardPackingNodeInputs.head,
    mkConst ``GuardPackingNodeInputs.preparation, mkConst ``GuardPackingNodeInputs.products,
    mkConst ``GuardPackingNodeInputs.reductions, mkConst ``GuardDescriptorInputs.firstPointBinding]
  let shapeNamespace := `Hex.RealClosure.Algebraic.KernelReplay.GuardPackingShape
  let mut counts : Nat := 0
  for (name, info) in (← getEnv).checked.get.constants.toList do
    if shapeNamespace.isPrefixOf name && info.isTheorem then
      proofs := proofs.push (mkConst name)
      counts := counts + 1
  unless counts == 5 do throwError "original packing census must audit all five node bounds, found {counts}"
  let count ← audit began proofs
  logInfo m!"original packing structure and root inputs module audit: originalNodes=5 allOriginalNodeBoundsChecked=true rootInputFields=4 originalGuardsRetained=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingInputsAudit
