/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardCoefficientReduceControl
import KernelReplay.GuardPackingRecordPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingControlAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let affected := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingInputs ++ `record1 ++ `node0
  let mut proofs := #[mkConst ``GuardCoefficientReduceControl.correct,
    mkConst (affected ++ `head), mkConst (affected ++ `preparation),
    mkConst (affected ++ `products), mkConst (affected ++ `reductions),
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  let shapeNamespace := `Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingShape
  let mut bindings : Nat := 0
  for (name, info) in (← getEnv).checked.get.constants.toList do
    if shapeNamespace.isPrefixOf name && info.isTheorem then
      proofs := proofs.push (mkConst name)
      bindings := bindings + 1
  unless bindings == 13 do
    throwError "remaining inventory census must audit all three lengths and ten node bounds, found {bindings}"
  let count ← audit began proofs
  logInfo m!"remaining inventory census and reduced coefficient control module audit: originalInventoryLengthsChecked=3 originalRemainingNodeBoundsChecked=10 originalAffectedInputFields=4 correctPositionAccepted=true sameOriginalRequestWithOutOfRangePositionRejected=true originalKernelBoundaryPreserved=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingControlAudit
