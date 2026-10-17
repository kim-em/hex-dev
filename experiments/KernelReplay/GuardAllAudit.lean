/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardObligations445
import KernelReplay.GuardAgreementPublicAudit
import KernelReplay.Guard208Audit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardAllAudit
open Lean Meta Elab GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let templates := GuardFrontier.templates.getState (← getEnv)
  unless templates.size == 3773 do throwError "original complete guard inventory changed"
  let mut proofs := #[mkConst ``GuardAgreementPublic.base,
    mkConst ``GuardSecondData.pointBinding,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  for index in [:3773] do
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardObligations ++
      Name.mkSimple s!"guard{index}"
    let info ← getConstInfo name
    unless info.isTheorem && info.levelParams.isEmpty && (← isProp info.type) do
      throwError "original guard was not retained as a closed checked proposition: {name}"
    if info.type.hasFVar || info.type.hasMVar || info.type.hasLooseBVars || info.type.hasSorry then
      throwError "original guard retains a temporary or incomplete type: {name}"
    proofs := proofs.push (mkConst name)
  let count ← audit began proofs
  logInfo m!"all original guard module audit: start=0 limit=3773 closedGuardProofs=3773 originalInventoryRetained=true completeOrderedBaseAgreementAndFixedProviderClause=true sameFirstAndSecondPointsChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardAllAudit
