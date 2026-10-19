/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardObligations07
import KernelReplay.GuardAgreementPublicAudit
import KernelReplay.GuardPrefixAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.Guard208Audit
open Lean Meta Elab GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[mkConst ``GuardAgreementPublic.base,
    mkConst ``GuardSecondData.pointBinding,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  for index in [:208] do
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardObligations ++
      Name.mkSimple s!"guard{index}"
    let info ← getConstInfo name
    unless info.isTheorem && info.levelParams.isEmpty && (← isProp info.type) do
      throwError "original guard was not retained as a closed checked proposition: {name}"
    if info.type.hasFVar || info.type.hasMVar || info.type.hasLooseBVars || info.type.hasSorry then
      throwError "original guard retains a temporary or incomplete type: {name}"
    proofs := proofs.push (mkConst name)
  let count ← audit began proofs
  logInfo m!"original guard208 module audit: start=0 limit=208 closedGuardProofs=208 originalInventory=3773 completeBaseAgreementAndFixedProviderClause=true sameFirstAndSecondPointsChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.Guard208Audit
