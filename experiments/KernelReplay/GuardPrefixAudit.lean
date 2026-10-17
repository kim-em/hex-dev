/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardObligations06
import KernelReplay.GuardFirstPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPrefixAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[mkConst ``GuardSecondData.pointBinding,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  for index in [:192] do
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardObligations ++
      Name.mkSimple s!"guard{index}"
    let info ← getConstInfo name
    unless info.isTheorem && info.levelParams.isEmpty do
      throwError "original guard was not retained as a closed checked theorem: {name}"
    proofs := proofs.push (mkConst name)
  let count ← audit began proofs
  logInfo m!"original guard prefix module audit: start=0 stop=192 allOriginalGuardProofs=192 originalGuard131Included=true completeOriginalTargetsRetained=true sameFirstAndSecondPointsChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPrefixAudit
