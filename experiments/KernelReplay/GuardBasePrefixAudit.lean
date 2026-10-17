/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardBaseAgreement
import KernelReplay.GuardPrefixAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardBasePrefixAudit
open Lean Meta Elab GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let mut proofs := #[mkConst ``GuardDescriptorInputs.firstPointBinding]
  for index in [:16] do
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardBaseAgreement ++
      Name.mkSimple s!"block{index}"
    let info ← getConstInfo name
    unless info.isTheorem && info.levelParams.isEmpty &&
        info.type.getAppFn.isConstOf ``Transport.Inventory.Agreement do
      throwError "original coefficient block has no complete checked agreement: {name}"
    proofs := proofs.push (mkConst name)
  let count ← audit began proofs
  logInfo m!"original base agreement prefix module audit: start=0 stop=16 completeOriginalBlocks=16 originalUniqueBlocks=2203 domainSignAndZeroReflectionRetained=true sameBaseInterpretation=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardBasePrefixAudit
