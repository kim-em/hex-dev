/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardBaseAgreement129
import KernelReplay.GuardBasePrefixAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardBaseAllAudit
open Lean Meta Elab GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let original := (← getConstInfo ``GuardInventoryReplay.agreement).type
  let parameters := original.getAppArgs
  let mut proofs := #[mkConst ``GuardDescriptorInputs.firstPointBinding]
  let mut checked : Nat := 0
  for index in [:2203] do
    let name := `Hex.RealClosure.Algebraic.KernelReplay.GuardBaseAgreement ++
      Name.mkSimple s!"block{index}"
    let info ← getConstInfo name
    unless info.isTheorem && info.levelParams.isEmpty &&
        info.type.getAppFn.isConstOf ``Transport.Inventory.Agreement do
      throwError "original coefficient block has no complete checked agreement: {name}"
    let arguments := info.type.getAppArgs
    unless arguments.size == parameters.size &&
        arguments.extract 0 (arguments.size-1) == parameters.extract 0 (parameters.size-1) do
      throwError "original block changed its base reader, domain or sign callbacks: {index}"
    proofs := proofs.push (mkConst name)
    checked := checked + 1
  unless checked == 2203 do throwError "complete original basis audit omitted a block"
  let count ← audit began proofs
  logInfo m!"all original base agreement blocks module audit: start=0 limit=2203 completeOriginalBlocks=2203 originalReaderDomainAndSignCallbacksRetained=true domainSignAndZeroReflectionRetained=true sameBaseInterpretation=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardBaseAllAudit
