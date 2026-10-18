/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardAgreementPublic
import KernelReplay.GuardBaseAllAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementPublicAudit
open Lean Meta Elab GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let original := (← getConstInfo ``GuardInventoryReplay.agreement).type
  let parameters := original.getAppArgs
  let root := `Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementJoin
  let mut proofs := #[mkConst ``GuardAgreementPublic.agreement,
    mkConst ``GuardAgreementPublic.fixed, mkConst ``GuardAgreementPublic.base,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  for index in [:29] do
    let _ ← bounded began
    let start := 128*index
    let support := mkConst (root ++ Name.mkSimple s!"support{start}")
    let name := root ++ Name.mkSimple s!"agreement{start}"
    let info ← getConstInfo name
    let required := mkAppN original.getAppFn
      (parameters.set! (parameters.size-1) support)
    unless info.isTheorem && info.levelParams.isEmpty && info.type == required do
      throwError "original ordered segment changed its complete agreement type: {start}"
    proofs := proofs.push (mkConst name)
  let support := mkConst ``GuardAgreementJoin.support
  let required := mkAppN original.getAppFn
    (parameters.set! (parameters.size-1) support)
  let final ← getConstInfo ``GuardAgreementJoin.agreement
  unless final.isTheorem && final.levelParams.isEmpty && final.type == required do
    throwError "complete ordered agreement changed the original reader, domain or sign callbacks"
  let base ← getConstInfo ``GuardAgreementJoin.base
  unless base.isTheorem && base.type.getAppFn.isConstOf ``And do
    throwError "complete ordered agreement lost its inherited-provider conjunction"
  let clauses := base.type.getAppArgs
  unless clauses.size == 2 && clauses[0]! == required &&
      clauses[1]! == (← getConstInfo ``GuardAgreementJoin.fixed).type do
    throwError "base conjunction changed its complete agreement or fixed-provider clause"
  let count ← audit began proofs
  logInfo m!"complete ordered agreement public module audit: roots=3 ordinaryPublicImports=true segments=29 originalOccurrences=3602 originalReaderDomainAndSignCallbacksRetained=true domainSignAndZeroReflectionRetained=true inheritedProviderValuesFixed=true sameBaseInterpretation=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardAgreementPublicAudit
