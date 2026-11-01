/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardAgreementJoin
public import KernelReplay.GuardBaseAllAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardJoinPrefixAudit
open Lean Meta Elab GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let original := (← getConstInfo ``GuardInventoryReplay.agreement).type
  let parameters := original.getAppArgs
  let support := mkConst ``GuardAgreementJoin.support0
  let info ← getConstInfo ``GuardAgreementJoin.agreement0
  let required := mkAppN original.getAppFn
    (parameters.set! (parameters.size-1) support)
  unless info.isTheorem && info.levelParams.isEmpty && info.type == required do
    throwError "first ordered segment changed its exact original agreement type"
  let count ← audit began #[mkConst ``GuardAgreementJoin.agreement0,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  logInfo m!"first original ordered agreement module audit: start=0 limit=128 occurrences=128 originalOccurrences=3602 originalReaderDomainAndSignCallbacksRetained=true domainSignAndZeroReflectionRetained=true sameBaseInterpretation=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardJoinPrefixAudit
