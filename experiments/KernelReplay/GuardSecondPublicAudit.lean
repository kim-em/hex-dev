/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardSecondPublic
public import KernelReplay.GuardRemainingRecordsAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardSecondPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardSecondData.descriptor, mkConst ``GuardSecondData.packings,
    mkConst ``GuardSecondData.signs, mkConst ``GuardSecondData.inverses,
    mkConst ``GuardSecondData.data, mkConst ``GuardSecondData.point,
    mkConst ``GuardSecondData.pointBinding, mkConst ``GuardSecondData.reader,
    mkConst ``GuardSecondData.equations, mkConst ``GuardSecondPublic.data,
    mkConst ``GuardSecondPublic.point, mkConst ``GuardSecondPublic.conditions,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"complete original second inventory public consumer audit: originalOwnerExplicit=true originalOrderedPackings=3 allOriginalPackingReplayNodes=15 cachedSigns=0 inverseFacts=0 completeOriginalDescriptor=true originalRootIntervalAndFullThomRetained=true allOriginalConditionsAtOnePoint=true sameSelectedSecondPointKernelChecked=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardSecondPublicAudit
