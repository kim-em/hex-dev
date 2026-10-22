/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRecordPublic
public import KernelReplay.GuardPackingRightPublicAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRecordPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardPackingRecord.nativeReplay, mkConst ``GuardPackingRecord.replay,
    mkConst ``GuardPackingRecord.difference, mkConst ``GuardPackingRecord.data,
    mkConst ``GuardPackingRecordPublic.first_entry, mkConst ``GuardPackingRecordPublic.data,
    mkConst ``GuardPackingRecordPublic.value, mkConst ``GuardDescriptorPoint.spec,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"complete original first packing public consumer audit: originalSecondInventoryIndex=0 originalInventoryPositionChecked=true fullOriginalReplayNodes=5 everyOriginalSplitChildAndMomentRetained=true originalReplayAndDifferenceChecked=true valueAndSignAtSameSecondPointChecked=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRecordPublicAudit
