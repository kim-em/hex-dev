/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardPackingRightPublic
public import KernelReplay.GuardPackingBranchPublicAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardPackingRight.node3.data,
    mkConst ``GuardPackingRight.node4.data, mkConst ``GuardPackingRight.node3.moments,
    mkConst ``GuardPackingRight.node4.moments, mkConst ``GuardPackingRightPublic.third,
    mkConst ``GuardPackingRightPublic.fourth, mkConst ``GuardPackingShape.node3.count_eq,
    mkConst ``GuardPackingShape.node4.count_eq, mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"original first packing right nodes public consumer audit: originalNodeIndices=[3,4] fieldsPerNode=5 originalMomentBoundEach=3 allSixOriginalQueriesComplete=true allOriginalGuardsRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRightPublicAudit
