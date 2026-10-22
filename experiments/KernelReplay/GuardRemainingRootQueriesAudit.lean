/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardRemainingRootQueriesPublic
public import KernelReplay.GuardRemainingFirstPublicAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRootQueriesAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardRemainingQuery.record1.node0.query0.data,
    mkConst ``GuardRemainingQuery.record1.node0.query1.data,
    mkConst ``GuardRemainingQuery.record1.node0.query1.squarefree,
    mkConst ``GuardRemainingQuery.record1.node0.query1.remainders,
    mkConst ``GuardRemainingRootQueriesPublic.first, mkConst ``GuardRemainingRootQueriesPublic.second,
    mkConst ``GuardRemainingShape.record1.node0.count_eq,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"original remaining root queries public consumer audit: originalRecordIndex=1 originalNodeIndex=0 originalQueryIndices=[0,1] queryFieldsEach=7 bothOriginalChainsEachComplete=true originalChainFieldsEach=10 originalSubjectsAndGuardsRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardRemainingRootQueriesAudit
