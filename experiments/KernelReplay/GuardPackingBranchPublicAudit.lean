/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardPackingBranchPublic
import KernelReplay.GuardPackingRootPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranchPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardPackingBranch.data, mkConst ``GuardPackingBranch.moments,
    mkConst ``GuardPackingLeaf.data, mkConst ``GuardPackingBranchPublic.branch,
    mkConst ``GuardPackingBranchPublic.leaf, mkConst ``GuardPackingShape.node1.count_eq,
    mkConst ``GuardPackingShape.node2.count_eq, mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"original first packing branch and leaf public consumer audit: originalNodeIndices=[1,2] fieldsPerNode=5 branchOriginalMomentBound=3 allOriginalMomentsAndGuardsRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingBranchPublicAudit
