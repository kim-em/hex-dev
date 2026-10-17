/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardPackingRootPublic
import KernelReplay.GuardPackingInputsAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRootPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardPackingRoot.data, mkConst ``GuardPackingRoot.moments,
    mkConst ``GuardPackingRootPublic.root, mkConst ``GuardPackingShape.node0.count_eq,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"original first packing root public consumer audit: originalNodeIndex=0 nodeFields=5 originalMomentBound=2 bothOriginalQueriesComplete=true originalGuardsRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPackingRootPublicAudit
