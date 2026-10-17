/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardMomentAllPublic
import KernelReplay.GuardLastRemainderPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAllPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardMomentLast.data, mkConst ``GuardMomentAll.moments,
    mkConst ``GuardMomentAllPublic.third, mkConst ``GuardMomentAllPublic.moments,
    mkConst ``GuardMomentSecond.momentCount_eq, mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"complete original moment family public consumer audit: actualFiniteBound=3 allOriginalIndices=[0,1,2] fieldsPerQuery=7 bothOriginalChainsRetained=true originalFamilyTargetRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentAllPublicAudit
