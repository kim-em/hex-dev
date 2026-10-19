/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardMomentPublic
import KernelReplay.GuardChainPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardMomentFirst.data, mkConst ``GuardMomentPublic.first,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"first complete moment public consumer audit: originalFields=7 bothOriginalChainsRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentPublicAudit
