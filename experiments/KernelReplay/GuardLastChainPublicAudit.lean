/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardLastChainPublic
public import KernelReplay.GuardMomentSecondPublicAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardLastChainPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardLastChainEnd.chain, mkConst ``GuardLastChainPublic.chain,
    mkConst ``GuardMomentSecond.momentCount_eq, mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"third moment squarefree chain public consumer audit: index=2 originalFields=10 actualFiniteBound=3 originalStatementRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardLastChainPublicAudit
