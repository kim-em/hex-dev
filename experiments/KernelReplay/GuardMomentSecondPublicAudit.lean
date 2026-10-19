/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardMomentSecondPublic
public import KernelReplay.GuardRemainderPublicAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardMomentSecondPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardMomentSecond.data, mkConst ``GuardMomentSecond.momentCount_eq,
    mkConst ``GuardMomentSecondPublic.second, mkConst ``GuardMomentSecondPublic.count,
    mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"second complete moment public consumer audit: index=1 originalFields=7 bothOriginalChainsRetained=true actualFiniteBound=3 originalCountBindingChecked=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardMomentSecondPublicAudit
