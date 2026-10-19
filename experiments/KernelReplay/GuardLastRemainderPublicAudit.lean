/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardLastRemainderPublic
import KernelReplay.GuardLastChainPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderPublicAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let proofs := #[mkConst ``GuardLastRemainderEnd.chain, mkConst ``GuardRecurrenceEnd.data,
    mkConst ``GuardRecurrenceEnd.recurrences, mkConst ``GuardRecurrenceShape.count_eq,
    mkConst ``GuardLastRemainderPublic.chain, mkConst ``GuardLastRemainderPublic.recurrences,
    mkConst ``GuardLastRemainderPublic.count, mkConst ``GuardDescriptorInputs.firstPointBinding]
  let count ← audit began proofs
  logInfo m!"third moment remainder chain public consumer audit: index=2 originalChainFields=10 originalRecurrenceFields=5 originalFamilyCount=1 allOriginalIndicesAndGuards=true originalCountBindingChecked=true originalStatementsRetained=true ordinaryPublicImports=true sameFirstPointChecked=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardLastRemainderPublicAudit
