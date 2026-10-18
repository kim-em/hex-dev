/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import KernelReplay.GuardReplayBindings
import KernelReplay.GuardProductPublicAudit

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardReplayBindingsAudit
open Lean Meta Elab GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let count ← audit began #[mkConst ``GuardRecordExt.packing_eq,
    mkConst ``GuardRecordExt.valueSign_eq]
  logInfo m!"generic record structural equality module audit: exactStandardAxioms=true wholeFieldReferences=[] declarations={count} comparisonsOnly=true aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardReplayBindingsAudit
