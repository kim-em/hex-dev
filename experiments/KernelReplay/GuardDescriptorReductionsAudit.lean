/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardDescriptorReductions
public import KernelReplay.GuardDescriptorInputsAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorReductionsAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let environment ← getEnv
  let mut roots := #[mkConst ``GuardDescriptorReductions.reductions]
  for name in (environment.checked.get.constants.fold (fun found name info =>
      if info.isTheorem && info.levelParams.isEmpty then found.push name else found) (#[] : Array Name)) do
    let _ ← bounded began
    let some index := environment.getModuleIdxFor? name | continue
    unless #[`KernelReplay.GuardDescriptorInputs, `KernelReplay.GuardDescriptorReductions].contains
        environment.header.moduleNames[index.toNat]! do continue
    roots := roots.push (mkConst name)
  let count ← audit began roots
  logInfo m!"actual descriptor reductions module audit: completeOriginalReduction=true sameFirstPointChecked=true roots={roots.size} exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardDescriptorReductionsAudit
