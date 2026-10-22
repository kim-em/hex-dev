/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import KernelReplay.GuardDescriptorSupplier
public import KernelReplay.GuardDescriptorReductionsAudit

public section

namespace Hex.RealClosure.Algebraic.KernelReplay.GuardPrimitiveAudit
open Lean Meta Elab FiniteData GuardDescriptorInputs

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
run_meta do
  let began ← IO.getNumHeartbeats
  let environment ← getEnv
  let mut roots := #[mkConst ``GuardCoefficientControl.first,
    mkConst ``GuardDescriptorReductions.reductions]
  let factNamespace := `Hex.RealClosure.Algebraic.KernelReplay.GuardPrimitiveFacts
  let mut facts : Nat := 0
  for name in (environment.checked.get.constants.fold (fun found name info =>
      if factNamespace.isPrefixOf name && info.isTheorem && info.levelParams.isEmpty then
        found.push name else found) (#[] : Array Name)) do
    let _ ← bounded began
    roots := roots.push (mkConst name)
    facts := facts+1
  unless facts == 75 do throwError "module export lost the original primitive facts"
  let count ← audit began roots
  logInfo m!"primitive arithmetic module audit: facts={facts} originalCoefficientIndexControl=true outOfRangeRejected=true exactStandardAxioms=true wholeFieldReferences=[] declarations={count} aggregateHeartbeat={((← IO.getNumHeartbeats)-began)/1000}"

end Hex.RealClosure.Algebraic.KernelReplay.GuardPrimitiveAudit
