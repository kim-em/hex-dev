/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.TowerFinishConformance
import HexRCF.ProofEvidence
import HexRCF.ProofPaths
import KernelReplay.AxiomClosure

open Lean Meta Hex.RealClosure Hex.RCF.RealCoefficients
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

run_meta do
  let roots := #[``Hex.RCF.TowerFinishConformance.source,``Hex.RCF.TowerFinishConformance.domain]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "compound source finishing has an unexpected complete axiom closure"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  Hex.RCF.ProofPaths.require `HexRCF.TowerFinishConformance
    ``Hex.RCF.TowerFinishConformance.source
    #[``Tower.Model.sub,``Hex.RCF.SelectedRootTests.Data.alpha_value]
  Hex.RCF.ProofPaths.require `HexRCF.TowerFinishConformance
    ``Hex.RCF.TowerFinishConformance.domain #[``Tower.Model.neg]
  for required in #[``Tower.Model.add,``Tower.Model.sub,``Tower.Model.div,``Tower.Model.nat,
      ``CompleteReplay.check_sound,``CompleteReplay.check_domains] do
    unless dependencies.contains required do
      throwError "compound source finishing omitted its actual interpretation/checker law {required}"
  for forbidden in #[``CellReplayTests.Algebraic.CompleteQuote.source,
      ``CellReplayTests.Algebraic.CompleteQuote.guarded_source,
      ``FieldBuild.produce,``FieldBuild.produceWithin] do
    if dependencies.contains forbidden then
      throwError "compound source finishing reused an old source proof or producer {forbidden}"
  let before := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let mut bodies : Nat := 0
  let mut traces : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless modules[index]! == `HexRCF.TowerFinishConformance do continue
    let .thmInfo info ← getConstInfo name | continue
    bodies := bodies + 1
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__compoundBody}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics checked
    unless diagnostics.enabled do throwError "compound source kernel diagnostics disabled"
    if !diagnostics.unfoldCounter.isEmpty then traces := traces + 1
  unless bodies == 30 && traces == 30 do
    throwError "compound source inventory changed: {bodies}/{traces}"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == before do
    throwError "compound source audit retained copied declarations"
  logInfo m!"fresh compound source: {bodies} actual theorem bodies; nonempty traces={traces}; full axioms={axioms}"
