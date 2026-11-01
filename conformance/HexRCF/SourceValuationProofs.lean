/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceValuationConformance
import HexRCF.ProofEvidence
import HexRCF.ProofPaths
import KernelReplay.AxiomClosure

open Lean Meta Hex.RealClosure
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

run_meta do
  let roots := ((List.range 3).toArray.map
    (Name.num `Hex.RCF.SourceValuationConformance.quoted)).push
      ``Hex.RCF.SourceValuationConformance.runFinished
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "source valuation has an unexpected complete axiom closure"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  Hex.RCF.ProofPaths.require `HexRCF.SourceValuationConformance
    (Name.num `Hex.RCF.SourceValuationConformance.quoted 2)
    #[``Tower.Model.add,``Tower.Model.nat,``Hex.RCF.SelectedRootTests.Data.alpha_value]
  for required in #[``Tower.Model.add,``Tower.Model.nat,
      ``Hex.RCF.SelectedRootTests.Data.alpha_value] do
    unless dependencies.contains required do
      throwError "source valuation omitted its actual interpretation law {required}"
  let before := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let mut bodies : Nat := 0
  let mut traces : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless modules[index]! == `HexRCF.SourceValuationConformance do continue
    let .thmInfo info ← getConstInfo name | continue
    bodies := bodies + 1
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__valuationBody}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics checked
    unless diagnostics.enabled do throwError "source valuation kernel diagnostics disabled"
    if !diagnostics.unfoldCounter.isEmpty then traces := traces + 1
  unless bodies == 13 && traces == 12 do
    throwError "source valuation inventory changed: {bodies}/{traces}"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == before do
    throwError "source valuation audit retained copied declarations"
  logInfo m!"fresh source valuations: {bodies} actual theorem bodies; nonempty traces={traces}; full axioms={axioms}"
