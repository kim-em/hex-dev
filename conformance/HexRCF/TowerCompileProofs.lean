/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.TowerCompileConformance
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure

open Lean Meta Hex.RealClosure Hex.RCF.RealCoefficients
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

run_meta do
  let roots := (List.range 9).toArray.map
    (Name.num `Hex.RCF.TowerCompileConformance.quoted)
  let roots := roots ++ #[``TowerCompile.pow_value,``Hex.RCF.TowerCompileConformance.runFinished]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "tower coefficient quotation has an unexpected complete axiom closure"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``Tower.Model.nat,``Tower.Model.add,``Tower.Model.sub,
      ``Tower.Model.mul,``Tower.Model.neg,``Tower.Model.inv,``Tower.Model.div,
      ``TowerCompile.pow_value,``Hex.RCF.SelectedRootTests.Data.alpha_value] do
    unless dependencies.contains required do
      throwError "tower coefficient quotation omitted its actual interpretation law {required}"
  let before := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let allowed := #[`HexRCF.TowerCompileConformance,`HexRCF.RealCoefficients.TowerCompile]
  let mut bodies : Nat := 0
  let mut traces : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless allowed.contains modules[index]! do continue
    let .thmInfo info ← getConstInfo name | continue
    bodies := bodies + 1
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__towerBody}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics checked
    unless diagnostics.enabled do throwError "tower quotation kernel diagnostics disabled"
    if !diagnostics.unfoldCounter.isEmpty then traces := traces + 1
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == before do
    throwError "fresh tower quotation audit retained copied declarations"
  unless bodies == 36 && traces == 35 do
    throwError "fresh tower quotation inventory changed: {bodies}/{traces}"
  logInfo m!"fresh tower quotation: {bodies} actual theorem bodies; nonempty traces={traces}; full axioms={axioms}"
