/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.SourceSelection
import all HexRCF.RealCoefficients.SourceSelection
public meta import HexRCF.ProofEvidence

/-! Recheck the actual theorem bodies in a fresh module. `import all` supplies
the private proof helpers for this inspection; consumers use the ordinary public
API. Concrete descriptor and native-point construction are outside this audit. -/
open Lean Meta Hex.RCF.RealCoefficients
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta withExporting (isExporting := false) do
  let roots := #[``SourceSelection.unique,``SourceSelection.exists_real]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for name in #[``NativeSelection.identity,``NativeSelection.relation_correct,
      ``NativeSources.true_real,``SourceSelection.unique] do
    unless dependencies.contains name do
      throwError "source selection omitted its checked selection or joint-reader law: {name}"
  let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
  for name in roots do
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "source selection has unexpected complete axioms: {name}: {axioms}"
    let .thmInfo info ← getConstInfo name | throwError "expected source-selection theorem: {name}"
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      (.thmDecl {info with name := ← mkFreshUserName `__sourceSelectionBody}) none (doCheck := true)
    unless (Kernel.getDiagnostics checked).enabled do
      throwError "source-selection body audit disabled diagnostics"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
    throwError "source-selection body audit retained temporary declarations"
  logInfo m!"source selection: {roots.size} exported theorem bodies checked in a fresh module"
