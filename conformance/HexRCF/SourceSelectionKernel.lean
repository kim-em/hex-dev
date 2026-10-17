/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SourceSelectionNative
import HexRCF.ProofEvidence
import HexRCF.SelectedRoot.KernelCheck
open Lean Meta Hex Hex.RealClosure Hex.RCF.RealCoefficients
namespace Hex.RCF.SourceSelectionKernel
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

/-! Inspect generated proof leaves as well as exported theorem bodies. This
inspection unit uses the existing non-module diagnostic helper; the source-root
construction and generic API remain public modules. Legacy native fixture
construction is outside the body scope and inside the complete axiom closure. -/
run_meta do
  let roots := #[``SourceSelectionCases.reader_eq,``SourceSelectionCases.binding_checked,
    ``SourceSelectionCases.parsed,``SourceSelectionCases.subject,``SourceSelectionCases.selected,
    ``SourceSelectionConformance.authenticated,``SourceSelectionConformance.inherited_free,
    ``SourceSelectionConformance.chain_source,``SourceSelectionConformance.swapped_roots,
    ``SourceSelectionNative.source_eq,``SourceSelectionNative.reader,
    ``SourceSelectionNative.witness,``SourceSelectionNative.counterexample]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  let modules := (← getEnv).header.moduleNames
  let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let mut bodies : Array Name := #[]
  let mut data : Array Name := #[]
  let mut traces : Nat := 0
  let mut failures : Array Name := #[]
  for name in roots do
    let axioms ← collectAxioms name
    unless axioms.all (fun a => [``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "source selection has unexpected complete axioms: {name}: {axioms}"
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless #[`HexRCF.SourceSelectionCases,`HexRCF.SourceSelectionConformance,
        `HexRCF.SourceSelectionNative,`HexRCF.RealCoefficients.SourceSelection,
        `HexRCF.RealCoefficients.FieldSelection].contains modules[index]! do continue
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
          bodies := bodies.push name
          pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__sourceBody})
      | .defnInfo info =>
          data := data.push name
          pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__sourceData})
      | _ => continue
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics checked
    unless diagnostics.enabled do throwError "source-selection diagnostics disabled"
    if let some (producer,count) := SelectedRootTests.KernelCheck.violation? diagnostics then
      logInfo m!"source-selection body {name} reduced native producer {producer}: {count}"
      failures := failures.push name
    if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
    throwError "source-selection inspection retained temporary declarations"
  unless bodies.contains ``SourceSelectionCases.reader_eq &&
      bodies.contains ``SourceSelectionCases.binding_checked &&
      bodies.contains ``SourceSelectionNative.witness &&
      bodies.contains ``SourceSelectionNative.counterexample do
    throwError "source-selection inspection omitted an actual generated or source proof"
  logInfo m!"source-selection inspection: {bodies.size} theorem bodies/{data.size} definitions; {traces} nonempty traces"
  logInfo m!"source-selection theorem inventory: {bodies.qsort Name.lt}"
  logInfo m!"source-selection definition inventory: {data.qsort Name.lt}"
  unless failures.isEmpty do
    throwError "source-selection native producer reductions in {failures}"
end Hex.RCF.SourceSelectionKernel
