/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FiniteFieldCells
import HexRCF.FiniteFieldSource
import HexRCF.FiniteFieldGuards
import HexRCF.ProofEvidence
import Lean
open Lean Meta
run_meta withoutExporting do
  let root := ``Hex.RCF.FiniteFieldCells.universal
  let axioms ← collectAxioms root
  unless axioms.toList.mergeSort Name.quickLt ==
      [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
    throwError "unexpected actual geometry axioms: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[root]
  for forbidden in #[``Hex.ZPoly.CheckedIrreducible,
      ``Hex.RCF.RealCoefficients.Field.value_eq_zero,
      ``Hex.RCF.RealCoefficients.Field.value_inv,
      ``Hex.RCF.RealCoefficients.Field.value_div,
      ``Hex.RCF.RealCoefficients.FieldBuild.isolateAt,
      ``Hex.RCF.RealCoefficients.FieldBuild.isolateAtWith,
      ``Hex.RCF.RealCoefficients.FieldBuild.buildTable,
      ``Hex.RCF.RealCoefficients.Field.prepareSign,
      ``Hex.Sturm.queryPrepared, ``Hex.QAdjoin.common] do
    if dependencies.contains forbidden then throwError "forbidden geometry proof dependency: {forbidden}"
  let .thmInfo outer ← getConstInfo root | throwError "expected exported theorem"
  let .some inner := outer.value.getAppFn.constName? | throwError "expected retained checked proof"
  let mut bodies : Nat := 0
  let mut traces : Nat := 0
  for name in #[root, inner] do
    let .thmInfo info ← getConstInfo name | throwError "expected actual theorem body"
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__geometryBody}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    bodies := bodies + 1
    unless (Kernel.getDiagnostics checked).unfoldCounter.isEmpty do traces := traces+1
  logInfo m!"FRESH_FINITE_FIELD_CELLS: bodies={bodies}; traces={traces}; dependencies={dependencies.size}; actual_axioms={axioms}"

run_meta withoutExporting do
  let root := ``Hex.RCF.FiniteFieldSource.original
  let axioms ← collectAxioms root
  unless axioms.toList.mergeSort Name.quickLt ==
      [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
    throwError "unexpected original-goal axioms: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies #[root]
  for forbidden in #[``Hex.RCF.RealCoefficients.Field.value_eq_zero,
      ``Hex.RCF.RealCoefficients.Field.value_inv, ``Hex.RCF.RealCoefficients.Field.value_div,
      ``Hex.RCF.RealCoefficients.FieldBuild.buildTable,
      ``Hex.RCF.RealCoefficients.Field.prepareSign,
      ``Hex.Sturm.queryPrepared, ``Hex.QAdjoin.common] do
    if dependencies.contains forbidden then throwError "unexpected original-goal dependency: {forbidden}"
  let .thmInfo outer ← getConstInfo root | throwError "expected actual source theorem"
  let some inner := outer.value.getAppFn.constName? | throwError "expected retained source proof"
  let mut bodies : Nat := 0
  for name in #[root,inner] do
    let .thmInfo info ← getConstInfo name | throwError "expected actual source proof body"
    let declaration := Declaration.thmDecl {info with name := ← mkFreshUserName `__sourceBody}
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    if (Kernel.getDiagnostics checked).unfoldCounter.isEmpty then
      throwError "source kernel recheck has no diagnostic trace"
    bodies := bodies+1
  logInfo m!"FRESH_FINITE_FIELD_SOURCE: bodies={bodies}; dependencies={dependencies.size}; actual_axioms={axioms}"

run_meta withoutExporting do
  let roots := #[``Hex.RCF.RealCoefficients.FieldCells.degrees,
    ``Hex.RCF.RealCoefficients.FieldCells.cells,
    ``Hex.RCF.RealCoefficients.FieldCells.specialize,
    ``Hex.RCF.RealCoefficients.FieldCells.forall_formula,
    ``Hex.RCF.RealCoefficients.FieldCells.exists_formula]
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for forbidden in #[``Hex.ZPoly.CheckedIrreducible,
      ``Hex.RCF.RealCoefficients.Field.value_eq_zero,
      ``Hex.RCF.RealCoefficients.Field.value_inv,
      ``Hex.RCF.RealCoefficients.Field.value_div] do
    if dependencies.contains forbidden then throwError "unexpected generic cell-law dependency: {forbidden}"
  for root in roots do
    let axioms ← collectAxioms root
    unless axioms.toList.mergeSort Name.quickLt ==
        [``propext, ``Classical.choice, ``Quot.sound].mergeSort Name.quickLt do
      throwError "unexpected cell-law axioms: {root}: {axioms}"
  logInfo m!"FINITE_FIELD_LAWS: roots={roots.size}; full_body_dependencies={dependencies.size}; standard_axioms_only"
