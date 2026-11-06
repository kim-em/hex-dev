/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FrozenReplay
import HexRCF.FiniteEvidence
import HexRCF.RealCoefficients.FieldCellProgress
import HexRCF.RealCoefficients.CommonSource
import Lean

set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

open Lean Meta Hex Hex.RCF.RealCoefficients

run_meta withoutExporting do
  let laws := #[``Replay.checkCells_parts, ``Replay.checkCells_domains,
    ``Replay.checkCells_spec, ``Replay.checkCells_sound, ``Replay.checkCells_original]
  let cells := #[``FieldCells.check, ``FieldCells.signs_checked, ``FieldCells.specialize,
    ``FieldCells.forall_formula, ``FieldCells.exists_formula,
    ``QueryCells.check, ``QueryCells.rows_checked, ``QueryCells.degrees,
    ``QueryCells.cells, ``QueryCells.forall_formula, ``QueryCells.exists_formula]
  let sources := #[``Hex.RCF.FrozenReplay.original, ``Hex.RCF.FrozenReplay.total]
  let forbidden := #[``Field.value_eq_zero, ``Field.value_inv, ``Field.value_div,
    ``Field.value_quotient, ``FieldBuild.buildTable, ``Field.prepareSign,
    ``FieldRootSigns.Table.build, ``RadicalCert.build, ``RadicalCert.buildMonic,
    ``IsolationReplay.build,
    ``IsolationReplay.queryAt, ``Hex.TarskiCertificate.fromChains,
    ``Hex.SignedRemainderChain.build, ``FieldIsolate.propose?,
    ``Hex.Sturm.queryPrepared, ``Hex.QAdjoin.common,
    ``FieldCells.produce, ``Replay.buildCellsTotal]
  let generic ← Hex.RCF.ProofEvidence.projectDependencies (laws ++ cells)
  for name in forbidden.push ``Hex.ZPoly.CheckedIrreducible do
    if generic.contains name then throwError "finite replay law has a forbidden dependency: {name}"
  let actual ← Hex.RCF.ProofEvidence.projectDependencies sources
  for name in forbidden do
    if actual.contains name then throwError "frozen source proof has a forbidden dependency: {name}"
  let mut presentations := 0
  let mut bodies := laws ++ cells
  for source in sources do
    presentations := presentations + (← Hex.RCF.FiniteEvidence.checkClasses source
      #[Hex.RCF.CertificationInputs.polynomial, SquareTwo.polynomial] #[8])
    let .thmInfo exported ← getConstInfo source | throwError "expected frozen source theorem"
    let some retained := exported.value.getAppFn.constName? |
      throwError "expected retained ordinary-kernel proof"
    bodies := bodies ++ #[source,retained]
  let progress := #[``FieldTransport.leading_complete, ``FieldQuery.complete,
    ``FieldIsolation.complete, ``FieldRootSigns.Table.build_entries,
    ``FieldRootSigns.Table.build_complete, ``FieldCells.complete, ``FieldCells.produce,
    ``Replay.Input.cellValue_spec, ``FieldTransport.lookup_complete,
    ``Replay.buildCellsTotal, ``Replay.buildCellsTotal_checked, ``Replay.buildCellsTotal_spec,
    ``Field.common_real, ``Field.common_eval, ``FieldSpecialize.grouped_eq,
    ``FieldBuild.produceWithin, ``CommonPresentation.checkEquation_complete,
    ``CommonPresentation.checkPresentation_complete, ``CommonPresentation.build_complete]
  bodies := bodies ++ progress
  for name in bodies do
    let axioms ← collectAxioms name
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "unexpected frozen replay axioms: {name}: {axioms}"
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
        pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__frozenBody})
      | .defnInfo info =>
        pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__frozenProducer})
      | _ => throwError "expected actual theorem or definition body: {name}"
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let _ ← ofExceptKernelException <| (← getEnv).addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
  unless bodies.size == 39 do throwError "missing finite replay law, production law or source body"
  logInfo m!"FRESH_FROZEN_REPLAY: replay/cell laws and definitions=16; production laws/definitions=19; source bodies=4; presentations={presentations}; no common-field class or producer in source proofs; standard_axioms_only"
