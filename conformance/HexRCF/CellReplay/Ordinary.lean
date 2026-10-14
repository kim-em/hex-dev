/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Check
import HexRCF.CellReplay.Refusals
import HexRCF.RootReplayOrdinaryConformance
import HexRCF.ProofEvidence
import HexRCF.Tactic
import HexRCF.RealCoefficients.SectionBuild
import HexRCF.RealCoefficients.PointBuild
open Lean Meta
run_meta do
  let .thmInfo source ← getConstInfo ``Hex.RCF.RealCoefficients.CellReplayTests.Check.source | throwError "expected actual cell source"
  let _ ← Hex.RCF.checkProof ``Hex.RCF.RealCoefficients.CellReplayTests.Check.source source.type source.value
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``Hex.RCF.RealCoefficients.CellReplayTests.Check.source]
  for required in #[``Hex.RCF.RealCoefficients.CellReplay.check_sound,
      ``Hex.RCF.RealCoefficients.RepresentationCells.atom_coverage,
      ``Hex.RCF.RealCoefficients.RootReplay.Result.coverage,
      ``Hex.SignDet.Descriptor.rootsFrom_coverage,
      ``Hex.RCF.RealCoefficients.RadicalCert.roots,
      ``Hex.RCF.RealCoefficients.SectorSamples.Sector.inside,
      ``Hex.RCF.RealCoefficients.PointRows.Packet.value,
      ``Hex.RCF.RealCoefficients.PointRows.Packet.row,
      ``Hex.SignDet.SelectedSigns.values_at_root,
      ``Hex.RCF.CellFold.Region.exists_spec] do
    unless seen.contains required do throwError "cell source omitted actual evidence: {required}"
  for forbidden in #[``Hex.RCF.RealCoefficients.Samples.run, ``Hex.RealClosure.Tower.Sample.family,
      ``Hex.RCF.RealCoefficients.SectionBuild.build, ``Hex.RCF.RealCoefficients.PointBuild.build,
      ``Hex.SignDet.Descriptor.build, ``Hex.SignDet.Descriptor.buildSigns,
      ``Hex.SignDet.Descriptor.buildRoots, ``Hex.SignDet.buildPrepared,
      ``Hex.SignDet.buildTree, ``Hex.SignDet.buildTreeFrom, ``Hex.SignDet.buildNode,
      ``Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance.source,
      ``Hex.RCF.RealCoefficients.RootReplayOrdinaryConformance.negative] do
    if seen.contains forbidden then throwError "cell source retained forbidden production or an old witness: {forbidden}"
  let environment ← getEnv
  let modules := environment.header.moduleNames
  let checked := #[`HexRCF.RealCoefficients.RepresentationCarrier, `HexRCF.RealCoefficients.RootCells, `HexRCF.RealCoefficients.RepresentationCells, `HexRCF.RealCoefficients.BoundarySigns,
    `HexRCF.RealCoefficients.SectorSamples, `HexRCF.RealCoefficients.PointRows, `HexRCF.RealCoefficients.CellReplay, `HexRCF.RealCoefficients.RowReplay, `HexRCF.RealCoefficients.SectorReplay, `HexRCF.RealCoefficients.CellRead,
    `HexRCF.CellReplay.Check, `HexRCF.CellReplay.Schema, `HexRCF.CellReplay.Refusals]
  for (name, declaration) in environment.constants do
    if let some index := environment.getModuleIdxFor? name then
      if checked.contains modules[index]! && declaration.isTheorem then
        let axioms ← collectAxioms name
        unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
          throwError "unexpected cell theorem axiom: {name}"
  let axioms ← collectAxioms ``Hex.RCF.RealCoefficients.CellReplayTests.Check.source
  unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
    throwError "unexpected complete cell-source axiom inventory"
