/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellDecision
import HexRCF.RealCoefficients.CellReuse
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.CellDecisionProofs
open Lean Meta
run_meta do
  let names := #[``SectorRequest.value_eq, ``SectorRequest.point_inside,
    ``SectorRequest.point_exists, ``SectorRequest.point_witness,
    ``SectorRequest.Cut.adjacent, ``SectorRequest.Cut.witness, ``SectorRequest.points_spec,
    ``RootBuild.from_production, ``RootBuild.success, ``RootBuild.prepare_success,
    ``CellBuild.prepare_success, ``RowEncode.read_covered, ``CellReplay.Evidence.changeFormula_row,
    ``CellAlignment.boundary, ``CellAlignment.requested_inside, ``CellAlignment.sector_points,
    ``CellProgress.row_success, ``CellProgress.point_polynomial,
    ``CellProgress.point_descriptor, ``CellProgress.point_packet,
    ``CellProgress.left_bound, ``CellProgress.right_bound, ``CellProgress.sector, ``CellProgress.evidence,
    ``CellDecision.run_total, ``CellDecision.check_total, ``CellDecision.check_spec, ``CellDecision.complete]
  for name in names do
    let .thmInfo declaration ← getConstInfo name | throwError "expected theorem: {name}"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected cell decision axioms: {name}"
  for (name, required) in #[
      (``CellDecision.complete, #[``CellBuild.prepare_success, ``CellAlignment.aligned,
        ``CellAlignment.sector_points, ``CellProgress.evidence, ``CellDecision.check_spec,
        ``RadicalCert.buildMonic_success_real, ``Hex.SignDet.Descriptor.buildRoots_success,
        ``Hex.RealClosure.Tower.Sample.Partition.model]),
      (``RootBuild.from_production, #[``Hex.SignDet.Descriptor.buildRoots_spec]),
      (``RootBuild.success, #[``Hex.SignDet.Descriptor.buildRoots_success]),
      (``RootBuild.prepare_success, #[``RadicalCert.buildMonic_success_real]),
      (``CellBuild.prepare_success, #[``RootBuild.prepare_success]),
      (``RowEncode.read_covered, #[``Hex.RealClosure.Algebraic.SignEvidence.codec_ofSigns_covered]),
      (``CellProgress.point_descriptor, #[``Hex.SignDet.Descriptor.build_success_iff]),
      (``CellProgress.point_packet, #[``Hex.SignDet.Descriptor.buildSigns_success]),
      (``CellAlignment.sector_points, #[``SectorRequest.Cut.witness,
        ``Hex.RealClosure.Tower.Sample.Partition.sectorBetween?_success,
        ``Hex.RealClosure.Tower.Sample.Partition.sectorBetween?_correct])] do
    let seen ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    for target in required do
      unless seen.contains target do throwError "cell decision omitted actual construction law: {name}, {target}"
  logInfo "all 28 actual construction, reuse and cell-decision proof bodies rechecked, standard axioms and required owner construction laws retained"
end Hex.RCF.RealCoefficients.CellDecisionProofs
