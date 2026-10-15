/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellExecution
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.CellExecutionProofs
open Lean Meta
run_meta do
  let environment ← getEnv
  for (declaration, expected) in #[
      (``CellBuild.evidence, `HexRCF.RealCoefficients.CellBuild),
      (``RootBuild.build, `HexRCF.RealCoefficients.RootBuild),
      (``RootBuild.prepare, `HexRCF.RealCoefficients.RootBuild),
      (``CellDiscover.run, `HexRCF.RealCoefficients.CellDiscover)] do
    let some index := environment.getModuleIdxFor? declaration |
      throwError "native producer has no owning module: {declaration}"
    unless environment.header.moduleNames[index]! == expected do
      throwError "quotation import boundary no longer matches producer owner: {declaration}"
  let names := #[``CellRead.collectWith_success, ``CellBuild.point_success, ``CellBuild.pointWith_success,
    ``BoundarySigns.left_sign, ``BoundarySigns.right_sign, ``CellBuild.bounds_success,
    ``CellBuild.evidence_success, ``CellBuild.build_success,
    ``CellAlignment.sector_vector, ``CellDiscover.run_success,
    ``CellBuild.packet_read, ``CellDiscover.run_replay, ``CellDiscover.run_complete]
  for name in names do
    let .thmInfo declaration ← getConstInfo name | throwError "expected theorem: {name}"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected executable cell proof axioms: {name}"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``CellDiscover.run_success]
  for required in #[``CellRead.collectWith_success, ``CellBuild.evidence_success,
      ``CellAlignment.sector_vector, ``SectorRequest.points_spec,
      ``CellBuild.prepare_success, ``CellDecision.check_spec,
      ``RadicalCert.buildMonic_success_real, ``Hex.SignDet.Descriptor.buildRoots_success,
      ``Hex.SignDet.Descriptor.buildSigns_success, ``Hex.SignDet.Descriptor.build_success_iff,
      ``BoundarySigns.difference, ``CellBuild.pointWith_success,
      ``BoundarySigns.left_sign, ``BoundarySigns.right_sign,
      ``Hex.RealClosure.Tower.Sample.Partition.model] do
    unless seen.contains required do throwError "executable acceptance omitted actual law: {required}"
  for forbidden in #[``CellProgress.evidence, ``CellProgress.sector, ``CellAlignment.sector_points,
      ``CellProgress.point_packet, ``CellDecision.complete] do
    if seen.contains forbidden then throwError "executable proof retained the chosen-point existence route: {forbidden}"
  let replay ← Hex.RCF.ProofEvidence.projectDependencies #[``CellDiscover.run_replay]
  for required in #[``CellDiscover.run_success, ``CellBuild.packet_read,
      ``CellFootprint.read_packet, ``RootCodec.read_covered,
      ``Hex.SignDet.Codec.bindings_of_check, ``Hex.RealClosure.Tower.Context.codec_lawful] do
    unless replay.contains required do throwError "native payload progress omitted actual reader law: {required}"
  let full ← Hex.RCF.ProofEvidence.projectDependencies #[``CellDiscover.run_complete]
  for required in #[``CompleteReplay.check_covered, ``RootTableCodec.read_roots,
      ``CellDiscover.run_success, ``Hex.RealClosure.Tower.Context.codec_lawful] do
    unless full.contains required do throwError "complete native packet progress omitted actual law: {required}"
  logInfo "thirteen actual public executable proof bodies kernel checked; complete root-and-cell literal acceptance retained"
end Hex.RCF.RealCoefficients.CellExecutionProofs
