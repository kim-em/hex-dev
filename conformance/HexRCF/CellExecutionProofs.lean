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
  let names := #[``CellRead.collectWith_success, ``CellBuild.point_success,
    ``CellBuild.left_sign, ``CellBuild.right_sign, ``CellBuild.bounds_success,
    ``CellBuild.evidence_success, ``CellBuild.build_success,
    ``CellAlignment.sector_vector, ``CellDiscover.run_success]
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
      ``Hex.SignDet.Descriptor.buildSigns_success,
      ``Hex.RealClosure.Tower.Sample.Partition.model] do
    unless seen.contains required do throwError "executable acceptance omitted actual law: {required}"
  logInfo "nine actual public executable proof bodies kernel checked; standard axioms and actual owner construction laws retained"
end Hex.RCF.RealCoefficients.CellExecutionProofs
