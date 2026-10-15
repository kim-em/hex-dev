/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellCodec
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.CellCodecProofs
open Lean Meta
run_meta do
  for name in #[``SectorEncode.read_row, ``SectorEncode.read_of_descriptor,
      ``CellCodec.packet_eq, ``CellCodec.tuple_fin, ``CellCodec.collect_eq,
      ``CellCodec.read_of_descriptors] do
    let .thmInfo declaration ← getConstInfo name | throwError "expected theorem: {name}"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let axioms ← collectAxioms name
    unless axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected cell serialization axioms: {name}"
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``CellCodec.read_of_descriptors]
  for required in #[``SectorEncode.read_of_descriptor, ``RowEncode.read_covered,
      ``Hex.RealClosure.Algebraic.SignEvidence.codec_ofSigns_covered, ``Hex.RealClosure.Algebraic.SignEvidence.check_ofSigns,
      ``CellRead.collectWith_success] do
    unless seen.contains required do throwError "cell serialization omitted actual reader law: {required}"
  let environment ← getEnv
  for forbidden in #[`HexRCF.RealCoefficients.CellBuild, `HexRCF.RealCoefficients.RootBuild,
      `HexRCF.RealCoefficients.CellDiscover] do
    if environment.header.moduleNames.contains forbidden then
      throwError "cell serialization audit imported producer module: {forbidden}"
  logInfo "six actual cell serialization proof bodies kernel checked; finite row laws retained and descriptor premise explicit"
end Hex.RCF.RealCoefficients.CellCodecProofs
