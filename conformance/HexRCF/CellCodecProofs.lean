/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CompleteReplay
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.CellCodecProofs
open Lean Meta
run_meta do
  for name in #[``SectorEncode.read_row, ``SectorEncode.read_of_descriptor,
      ``CellCodec.packet_eq, ``CellCodec.tuple_fin, ``CellCodec.collect_eq,
      ``CellCodec.read_of_descriptors, ``CellFootprint.sector_covered,
      ``CellFootprint.descriptor_covered, ``CellFootprint.covered, ``CellFootprint.read_covered,
      ``RootCodec.graph_covered, ``RootCodec.read_covered, ``CellFootprint.read_packet,
      ``RootCodec.replay_covered, ``RootTableCodec.read_covered, ``RootTableCodec.read_roots,
      ``CompleteReplay.read_covered, ``CompleteReplay.check_covered,
      ``CompleteReplay.check_parts, ``CompleteReplay.check_domains, ``CompleteReplay.check_sound] do
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
  let footprint ← Hex.RCF.ProofEvidence.projectDependencies #[``CellFootprint.read_covered]
  for required in #[``CellFootprint.covered, ``CellFootprint.sector_covered,
      ``CellCodec.read_of_descriptors, ``Hex.RealClosure.Tower.Signature.codec_lawful] do
    unless footprint.contains required do throwError "finite inventory composition omitted actual law: {required}"
  let restored ← Hex.RCF.ProofEvidence.projectDependencies #[``CellFootprint.read_packet]
  for required in #[``RootCodec.read_covered,
      ``Hex.RealClosure.Algebraic.RootReplay.readDescriptor_covered,
      ``Hex.SignDet.Codec.bindings_of_validate, ``Hex.SignDet.Dag.validate_encode,
      ``Hex.SignDet.Codec.bindings_of_check, ``Hex.SignDet.Codec.read_graph_covered,
      ``CellFootprint.descriptor_covered] do
    unless restored.contains required do throwError "payload restoration omitted actual owner law: {required}"
  let complete ← Hex.RCF.ProofEvidence.projectDependencies #[``CompleteReplay.read_covered,
    ``CompleteReplay.check_sound, ``CompleteReplay.check_domains]
  for required in #[``RootTableCodec.read_roots, ``RootCodec.replay_covered,
      ``CellFootprint.read_packet, ``CellReplay.check_sound, ``CellReplay.check_domains] do
    unless complete.contains required do throwError "complete root/cell replay omitted actual law: {required}"
  let environment ← getEnv
  for forbidden in #[`HexRCF.RealCoefficients.CellBuild, `HexRCF.RealCoefficients.RootBuild,
      `HexRCF.RealCoefficients.CellDiscover] do
    if environment.header.moduleNames.contains forbidden then
      throwError "cell serialization audit imported producer module: {forbidden}"
  logInfo "twenty-one actual complete serialization proof bodies kernel checked; root table, cells, domains and soundness retained"
end Hex.RCF.RealCoefficients.CellCodecProofs
