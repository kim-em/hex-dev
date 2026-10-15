/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.CellAlignment
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.CellDiscoverProofs
open Lean Meta
run_meta do
  for name in #[``CellDiscover.Packet.model, ``CellDiscover.Packet.values,
      ``CellDiscover.Packet.sound, ``CellDiscover.Packet.domains,
      ``CellAlignment.points_length, ``CellAlignment.product_roots,
      ``CellAlignment.polynomial_eq, ``CellAlignment.source_roots,
      ``CellAlignment.aligned, ``CellAlignment.dimensions] do
    let .thmInfo declaration ← getConstInfo name | throwError "expected theorem: {name}"
    let _ ← Hex.RCF.checkProof name declaration.type declaration.value
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected discovery theorem axioms: {name}"
  for (name, required) in #[
      (``CellDiscover.Packet.sound, #[``CellReplay.check_sound, ``CellDiscover.Packet.model]),
      (``CellDiscover.Packet.domains, #[``CellReplay.check_domains, ``CellDiscover.Packet.model]),
      (``CellAlignment.aligned, #[``RootReplay.Result.coverage, ``RootReplay.Result.ordered,
        ``RadicalCert.roots, ``Hex.RealClosure.Tower.Sample.Partition.coverage,
        ``Hex.RealClosure.Tower.Sample.Partition.sorted])] do
    let seen ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    for target in required do
      unless seen.contains target do throwError "discovery law omitted actual owner evidence: {name}, {target}"
  logInfo "all ten actual discovery proof bodies rechecked, standard axioms and required source/coverage laws retained"
end Hex.RCF.RealCoefficients.CellDiscoverProofs
