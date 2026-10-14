/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Guards
import HexRCF.CellReplay.Algebraic.Meaning
import HexRCF.CellReplay.Algebraic.Refusals
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
open Lean Meta
run_meta do
  for name in #[``Quote.source, ``Guards.source] do
    let .thmInfo source ← getConstInfo name | throwError "expected actual source quotation"
    let _ ← Hex.RCF.checkProof name source.type source.value
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected algebraic source quotation axioms"
    let seen ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    for required in #[``Hex.RCF.RealCoefficients.CellReplay.check_sound,
        ``Hex.RCF.RealCoefficients.RootReplay.Result.coverage,
        ``Hex.RCF.RealCoefficients.CellPacketRead.read,
        ``Hex.RCF.RealCoefficients.RootTable.read,
        ``Hex.RCF.RealCoefficients.ScalarPacket.restore,
        ``Records.facts, ``Read.accepted,
        ``Radical.accepted] do
      unless seen.contains required do throwError "fresh algebraic quotation omitted checked evidence: {required}"
    for forbidden in #[`AlgebraicSeedSupply.supply, `AlgebraicCellSeeds.packets,
        ``Check.source, `AlgebraicCellRootMeaning.roots,
        `Hex.RCF.RealCoefficients.NestedRootProduceConformance.checkedFacts,
        `Hex.RCF.RealCoefficients.NestedRootProduceConformance.source] do
      if seen.contains forbidden then throwError "fresh algebraic quotation retained production or earlier witness: {forbidden}"
    logInfo "fresh algebraic source body rechecked; frozen readers and standard three axioms verified"
  for name in #[``Meaning.roots_eq, ``Meaning.positive_mem, ``Meaning.negative_mem,
      ``Meaning.ordered, ``Refusals.accepted, ``Guards.zero_refused, ``Guards.zero_before_decode] do
    let axioms ← collectAxioms name
    unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unexpected algebraic root/domain proof axiom: {name}"

end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
