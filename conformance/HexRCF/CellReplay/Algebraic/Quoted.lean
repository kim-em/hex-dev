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
  let modules := (← getEnv).header.moduleNames
  for forbidden in #[`HexRCF.RealCoefficients.CellBuild, `HexRCF.RealCoefficients.CellDiscover,
      `HexRCF.RealCoefficients.RootBuild] do
    if modules.contains forbidden then
      throwError "literal quotation imports native cell production: {forbidden}"
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
    -- SignFact types mention signPoly and therefore its native implementation.
    -- KernelCheck separately forbids executing those producers during replay.
    for forbidden in #[``Check.source, ``ScalarPacket.build, ``ScalarPacket.buildLiteral] do
      if seen.contains forbidden then throwError "fresh algebraic quotation retained production or earlier witness: {forbidden}"
    logInfo "fresh algebraic source body rechecked; frozen readers and standard three axioms verified"
  let environment ← getEnv
  let modules := environment.header.moduleNames
  let checked := #[`HexRCF.RealCoefficients.RowOperations,
    `HexRCF.RealCoefficients.CellPackets, `HexRCF.RealCoefficients.CellPacketRead,
    `HexRCF.RealCoefficients.CellPacketTransport, `HexRCF.RealCoefficients.CellPacketConvert,
    `HexRCF.CellReplay.Algebraic.Schema, `HexRCF.CellReplay.Algebraic.Records,
    `HexRCF.CellReplay.Algebraic.Inputs, `HexRCF.CellReplay.Algebraic.Sections,
    `HexRCF.CellReplay.Algebraic.Read, `HexRCF.CellReplay.Algebraic.Convert,
    `HexRCF.CellReplay.Algebraic.Canonical, `HexRCF.CellReplay.Algebraic.Radical,
    `HexRCF.CellReplay.Algebraic.Check, `HexRCF.CellReplay.Algebraic.Quote,
    `HexRCF.CellReplay.Algebraic.Guards, `HexRCF.CellReplay.Algebraic.Meaning,
    `HexRCF.CellReplay.Algebraic.Refusals]
  let mut swept : Array Name := #[]
  for (name, declaration) in environment.constants do
    if let some index := environment.getModuleIdxFor? name then
      if checked.contains modules[index]! && declaration.isTheorem then
        swept := swept.push name
        let axioms ← collectAxioms name
        unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
          throwError "unexpected algebraic cell theorem axiom: {name}"
  for required in #[``RowOperations.retarget_values, ``CellPackets.Sector.changeOps_values,
      ``Check.forall_run, ``Check.forall_false, ``Meaning.roots_eq,
      ``Refusals.accepted, ``Guards.zero_refused, ``Guards.zero_before_decode] do
    unless swept.contains required do throwError "algebraic cell axiom sweep missed {required}"

end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
