/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.CompleteQuote
import HexRCF.ProofEvidence
import HexRCF.Tactic
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
open Lean Meta
run_meta do
  for forbidden in #[`HexRCF.RealCoefficients.CellBuild, `HexRCF.RealCoefficients.CellDiscover,
      `HexRCF.RealCoefficients.RootBuild] do
    if (← getEnv).header.moduleNames.contains forbidden then
      throwError "complete-packet quotation imports adapter production: {forbidden}"
  for name in #[``CompleteQuote.source, ``CompleteQuote.guarded_source] do
    let .thmInfo source ← getConstInfo name | throwError "expected actual complete source quotation"
    let _ ← Hex.RCF.checkProof name source.type source.value
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (#[``propext, ``Classical.choice, ``Quot.sound].contains ·) do
      throwError "unexpected complete source quotation axioms"
    let seen ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    for required in #[``CompleteReplay.check_sound, ``CompleteReplay.check_covered,
        ``RootTableCodec.read_roots, ``RootCodec.replay_covered, ``CellFootprint.read_packet,
        ``Hex.SignDet.Codec.bindings_of_check, ``Read.accepted, ``Check.exists_run] do
      unless seen.contains required do throwError "complete quotation omitted checked evidence: {required}"
    for forbidden in #[``Check.source, ``Quote.source, ``Guards.source,
        ``ScalarPacket.build, ``ScalarPacket.buildLiteral] do
      if seen.contains forbidden then throwError "complete quotation reused production or a source witness: {forbidden}"
    logInfo "fresh complete-packet source body rechecked; finite codec laws and standard three axioms verified"
  let .thmInfo domains ← getConstInfo ``CompleteQuote.domains | throwError "expected checked original domains"
  let _ ← Hex.RCF.checkProof ``CompleteQuote.domains domains.type domains.value
  let seen ← Hex.RCF.ProofEvidence.projectDependencies #[``CompleteQuote.domains]
  for required in #[``CompleteReplay.check_domains, ``CompleteQuote.guarded_checked] do
    unless seen.contains required do throwError "complete domain proof omitted actual guard law: {required}"
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
