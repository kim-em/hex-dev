/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.BooleanSources
import HexRCF.CellReplay.Algebraic.BooleanBinding
import HexRCF.ProofEvidence
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanQuoted
open Lean Meta
run_meta do
  let modules := (← getEnv).header.moduleNames
  for forbidden in #[`HexRCF.RealCoefficients.CellBuild, `HexRCF.RealCoefficients.CellDiscover] do
    if modules.contains forbidden then
      throwError "literal quotation imports native cell production: {forbidden}"
  for name in #[``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanSources.lt_or_ge, ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanSources.eq_or_ne,
      ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanSources.positive, ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanSources.negative] do
    let .thmInfo source ← getConstInfo name | throwError "expected source theorem"
    let _ ← Hex.RCF.checkProof name source.type source.value
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "unexpected Boolean source axioms"
    let seen ← Hex.RCF.ProofEvidence.projectDependencies #[name]
    for required in #[``Hex.RCF.RealCoefficients.CellReplay.Evidence.changeFormula,``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean.transfer,
        ``Hex.RCF.RealCoefficients.CellReplay.check_sound,
        ``Hex.RCF.RealCoefficients.RootReplay.Result.coverage,
        ``Hex.RCF.RealCoefficients.CellPacketRead.read,
        ``Hex.RCF.RealCoefficients.ScalarPacket.restore] do
      unless seen.contains required do throwError "Boolean source missing checked dependency {required}"
    for forbidden in #[``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Check.source,
        ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Quote.source,
        ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Guards.source,
        ``Hex.RCF.RealCoefficients.ScalarPacket.build,
        ``Hex.RCF.RealCoefficients.ScalarPacket.buildLiteral] do
      if seen.contains forbidden then throwError "Boolean source reused old witness/supplier {forbidden}"
    logInfo m!"fresh Boolean source body rechecked with actual cells, standard axioms and no prior source witness: {name}"
  for name in #[``Hex.RCF.RealCoefficients.CellReplay.Evidence.changeFormula_row,
      ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanBinding.refused,
      ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean.incompatible,
      ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean.not_all_positive] do
    let axioms ← collectAxioms name
    unless axioms.all (fun a => #[``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "unexpected Boolean transfer/refusal axiom: {name}"

end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanQuoted
