/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellSourceQuote
import HexRCF.RealCoefficients.CellBuild
import HexRCF.ProofEvidence
import HexRCF.SelectedRoot.KernelCheck
import KernelReplay.AxiomClosure
meta section
open Lean Meta Hex.RealClosure Hex.RCF.RealCoefficients
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
run_meta do
  let roots := #[``Hex.RCF.CellSourceQuote.checked,``Hex.RCF.CellSourceQuote.source]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
    throwError "fresh complete source has inadmissible dependencies"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``SourceIdentity.identify,``SourceIdentity.observe,``SourceIdentity.select,
      ``ScalarPacket.restore,``Tower.Model.root_generator,
      ``RowQuote.read_eq,``Hex.SignDet.Dag.selectedSigns_memo,
      ``CompleteReplay.check_sound,``CellOperations.check_of_parts,
      ``CellOperations.readCells_of_parts,``CellRead.collectWith_eq,``CellOperations.check_eq,
      ``RootQuote.read_eq,``Hex.SignDet.Replay.check.eq_1,``Hex.MvPoly.termsList,
      ``RowQuote.values_cast,``RowQuote.values_restore,
      ``RowQuote.values_retarget,``RowQuote.value_eq] do
    unless dependencies.contains required do throwError "fresh complete source omitted {required}"
  for forbidden in #[``CellReplayTests.Algebraic.Schema.coefficient,
      ``Hex.RCF.SourceIdentityPacket.coefficient,``Hex.RCF.SourceIdentityPacket.selected,
      ``Hex.RCF.SelectedRootTests.Data.alpha_value,``Hex.RCF.SelectedRootTests.Data.selectedSqrt,
      ``Hex.RCF.SourceIdentityCases.source_selected,``Hex.RCF.SourceIdentityCases.coefficient,
      ``Hex.RCF.SourceIdentityCases.equationFact,``Hex.RCF.SourceIdentityCases.marginFact,
      ``CellReplayTests.Operations.accepted,``CellReplayTests.Operations.checked,
      ``CellReplayTests.Operations.source,``CellReplayTests.Algebraic.CompleteQuote.checked,
      ``CellReplayTests.Algebraic.CompleteQuote.source,``CellReplayTests.Algebraic.Read.accepted,
      ``CellReplayTests.Algebraic.Canonical.evidence,``CellReplayTests.Algebraic.Canonical.cert,
      ``CellBuild.build,``ScalarPacket.build,``ScalarPacket.buildLiteral] do
    if dependencies.contains forbidden then throwError "fresh complete source reused {forbidden}"
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let allowed := #[`HexRCF.SourceIdentityPacket,`HexRCF.SourceIdentityLiterals,
    `HexRCF.RealCoefficients.SourceIdentity,`HexRCF.RealCoefficients.ScalarPacket,
    `HexRCF.RealCoefficients.RowPacketQuote,`HexRCF.CellSourceQuote,`HexRCF.RealCoefficients.RootQuote,
    `HexRCF.RealCoefficients.ScalarQuote,`HexRCF.RealCoefficients.CellQuote,
    `HexRCF.RealCoefficients.RowQuote,`HexRCF.RealCoefficients.CellRead,
    `HexRCF.RealCoefficients.CellOperations]
  let mut theorems : Nat := 0
  let mut definitions : Nat := 0
  let mut traces : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless allowed.contains modules[index]! do continue
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
        theorems := theorems+1
        pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__completeBody})
      | .defnInfo info =>
        definitions := definitions+1
        pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__completeData})
      | _ => continue
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics checked
    unless diagnostics.enabled do throwError "complete source diagnostics disabled"
    if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
        #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
          ``Hex.SignDet.Descriptor.ofReplay?] then
      throwError "complete source reduced producer {producer}: {count}; body={name}"
    if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
  unless theorems == 1191 && definitions == 202 && traces == 1351 do
    throwError "complete source inventory changed: {theorems}/{definitions}/{traces}"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "complete source audit retained copied declarations"
  logInfo m!"complete original source actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
