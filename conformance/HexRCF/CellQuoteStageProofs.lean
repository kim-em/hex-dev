/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellQuoteStages
import HexRCF.RealCoefficients.ScalarPacket
import HexRCF.ProofEvidence
import HexRCF.SelectedRoot.KernelCheck
import KernelReplay.AxiomClosure
meta section
open Lean Meta Hex.RealClosure Hex.RCF.RealCoefficients
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
run_meta do
  let roots := #[``Hex.RCF.CellQuoteStages.trueChecked,``Hex.RCF.CellQuoteStages.falseChecked,
    ``Hex.RCF.CellQuoteStages.source,
    ``Hex.RCF.CellQuoteStages.Quadratic.existsChecked]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
    throwError "staged cell quotation has inadmissible dependencies"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``CellOperations.check_of_parts,``CellOperations.readCells_of_parts,
      ``CellRead.collectWith_eq,``CellOperations.check_eq,
      ``CompleteReplay.check_sound,``RootQuote.read_eq,``RootQuote.read_some,
      ``Hex.SignDet.Replay.check.eq_1,``Hex.SignDet.Dag.replay_eq] do
    unless dependencies.contains required do throwError "staged quotation omitted {required}"
  for forbidden in #[`Hex.RCF.RealCoefficients.RootReplayConformance.constant_accepted,
      `Hex.RCF.RealCoefficients.RootReplayConformance.whole_accepted,
      `Hex.RCF.RealCoefficients.RootReplayConformance.positive_accepted,
      `Hex.RCF.RealCoefficients.CellReplayTests.Check.accepted,
      `Hex.RCF.RealCoefficients.CellReplayTests.Check.exists_checked,
      `Hex.RCF.RealCoefficients.CellReplayTests.Check.forall_false,
      `Hex.RCF.RealCoefficients.CellReplayTests.Zero.accepted,
      `Hex.RCF.RealCoefficients.CellReplayTests.Zero.all_checked,
      `Hex.SignDet.Conformance.literal_accepts,`Hex.SignDet.Conformance.full_kernel] do
    if dependencies.contains forbidden then throwError "staged quotation reused fixture proof {forbidden}"
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let allowed := #[`HexRCF.CellQuoteStages,`HexRCF.RealCoefficients.RootQuote,
    `HexRCF.RealCoefficients.CellOperations,`HexRCF.RealCoefficients.CellQuote,
    `HexRCF.RealCoefficients.CellRead,`HexRCF.RealCoefficients.RowQuote]
  let mut theorems : Nat := 0
  let mut definitions : Nat := 0
  let mut traces : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless allowed.contains modules[index]! do continue
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
        theorems := theorems+1
        pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__treeBody})
      | .defnInfo info =>
        definitions := definitions+1
        pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__treeData})
      | _ => continue
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics checked
    unless diagnostics.enabled do throwError "staged cell quotation diagnostics disabled"
    if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
        #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
          ``Hex.SignDet.Descriptor.ofReplay?] then
      throwError "staged cell quotation reduced producer {producer}: {count}; body={name}"
    if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
  unless theorems == 1409 && definitions == 78 && traces == 1439 do
    throwError "staged cell quotation inventory changed: {theorems}/{definitions}/{traces}"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "staged cell quotation audit retained copied declarations"
  logInfo m!"staged cell quotation actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
