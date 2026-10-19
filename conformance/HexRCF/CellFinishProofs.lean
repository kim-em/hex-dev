/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellFinishCases
import HexRCF.RealCoefficients.ScalarPacket
import HexRCF.ProofEvidence
import HexRCF.SelectedRoot.KernelCheck
import KernelReplay.AxiomClosure
meta section
open Lean Meta Hex.RealClosure Hex.RCF.RealCoefficients
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
run_meta do
  let roots := #[``Hex.RCF.CellFinishCases.source]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
    throwError "continued cell finishing has inadmissible dependencies"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``CompleteReplay.check_sound,``CellOperations.check_of_parts,
      ``CellOperations.check_eq,``RowQuote.read_eq,``Hex.SignDet.Dag.selectedSigns_memo] do
    unless dependencies.contains required do throwError "joint finishing omitted {required}"
  for forbidden in #[``Hex.RCF.CellQuoteStages.trueChecked,``Hex.RCF.CellQuoteStages.source,
      ``Hex.RCF.CellQuoteStages.falseChecked,
      `Hex.RCF.RealCoefficients.CellReplayTests.Zero.accepted,
      `Hex.RCF.RealCoefficients.CellReplayTests.Zero.all_checked,
      `Hex.RCF.RealCoefficients.RootReplayConformance.constant_accepted,
      `Hex.SignDet.Conformance.literal_accepts,`Hex.SignDet.Conformance.full_kernel] do
    if dependencies.contains forbidden then throwError "joint finishing reused fixture proof {forbidden}"
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let allowed := #[`HexRCF.CellFinishCases,`HexRCF.RealCoefficients.CellQuote,
    `HexRCF.RealCoefficients.RootQuote,`HexRCF.RealCoefficients.CellOperations,
    `HexRCF.RealCoefficients.CellRead,`HexRCF.RealCoefficients.RowQuote,
    `HexRCF.RealCoefficients.RowPacketQuote]
  let mut theorems : Nat := 0
  let mut definitions : Nat := 0
  let mut traces : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless allowed.contains modules[index]! do continue
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
        theorems := theorems+1
        pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__finishBody})
      | .defnInfo info =>
        definitions := definitions+1
        pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__finishData})
      | _ => continue
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let checked ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics checked
    unless diagnostics.enabled do throwError "joint finishing diagnostics disabled"
    if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
        #[``ScalarPacket.build,``ScalarPacket.buildLiteral,
          ``Hex.RealClosure.Algebraic.Element.codec,``Hex.SignDet.Descriptor.ofReplay?] then
      throwError "joint finishing reduced producer {producer}: {count}; body={name}"
    if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
  unless theorems == 163 && definitions == 43 && traces == 170 do
    throwError "joint finishing has no actual checked body evidence"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "joint finishing audit retained copied declarations"
  logInfo m!"joint source finishing actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
