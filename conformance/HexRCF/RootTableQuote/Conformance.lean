/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RootTableQuote.Semantics
public import HexRCF.ProofEvidence
public import KernelReplay.AxiomClosure
public import HexRCF.SelectedRoot.KernelCheck

public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RootTableQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  let roots := #[``literal_read,``input_read,``input_size,``reduction_eq,``table_read,``roots_count,``solutions,``witness,``checked_witness]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected complete root-table quotation axiom closure: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``RootTable.read,``RootTable.extract_eq,``Dag.replay_eq,
      ``RootReplay.Result.coverage,``RootReplay.Result.ordered,
      ``Codec.readPoly_refines,``Algebraic.Element.signCodec_sound,
      ``CellReplayTests.Algebraic.Records.accepted0] do
    unless dependencies.contains required do throwError "root-table quote omitted evidence: {required}"
  for forbidden in #[``CellReplayTests.Algebraic.Inputs.polynomialAt,
      ``ScalarPacket.build,``ScalarPacket.buildLiteral] do
    if dependencies.contains forbidden then throwError "root-table quote retained source computation: {forbidden}"
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let mut theorems : Array Name := #[]
  let mut definitions : Array Name := #[]
  let mut reductions : Nat := 0
  for name in dependencies.toArray do
    if let some index := (← getEnv).getModuleIdxFor? name then
      if #[`HexRCF.RootTableQuote.Cases,`HexRCF.RootTableQuote.Input,
          `HexRCF.RootTableQuote.Table,`HexRCF.RootTableQuote.Semantics].contains modules[index]! then
        let info ← getConstInfo name
        let declaration ← match info with
          | .thmInfo declaration =>
            theorems := theorems.push name
            pure (Declaration.thmDecl {declaration with name := ← mkFreshUserName `__rootTableBody})
          | .defnInfo declaration =>
            definitions := definitions.push name
            pure (Declaration.defnDecl {declaration with name := ← mkFreshUserName `__rootTableData})
          | _ => continue
        let options := (← getOptions).setBool `debug.skipKernelTC false
        let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
        let env ← ofExceptKernelException <| environment.addDeclCore
          (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
          declaration none (doCheck := true)
        let diagnostics := Kernel.getDiagnostics env
        unless diagnostics.enabled do throwError "root-table quotation diagnostics disabled"
        if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
            #[``ScalarPacket.build,``ScalarPacket.buildLiteral] then
          throwError "root-table quotation executed native producer {producer}: {count}; body={name}"
        if !diagnostics.unfoldCounter.isEmpty then reductions := reductions + 1
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "root-table audit retained copied declarations"
  unless reductions > 0 do throwError "root-table quotation audit did not observe any reductions"
  unless theorems.size == 86 && definitions.size == 14 do
    throwError "root-table quotation body coverage changed: {theorems.size}/{definitions.size}"
  logInfo m!"root-table quotation: {theorems.size} theorem bodies, {definitions.size} data definitions"
  logInfo "complete standard-three axiom closure; no native producer reductions"
  logInfo m!"root-table theorem inventory: {theorems.qsort Name.lt}"
  logInfo m!"root-table data inventory: {definitions.qsort Name.lt}"
end Hex.RCF.RootTableQuoteTests
