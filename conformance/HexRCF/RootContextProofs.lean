/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootContextConformance
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck
meta section

/-! Fresh importing body and axiom audits for native context assembly. -/
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  withoutExporting do
    let roots := #[``Hex.RCF.RootContextCases.context_checked,
      ``Hex.RCF.RootContextCases.signature_checked,``Hex.RCF.RootContextCases.value_checked,
      ``Hex.RCF.RootContextCases.positive_checked,``Hex.RCF.RootHeaderPacket.read_checked,
      ``Hex.RCF.RootHeaderPacket.sign,``Hex.RCF.RootHeaderPacket.coefficient_read,
      ``Hex.RCF.RootHeaderPacket.coefficient_value,``Hex.RCF.RootHeaderPacket.coefficient_positive]
    let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "root context axiom closure changed: {axioms}"
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
    for required in #[``Algebraic.Context.signPoly_checked,``ScalarPacket.fields,
        ``Tower.Signature.codec_lawful,``Tower.Signature.codec_literal,
        ``Hex.RealClosure.Algebraic.RootReplay.readDescriptor_subject,
        ``Hex.RCF.RootHeaderPacket.raw_binding] do
      unless dependencies.contains required do throwError "root context omitted {required}"
    for legacy in #[``Hex.RCF.RootQuoteTests.root_raw,``Hex.RCF.RootQuoteTests.subject_read,
        ``Hex.RCF.RootQuoteTests.nativeRoot_read] do
      if dependencies.contains legacy then throwError "generic header used fixture identity {legacy}"
    let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let modules := (← getEnv).header.moduleNames
    let allowed := #[`HexRCF.RootContextConformance,`HexRCF.RealCoefficients.RootContext,
      `HexRCF.RealCoefficients.RealModel,`HexRCF.RootHeaderPacket,`HexRCF.RootHeaderValues,`HexRCF.RealCoefficients.RootHeader,`HexRCF.RealCoefficients.RootQuote,
      `HexRCF.RootQuoteCases,`HexRCF.RootQuoteSource,`HexRCF.RootQuoteData,
      `HexRCF.RealCoefficients.ScalarPacket]
    let mut theorems : Nat := 0
    let mut definitions : Nat := 0
    let mut traces : Nat := 0
    for name in dependencies.toArray do
      let some index := (← getEnv).getModuleIdxFor? name | continue
      unless allowed.contains modules[index]! do continue
      let declaration ← match ← getConstInfo name with
        | .thmInfo info =>
          theorems := theorems+1
          pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__publicPacketBody})
        | .defnInfo info =>
          definitions := definitions+1
          pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__publicPacketData})
        | _ => continue
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
      let checked ← ofExceptKernelException <| environment.addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      let diagnostics := Kernel.getDiagnostics checked
      unless diagnostics.enabled do throwError "root context body diagnostics are disabled"
      let extra := #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
        ``Descriptor.ofReplay?] ++ if modules[index]! == `HexRCF.RootContextConformance then
          #[``Tower.rootData,``Dag.encode] else #[]
      if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics extra then
        throwError "root context reduced producer/encoder {producer}: {count}; body={name}"
      if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
    unless theorems == 682 && definitions == 68 && traces == 735 do
      throwError "root context body inventory changed: {theorems}/{definitions}/{traces}"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
      throwError "root context audit retained declarations"
    logInfo m!"root context actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
