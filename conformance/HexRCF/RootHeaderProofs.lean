/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootHeaderValues
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck
meta section

/-! Fresh importing body audits for cubic packet quotation with original header bindings. -/
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  withoutExporting do
    let roots := #[``Hex.RCF.RootHeaderPacket.read_checked,
      ``Hex.RCF.RootHeaderPacket.accepted,``Hex.RCF.RootHeaderPacket.sign,
      ``Hex.RCF.RootHeaderPacket.coefficient_read,``Hex.RCF.RootHeaderPacket.coefficient_value,
      ``Hex.RCF.RootHeaderPacket.coefficient_positive]
    let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "root/header packet axiom closure changed: {axioms}"
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
    for required in #[``Algebraic.Context.signPoly_checked,``ScalarPacket.fields,
        ``Tower.Signature.codec_lawful,``Tower.Signature.codec_literal,
        ``Hex.RealClosure.Algebraic.RootReplay.readDescriptor_subject,
        ``Hex.RCF.RootHeaderPacket.raw_binding] do
      unless dependencies.contains required do throwError "root/header packet omitted {required}"
    for legacy in #[``Hex.RCF.RootQuoteTests.root_raw,``Hex.RCF.RootQuoteTests.subject_read,
        ``Hex.RCF.RootQuoteTests.nativeRoot_read] do
      if dependencies.contains legacy then throwError "generic header used fixture identity {legacy}"
    let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let modules := (← getEnv).header.moduleNames
    let allowed := #[`HexRCF.RootHeaderPacket,`HexRCF.RootHeaderValues,`HexRCF.RealCoefficients.RootHeader,`HexRCF.RealCoefficients.RootQuote,
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
      unless diagnostics.enabled do throwError "root/header packet body diagnostics are disabled"
      if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
          #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
            ``Descriptor.ofReplay?] then
        throwError "root/header packet reduced producer {producer}: {count}; body={name}"
      if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
    unless theorems == 724 && definitions == 66 && traces == 775 do
      throwError "root/header packet body inventory changed: {theorems}/{definitions}/{traces}"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
      throwError "root/header packet audit retained declarations"
    logInfo m!"root/header packet actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
