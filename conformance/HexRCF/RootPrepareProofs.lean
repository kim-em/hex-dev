/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RootPreparePublic
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck
meta section
/-! Fresh importing kernel-body and complete dependency audits for retained contexts. -/
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
private def progress (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "HEX_RCF_ROOT_PREPARE_TRACE" then
    IO.FS.withFile path .append fun handle => do
      handle.putStrLn message
      handle.flush

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  withoutExporting do
    let roots := #[``Hex.RCF.RootPreparePacket.read_checked,
      ``Hex.RCF.RootPreparePublic.accepted,``Hex.RCF.RootPreparePublic.sign]
    progress "root preparation audit: collecting full axiom closure"
    let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "retained root/context axiom closure changed: {axioms}"
    progress "root preparation audit: enumerating project dependencies"
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
    for required in #[``Algebraic.RootReplay.readDescriptor_subject,``Tower.Signature.codec_literal,
        ``ScalarPacket.read_restore] do
      unless dependencies.contains required do throwError "retained root/context omitted {required}"
    for forbidden in #[``Hex.RCF.RootHeaderPacket.read_checked,``Hex.RCF.RootHeaderPacket.root,
        ``Hex.RCF.RootHeaderPacket.context,``Hex.RCF.RootHeaderPacket.raw_binding,``Hex.RCF.RootQuoteTests.root_raw,
        ``Hex.RCF.RootQuoteTests.subject_read,``Hex.RCF.RootQuoteTests.nativeRoot_read] do
      if dependencies.contains forbidden then throwError "retained quotation reused {forbidden}"
    progress s!"root preparation audit: dependencies={dependencies.toArray.size}; checking scoped bodies"
    let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let modules := (← getEnv).header.moduleNames
    let allowed := #[`HexRCF.RootPreparePacket,`HexRCF.RootPreparePublic,
      `HexRCF.RealCoefficients.RootPrepare,`HexRCF.RealCoefficients.RootQuote,
      `HexRCF.RealCoefficients.RootHeader,`HexRCF.RootHeaderPacket,
      `HexRCF.RootQuoteCases,`HexRCF.RootQuoteSource,`HexRCF.RootQuoteData,
      `HexRCF.RealCoefficients.ScalarPacket,`HexRCF.RealCoefficients.ScalarPacketQuote]
    let mut theorems : Nat := 0
    let mut definitions : Nat := 0
    let mut traces : Nat := 0
    for name in dependencies.toArray do
      let some index := (← getEnv).getModuleIdxFor? name | continue
      unless allowed.contains modules[index]! do continue
      let declaration ← match ← getConstInfo name with
        | .thmInfo info =>
          theorems := theorems+1
          pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__rootDecodeBody})
        | .defnInfo info =>
          definitions := definitions+1
          pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__rootDecodeData})
        | _ => continue
      progress s!"root preparation body: {name}"
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
      let checked ← ofExceptKernelException <| environment.addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      let diagnostics := Kernel.getDiagnostics checked
      unless diagnostics.enabled do throwError "generic root body diagnostics are disabled"
      let extra := #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
        ``Descriptor.ofReplay?] ++ if #[`HexRCF.RootPreparePacket,`HexRCF.RootPreparePublic].contains modules[index]! then
          #[``Tower.rootData,``Dag.encode] else #[]
      if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics extra then
        throwError "retained root/context reduced producer/encoder {producer}: {count}; body={name}"
      if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
    unless theorems == 827 && definitions == 63 && traces == 875 do
      throwError "retained root/context body inventory changed: {theorems}/{definitions}/{traces}"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
      throwError "retained root/context audit retained declarations"
    logInfo m!"retained root/context actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
