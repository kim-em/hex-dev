/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.FrozenSignatureConformance
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck
meta section

/-! Fresh importing body and axiom audits for frozen signature quotation. -/
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  withoutExporting do
    let roots := #[``Hex.RCF.FrozenSignature.readFirst_checked,
      ``Hex.RCF.FrozenSignature.readSecond_checked,``Hex.RCF.FrozenSignature.readProjected_checked]
    let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
    unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "frozen signature axiom closure changed: {axioms}"
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
    unless dependencies.contains ``Tower.Signature.codec_literal do
      throwError "frozen signature quotation did not consume the public literal law"
    let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let modules := (← getEnv).header.moduleNames
    let allowed := #[`HexRCF.FrozenSignatureConformance,`HexRCF.RealCoefficients.RootQuote,
      `HexRCF.RealCoefficients.SignatureQuote]
    let mut theorems : Nat := 0
    let mut definitions : Nat := 0
    let mut traces : Nat := 0
    for name in dependencies.toArray do
      let some index := (← getEnv).getModuleIdxFor? name | continue
      unless allowed.contains modules[index]! do continue
      let declaration ← match ← getConstInfo name with
        | .thmInfo info =>
          theorems := theorems+1
          pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__signatureBody})
        | .defnInfo info =>
          definitions := definitions+1
          pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__signatureData})
        | _ => continue
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
      let checked ← ofExceptKernelException <| environment.addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      let diagnostics := Kernel.getDiagnostics checked
      unless diagnostics.enabled do throwError "frozen signature diagnostics are disabled"
      if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation?
          diagnostics #[``Tower.rootData,``Dag.encode] then
        throwError "frozen signature reduced producer/encoder {producer}: {count}; body={name}"
      if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
    unless theorems == 23 && definitions == 7 && traces == 16 do
      throwError "frozen signature body inventory changed: {theorems}/{definitions}/{traces}"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
      throwError "frozen signature audit retained declarations"
    logInfo m!"frozen signature actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
