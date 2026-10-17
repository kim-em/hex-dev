/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.PublicSignPacketValues
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck
/-! Recheck actual imported bodies, their complete axiom closure and the
unchanged native-producer exclusion guard. -/

meta section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  withoutExporting do
    let roots := #[``Hex.RCF.PublicSignPacket.read_checked,
      ``Hex.RCF.PublicSignPacket.accepted,``Hex.RCF.PublicSignPacket.sign,
      ``Hex.RCF.PublicSignPacket.coefficient_read,``Hex.RCF.PublicSignPacket.coefficient_value,
      ``Hex.RCF.PublicSignPacket.coefficient_sign,``Hex.RCF.PublicSignPacket.coefficient_positive]
    let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
    unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
      throwError "public packet axiom closure changed: {axioms}"
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
    let decoded ← Hex.RCF.ProofEvidence.projectDependencies
      #[``Hex.RCF.PublicSignPacket.coefficient_read]
    for required in #[``Hex.RCF.PublicSignPacket.fact,
        ``ScalarQuote.accepted] do
      unless decoded.contains required do throwError "public decoded coefficient omitted {required}"
    for name in dependencies.toArray do
      if (`Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Records).isPrefixOf name then
        throwError "public packet depends on the legacy fixture facts: {name}"
    for required in #[``Algebraic.Context.signPoly_checked,``ScalarPacket.fields,
        ``Tower.Signature.codec_lawful,``Hex.RCF.RootQuoteTests.root_raw,
        ``ScalarQuote.accepted,``Algebraic.Element.signCodec_sound,``Algebraic.Element.sign_spec] do
      unless dependencies.contains required do throwError "public packet omitted {required}"
    let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let modules := (← getEnv).header.moduleNames
    let allowed := #[`HexRCF.PublicSignPacket,`HexRCF.PublicSignPacketValues,`HexRCF.RealCoefficients.RootQuote,
      `HexRCF.RootQuoteCases,`HexRCF.RootQuoteSource,`HexRCF.RootQuoteData,
      `HexRCF.RealCoefficients.ScalarPacket]
    let mut theorems : Nat := 0
    let mut definitions : Nat := 0
    let mut traces : Nat := 0
    let mut inventory : Array (Name × Bool) := #[]
    for name in dependencies.toArray do
      let some index := (← getEnv).getModuleIdxFor? name | continue
      unless allowed.contains modules[index]! do continue
      let declaration ← match ← getConstInfo name with
        | .thmInfo info =>
          theorems := theorems+1
          inventory := inventory.push (name,true)
          pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__publicPacketBody})
        | .defnInfo info =>
          definitions := definitions+1
          inventory := inventory.push (name,false)
          pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__publicPacketData})
        | _ => continue
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
      let checked ← ofExceptKernelException <| environment.addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      let diagnostics := Kernel.getDiagnostics checked
      unless diagnostics.enabled do throwError "public packet body diagnostics are disabled"
      if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
          #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
            ``Descriptor.ofReplay?] then
        throwError "public packet reduced producer {producer}: {count}; body={name}"
      if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
    unless theorems == 646 && definitions == 67 && traces == 703 do
      throwError "public packet body inventory changed: {theorems}/{definitions}/{traces}"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
      throwError "public packet audit retained declarations"
    logInfo m!"public packet actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
    logInfo m!"public packet body inventory (theorem=true): {inventory.qsort (fun a b => Name.lt a.1 b.1)}"
