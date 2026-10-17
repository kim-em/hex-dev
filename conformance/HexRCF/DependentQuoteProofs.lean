/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.ProofFunctionPublic
import HexRCF.RealCoefficients.ScalarPacket
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
    let roots := #[``Hex.RCF.DependentQuote.reader_checked,``Hex.RCF.DependentQuote.nested_checked,
      ``Hex.RCF.DependentQuote.continued_checked,``Hex.RCF.DependentQuote.queried_checked,
      ``Hex.RCF.DependentQuote.boolReader_checked,``Hex.RCF.DependentQuote.multiple_checked,
      ``Hex.RCF.DependentQuote.independent_checked,
      ``Hex.RCF.DependentQuote.proofFunction_checked,
      ``Hex.RCF.DependentQuote.continuedFunction_checked,
      ``Hex.RCF.ProofFunctionPublic.first,``Hex.RCF.ProofFunctionPublic.continued]
    let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
    unless axioms.all (fun name => #[``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "unexpected dependent quotation axioms: {axioms}"
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
    let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let modules := (← getEnv).header.moduleNames
    let allowed := #[`HexRCF.DependentQuote,`HexRCF.DependentQuoteData,
      `HexRCF.ProofFunctionPublic,`HexRCF.RealCoefficients.RootQuote]
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
          pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__dependentQuoteBody})
        | .defnInfo info =>
          definitions := definitions+1
          inventory := inventory.push (name,false)
          pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__dependentQuoteData})
        | _ => continue
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
      let checked ← ofExceptKernelException <| environment.addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      let diagnostics := Kernel.getDiagnostics checked
      unless diagnostics.enabled do throwError "dependent quotation body diagnostics are disabled"
      if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
          #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
            ``Descriptor.ofReplay?] then
        throwError "dependent quotation reduced producer {producer}: {count}; body={name}"
      if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
    unless theorems == 145 && definitions == 16 && traces == 88 do
      throwError "dependent quotation body inventory changed: {theorems}/{definitions}/{traces}"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
      throwError "dependent quotation audit retained declarations"
    logInfo m!"dependent quotation actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
    logInfo m!"dependent quotation body inventory (theorem=true): {inventory.qsort (fun a b => Name.lt a.1 b.1)}"
