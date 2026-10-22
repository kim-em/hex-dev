/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.DependentScalarQuote
public import HexRCF.RealCoefficients.ScalarPacket
public import HexRCF.ProofEvidence
public import KernelReplay.AxiomClosure
public import HexRCF.SelectedRoot.KernelCheck

public section
/-! Recheck actual imported bodies, their complete axiom closure and the
unchanged native-producer exclusion guard. -/

meta section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  withoutExporting do
    let roots := #[``Hex.RCF.DependentScalarQuote.read_checked,``Hex.RCF.DependentScalarQuote.nested_checked]
    let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
    unless axioms.all (fun name => #[``propext,``Classical.choice,``Quot.sound].contains name) do
      throwError "unexpected dependent scalar axioms: {axioms}"
    let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
    let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
    let modules := (← getEnv).header.moduleNames
    let allowed := #[`HexRCF.DependentScalarQuote,`HexRCF.RealCoefficients.RootQuote]
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
          pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__dependentScalarBody})
        | .defnInfo info =>
          definitions := definitions+1
          inventory := inventory.push (name,false)
          pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__dependentScalarData})
        | _ => continue
      let options := (← getOptions).setBool `debug.skipKernelTC false
      let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
      let checked ← ofExceptKernelException <| environment.addDeclCore
        (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
        declaration none (doCheck := true)
      let diagnostics := Kernel.getDiagnostics checked
      unless diagnostics.enabled do throwError "dependent scalar body diagnostics are disabled"
      if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
          #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
            ``Descriptor.ofReplay?] then
        throwError "dependent scalar reduced producer {producer}: {count}; body={name}"
      if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
    unless theorems == 61 && definitions == 4 && traces == 56 do
      throwError "dependent scalar body inventory changed: {theorems}/{definitions}/{traces}"
    unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
      throwError "dependent scalar audit retained declarations"
    logInfo m!"dependent scalar actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
    logInfo m!"dependent scalar body inventory (theorem=true): {inventory.qsort (fun a b => Name.lt a.1 b.1)}"
