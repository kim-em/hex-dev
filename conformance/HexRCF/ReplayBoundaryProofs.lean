/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.ReplayBoundary
import HexRCF.RealCoefficients.ScalarPacket
import HexRCF.ProofEvidence
import HexRCF.SelectedRoot.KernelCheck
import KernelReplay.AxiomClosure
meta section
open Lean Meta Hex.RealClosure Hex.RCF.RealCoefficients
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
run_meta do
  let roots := #[``Hex.RCF.ReplayBoundaryTests.inlineTrue,``Hex.RCF.ReplayBoundaryTests.inlineFalse,
    ``Hex.RCF.ReplayBoundaryTests.storedTrue,``Hex.RCF.ReplayBoundaryTests.storedFalse]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms.all (fun name => [``propext,``Classical.choice,``Quot.sound].contains name) do
    throwError "dependent replay boundary has inadmissible dependencies"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``Hex.SignDet.Replay.check.eq_1,``Hex.RCF.ReplayBoundaryTests.guard_true] do
    unless dependencies.contains required do throwError "public quotation omitted {required}"
  for forbidden in #[``Hex.SignDet.Conformance.literal_accepts,``Hex.SignDet.Conformance.full_kernel] do
    if dependencies.contains forbidden then throwError "public quotation reused fixture proof {forbidden}"
  let names := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let modules := (← getEnv).header.moduleNames
  let allowed := #[`HexRCF.ReplayBoundary,`HexRCF.RealCoefficients.RootQuote]
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
    unless diagnostics.enabled do throwError "dependent replay boundary diagnostics disabled"
    if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
        #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,
          ``Hex.SignDet.Descriptor.ofReplay?] then
      throwError "dependent replay boundary reduced producer {producer}: {count}; body={name}"
    if !diagnostics.unfoldCounter.isEmpty then traces := traces+1
  unless theorems == 132 && definitions == 3 && traces == 135 do
    throwError "dependent replay boundary inventory changed: {theorems}/{definitions}/{traces}"
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == names do
    throwError "dependent replay boundary audit retained copied declarations"
  logInfo m!"dependent replay boundary actual bodies: {theorems} theorems/{definitions} definitions; nonempty traces={traces}; full axioms={axioms}"
