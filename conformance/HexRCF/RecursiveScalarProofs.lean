/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RecursiveScalarQuote
import HexRCF.RecursiveScalarPublic
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RecursiveScalarProofs
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  let roots := #[``RecursiveScalarQuote.read_checked,``RecursiveScalarQuote.constant_read,
    ``RecursiveScalarQuote.sign,
    ``RecursiveScalarPublic.read_checked,``RecursiveScalarPublic.accepted,
    ``RecursiveScalarPublic.sign]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected recursive scalar complete axiom closure: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``ScalarQuote.accepted,``Algebraic.Element.signCodec_sound,
      ``RootQuote.read_eq] do
    unless dependencies.contains required do throwError "recursive quotation omitted law: {required}"
  let modules := (← getEnv).header.moduleNames
  let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let mut theorems : Array Name := #[]
  let mut definitions : Array Name := #[]
  let mut reductions : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless #[`HexRCF.RecursiveScalarQuote,`HexRCF.RecursiveScalarPublic].contains modules[index]! do
      continue
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
        theorems := theorems.push name
        pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__recursiveScalarBody})
      | .defnInfo info =>
        definitions := definitions.push name
        pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__recursiveScalarData})
      | _ => continue
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let env ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics env
    unless diagnostics.enabled do throwError "recursive scalar diagnostics disabled"
    if let some (producer,count) := SelectedRootTests.KernelCheck.violation? diagnostics
        #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec] then
      throwError "recursive scalar quotation reduced native producer {producer}: {count}; body={name}"
    if !diagnostics.unfoldCounter.isEmpty then reductions := reductions+1
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
    throwError "recursive scalar audit retained temporary declarations"
  unless theorems.size == 51 && definitions.size == 5 && reductions > 0 do
    throwError "recursive scalar audit inventory changed: {theorems.size} theorem bodies/{definitions.size} definitions; traces={reductions}"
  logInfo m!"recursive scalar quotation: {theorems.size} theorem bodies, {definitions.size} definitions"
  logInfo m!"recursive scalar nonempty diagnostic traces: {reductions}"
  logInfo m!"recursive scalar theorem inventory: {theorems.qsort Name.lt}"
  logInfo m!"recursive scalar definition inventory: {definitions.qsort Name.lt}"
end Hex.RCF.RecursiveScalarProofs
