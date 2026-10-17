/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SignPacketQuote
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.SignPacketProofs
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  let roots := #[``SignPacketQuote.root_read,``SignPacketQuote.read_checked,
    ``SignPacketQuote.lower_eq,``SignPacketQuote.context_eq,``SignPacketQuote.original_accepted,
    ``SignPacketQuote.coefficient_read,``SignPacketQuote.coefficient_value,
    ``SignPacketQuote.coefficient_polynomial,``SignPacketQuote.coefficient_sign,``SignPacketQuote.decoded_value,
    ``SignPacketQuote.original_read,``SignPacketQuote.standalone_read,``SignPacketQuote.sign,``SignPacketQuote.original_sign]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected sign packet complete axiom closure: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  let decoded ← Hex.RCF.ProofEvidence.projectDependencies #[``SignPacketQuote.decoded_value]
  for required in #[``SignPacketQuote.fact,``SignPacketQuote.coefficient_read,
      ``ScalarQuote.accepted] do
    unless decoded.contains required do
      throwError "decoded coefficient omitted its quoted fact or reader law: {required}"
  for required in #[``RootQuote.option_eq,``ScalarPacket.read_restore,
      ``ScalarPacket.fields,``Algebraic.Context.signPoly_checked,
      ``ScalarQuote.accepted,``Algebraic.Element.signCodec_sound] do
    unless dependencies.contains required do throwError "sign packet quotation omitted law: {required}"
  for name in dependencies.toArray do
    if (`Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Records).isPrefixOf name then
      throwError "sign packet proof depends on the legacy fixture fact list: {name}"
  let modules := (← getEnv).header.moduleNames
  let originalNames := (← (← getEnv).getLocalConstantInfos).map (·.name)
  let mut theorems : Array Name := #[]
  let mut definitions : Array Name := #[]
  let mut reductions : Nat := 0
  for name in dependencies.toArray do
    let some index := (← getEnv).getModuleIdxFor? name | continue
    unless #[`HexRCF.SignPacketQuote,`HexRCF.RealCoefficients.RootQuote,`HexRCF.RealCoefficients.ScalarPacket].contains modules[index]! do
      continue
    let declaration ← match ← getConstInfo name with
      | .thmInfo info =>
        theorems := theorems.push name
        pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__signPacketBody})
      | .defnInfo info =>
        definitions := definitions.push name
        pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__signPacketData})
      | _ => continue
    let options := (← getOptions).setBool `debug.skipKernelTC false
    let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
    let env ← ofExceptKernelException <| environment.addDeclCore
      (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
      declaration none (doCheck := true)
    let diagnostics := Kernel.getDiagnostics env
    unless diagnostics.enabled do throwError "sign packet diagnostics disabled"
    if let some (producer,count) := SelectedRootTests.KernelCheck.violation? diagnostics
        #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec,``Descriptor.ofReplay?] then
      throwError "sign packet quotation reduced native producer {producer}: {count}; body={name}"
    if !diagnostics.unfoldCounter.isEmpty then reductions := reductions+1
  unless (← (← getEnv).getLocalConstantInfos).map (·.name) == originalNames do
    throwError "sign packet audit retained temporary declarations"
  unless theorems.size == 96 && definitions.size == 11 && reductions == 97 do
    throwError "sign packet audit inventory changed: {theorems.size} theorem bodies/{definitions.size} definitions; traces={reductions}"
  logInfo m!"sign packet quotation: {theorems.size} theorem bodies, {definitions.size} definitions"
  logInfo m!"sign packet nonempty diagnostic traces: {reductions}"
  logInfo m!"sign packet theorem inventory: {theorems.qsort Name.lt}"
  logInfo m!"sign packet definition inventory: {definitions.qsort Name.lt}"
end Hex.RCF.SignPacketProofs
