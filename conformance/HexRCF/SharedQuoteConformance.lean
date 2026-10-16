/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.SharedQuoteCases
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck

open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.SharedQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

run_meta do
  let roots := #[``read_checked,``coefficient_zero,``coefficient_one,``value_zero]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected complete shared quotation axiom closure: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``RootQuote.read_eq,``RootQuote.read_some,``Codec.readPoly_refines,
      ``Algebraic.Element.signCodec_sound,``Algebraic.SignFact.read_sound,
      ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Records.accepted0] do
    unless dependencies.contains required do throwError "shared quotation omitted evidence: {required}"
  let some index := (← getEnv).getModuleIdxFor? ``restored
    | throwError "shared quotation case module missing"
  let mut checked : Nat := 0
  let mut definitions : Nat := 0
  for name in dependencies.toArray do
    if (← getEnv).getModuleIdxFor? name == some index then
      if let .thmInfo declaration ← getConstInfo name then
        Hex.RCF.SelectedRootTests.KernelCheck.addChecked
          (← mkFreshUserName `__sharedQuoteBody) declaration.type declaration.value
          #[``ScalarPacket.build,``ScalarPacket.buildLiteral]
        checked := checked+1
      else if let .defnInfo declaration ← getConstInfo name then
        let options := (← getOptions).setBool `debug.skipKernelTC false
        let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
        let env ← ofExceptKernelException <| environment.addDeclCore
          (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
          (.defnDecl {declaration with name := ← mkFreshUserName `__sharedQuoteValue}) none (doCheck := true)
        let diagnostics := Kernel.getDiagnostics env
        unless diagnostics.enabled do throwError "shared value diagnostics disabled"
        if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
            #[``ScalarPacket.build,``ScalarPacket.buildLiteral] then
          throwError "shared value definition reduced native producer {producer}: {count}"
        setEnv (Kernel.enableDiag env false)
        definitions := definitions+1
  unless checked == 6 do throwError "shared quotation body coverage changed: {checked}"
  unless definitions == 3 do throwError "shared value definition coverage changed: {definitions}"
  logInfo m!"shared polynomial quotation: {checked} actual theorem bodies and {definitions} data definitions under kernel producer diagnostics; selected coefficient values and complete standard-three axiom closure"

end Hex.RCF.SharedQuoteTests
