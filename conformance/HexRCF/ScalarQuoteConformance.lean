/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.ScalarQuoteCases
import HexRCF.ProofEvidence
import KernelReplay.AxiomClosure
import HexRCF.SelectedRoot.KernelCheck

open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.ScalarQuoteTests
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

run_meta do
  for (reader,source) in #[( ``canonical_read,``canonical_source),( ``zero_read,``zero_source)] do
    let .thmInfo first ← getConstInfo reader | throwError "missing read"
    let .thmInfo second ← getConstInfo source | throwError "missing source"
    unless first.type == second.type && second.value.consumeMData.isConstOf reader do
      logInfo m!"reader type: {first.type}"
      logInfo m!"source type: {second.type}"
      throwError "independent source {source} differs from its exact reader equation"
  let roots := #[``canonical_read,``canonical_source,``zero_read,``zero_source,``restored_polynomial,``restored_sign,
    ``restored_value]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected complete scalar quotation axiom closure: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``ScalarQuote.accepted,``Algebraic.Element.signCodec_sound,
      ``Algebraic.SignFact.read_sound,``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Records.accepted0] do
    unless dependencies.contains required do throwError "scalar quotation omitted owner evidence: {required}"
  let some index := (← getEnv).getModuleIdxFor? ``restored
    | throwError "scalar quotation case module missing"
  let mut checked : Nat := 0
  let mut definitions : Nat := 0
  let mut theoremNames : Array Name := #[]
  let mut definitionNames : Array Name := #[]
  for name in dependencies.toArray do
    if (← getEnv).getModuleIdxFor? name == some index then
      if let .thmInfo declaration ← getConstInfo name then
        if name == ``canonical_source || name == ``zero_source then
          -- This proof is exactly the already audited constant with the same
          -- type. Assert zero reductions; the common helper requires a
          -- nonempty trace for the nontrivial replay bodies instead.
          let options := (← getOptions).setBool `debug.skipKernelTC false
          let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
          let env ← ofExceptKernelException <| environment.addDeclCore
            (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
            (.thmDecl {
              name := ← mkFreshUserName `__scalarSource,
              levelParams := [],type := declaration.type,value := declaration.value}) none (doCheck := true)
          let diagnostics := Kernel.getDiagnostics env
          unless diagnostics.enabled && diagnostics.unfoldCounter.isEmpty do
            throwError "canonical source transport unexpectedly reduced a definition"
          setEnv (Kernel.enableDiag env false)
        else
          Hex.RCF.SelectedRootTests.KernelCheck.addChecked
            (← mkFreshUserName `__scalarQuoteBody) declaration.type declaration.value
            #[``ScalarPacket.build,``ScalarPacket.buildLiteral]
        checked := checked + 1
        theoremNames := theoremNames.push name
      else if let .defnInfo declaration ← getConstInfo name then
        let options := (← getOptions).setBool `debug.skipKernelTC false
        let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
        let env ← ofExceptKernelException <| environment.addDeclCore
          (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
          (.defnDecl {declaration with name := ← mkFreshUserName `__scalarValue}) none (doCheck := true)
        let diagnostics := Kernel.getDiagnostics env
        unless diagnostics.enabled do throwError "scalar value diagnostics disabled"
        if let some (producer,count) := Hex.RCF.SelectedRootTests.KernelCheck.violation? diagnostics
            #[``ScalarPacket.build,``ScalarPacket.buildLiteral] then
          throwError "scalar value definition reduced native producer {producer}: {count}"
        setEnv (Kernel.enableDiag env false)
        definitions := definitions+1
        definitionNames := definitionNames.push name
  unless checked == 13 do throwError "scalar quotation body coverage changed: {checked}"
  unless definitions == 3 do throwError "scalar value definition coverage changed: {definitions}"
  let .thmInfo bridge ← getConstInfo ``ScalarQuote.accepted
    | throwError "canonical scalar transport theorem missing"
  let _ ← Hex.RCF.checkProof ``ScalarQuote.accepted bridge.type bridge.value
  logInfo m!"canonical scalar quotation: {checked} actual theorem bodies and {definitions} data definitions checked without producer reduction; exact polynomial/sign and complete standard-three axiom closure"
  logInfo m!"scalar theorem inventory: {theoremNames.qsort Name.lt}"
  logInfo m!"scalar definition inventory: {definitionNames.qsort Name.lt}"

end Hex.RCF.ScalarQuoteTests
