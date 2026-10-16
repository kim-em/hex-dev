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
  let .thmInfo first ← getConstInfo ``canonical_read | throwError "missing read"
  let .thmInfo second ← getConstInfo ``canonical_source | throwError "missing source"
  unless first.type == second.type && second.value.consumeMData.isConstOf ``canonical_read do
    throwError "independent canonical source differs from its exact reader equation"
  let roots := #[``canonical_read,``canonical_source,``zero_read,``restored_polynomial,``restored_sign,
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
  for name in dependencies.toArray do
    if (← getEnv).getModuleIdxFor? name == some index then
      if let .thmInfo declaration ← getConstInfo name then
        if name == ``canonical_source then
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
  unless checked == 12 do throwError "scalar quotation body coverage changed: {checked}"
  let .thmInfo bridge ← getConstInfo ``ScalarQuote.accepted
    | throwError "canonical scalar transport theorem missing"
  let _ ← Hex.RCF.checkProof ``ScalarQuote.accepted bridge.type bridge.value
  logInfo m!"canonical scalar quotation: {checked} actual theorem bodies checked without producer reduction; exact polynomial/sign and complete standard-three axiom closure"

end Hex.RCF.ScalarQuoteTests
