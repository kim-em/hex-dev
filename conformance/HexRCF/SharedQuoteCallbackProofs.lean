/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.SharedQuoteCallbacks
public import HexRCF.PolynomialQuotePublic
public import HexRCF.ScalarQuotePublic
public import HexRCF.ProofEvidence
public import KernelReplay.AxiomClosure
public import HexRCF.SelectedRoot.KernelCheck

public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.SharedQuoteCallbackProofs
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
run_meta do
  let roots := #[``SharedQuoteCallbacks.read_checked,``SharedQuoteCallbacks.coordinate_sign,
    ``SharedQuoteCallbacks.predecessor_read,``SharedQuoteCallbacks.bare_read,
    ``SharedQuoteCallbacks.constant_read,``SharedQuoteCallbacks.constant_bare_read,``SharedQuoteCallbacks.tagged_bare_read,
    ``PolynomialQuotePublic.accepted,
    ``PolynomialQuotePublic.nonzero_accepted,``PolynomialQuotePublic.coefficient_count,
    ``ScalarQuotePublic.polynomial_accepted]
  let axioms ← Algebraic.KernelReplay.AxiomClosure.collect roots
  unless axioms == (#[``propext,``Classical.choice,``Quot.sound].qsort Name.lt) do
    throwError "unexpected complete callback/public quotation axiom closure: {axioms}"
  let dependencies ← Hex.RCF.ProofEvidence.projectDependencies roots
  for required in #[``ScalarQuote.accepted,``Codec.readPoly_refines,
      ``Algebraic.Element.signCodec_sound,``Algebraic.Context.signPoly_const,
      ``ScalarQuote.polynomialAccepted,``ScalarQuote.normalizedBack,
      ``Algebraic.Element.restore_sign,``Algebraic.Element.sign_eq_zero,
      ``DensePoly.ofCoeffs_toArray] do
    unless dependencies.contains required do throwError "callback quotation omitted law: {required}"
  let modules := (← getEnv).header.moduleNames
  let mut theorems : Array Name := #[]
  let mut definitions : Array Name := #[]
  let mut reductions := 0
  for name in dependencies.toArray do
    if let some index := (← getEnv).getModuleIdxFor? name then
      if #[`HexRCF.SharedQuoteCallbacks,`HexRCF.PolynomialQuotePublic,`HexRCF.ScalarQuotePublic].contains modules[index]! then
        let declaration ← match ← getConstInfo name with
          | .thmInfo info =>
            theorems := theorems.push name
            pure (Declaration.thmDecl {info with name := ← mkFreshUserName `__callbackBody})
          | .defnInfo info =>
            definitions := definitions.push name
            pure (Declaration.defnDecl {info with name := ← mkFreshUserName `__callbackData})
          | _ => continue
        let options := (← getOptions).setBool `debug.skipKernelTC false
        let environment := Kernel.enableDiag (Kernel.resetDiag (← getEnv)) true
        let env ← ofExceptKernelException <| environment.addDeclCore
          (Core.getMaxHeartbeats options).toUSize (maxRecDepth.get options).toUSize
          declaration none (doCheck := true)
        let diagnostics := Kernel.getDiagnostics env
        unless diagnostics.enabled do throwError "callback quotation diagnostics disabled"
        if let some (producer,count) := SelectedRootTests.KernelCheck.violation? diagnostics
            #[``ScalarPacket.build,``ScalarPacket.buildLiteral,``Algebraic.Element.codec] then
          throwError "callback quotation reduced native producer {producer}: {count}; body={name}"
        if !diagnostics.unfoldCounter.isEmpty then reductions := reductions+1
        setEnv (Kernel.enableDiag env false)
  unless theorems.size == 65 && definitions.size == 14 && reductions > 0 do
    throwError "callback quotation audit omitted bodies or reduction diagnostics"
  logInfo m!"callback/public quotation: {theorems.size} theorem bodies, {definitions.size} definitions"
  logInfo m!"callback theorem inventory: {theorems.qsort Name.lt}"
  logInfo m!"callback definition inventory: {definitions.qsort Name.lt}"
end Hex.RCF.SharedQuoteCallbackProofs
