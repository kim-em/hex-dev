/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.ScalarQuote
public import HexRCF.RootQuoteCases
public meta import HexRCF.RealCoefficients.ScalarQuote
public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.PolynomialQuotePublic
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

@[expose] def context := Algebraic.Context.adjoin RootQuoteTests.nativeRoot RootQuoteTests.base.isClean
@[expose] def reader := Codec.readPoly
  (Algebraic.Element.codec (context := context) RootQuoteTests.base.codec) (.array .nil)
@[expose] def facts : List (Algebraic.SignFact context) := []

run_meta do
  withExporting (isExporting := false) do
    let some original ← unfoldDefinition? (mkConst ``reader)
      | throwError "public polynomial reader unavailable"
    let .ok result ← RootQuote.runWith
        (ScalarQuote.quotePolyWith original (mkConst ``facts))
      | throwError "public polynomial quotation failed"
    let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``reader])
      (← mkAppM ``Option.some #[result.value])
    let proof ← Hex.RCF.checkProof `publicPolynomial statement result.proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.PolynomialQuotePublic.reader_checked,levelParams := [],
        type := statement,value := proof})

/-- The actual emitted polynomial proof is usable by an ordinary module consumer. -/
theorem accepted : reader.toOption.isSome = true := by
  rw [reader_checked]
  rfl
end Hex.RCF.PolynomialQuotePublic
