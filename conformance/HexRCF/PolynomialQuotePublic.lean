/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.ScalarQuote
public import HexRCF.RootQuoteCases
public meta import HexRCF.RealCoefficients.ScalarQuote
public meta import HexRCF.RealCoefficients.RationalQuote
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
    let outcome ← RootQuote.runWith
        (ScalarQuote.quotePolyWith original (mkConst ``facts))
    let result ← match outcome with
      | .ok result => pure result
      | .error error => throwError "public polynomial quotation failed: {Hex.RealFormula.Reify.Error.toMessageData error}"
    let name := `Hex.RCF.PolynomialQuotePublic.empty
    withExporting (isExporting := true) do
      let declaration := Declaration.defnDecl {
        name,levelParams := [],type := ← inferType result.value,value := result.value,
        hints := .regular 0,safety := .safe}
      addDecl declaration (forceExpose := true)
      compileDecl declaration (logErrors := true)
    let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``reader])
      (← mkAppM ``Option.some #[mkConst name])
    let proof ← Hex.RCF.checkProof `publicPolynomial statement result.proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.PolynomialQuotePublic.reader_checked,levelParams := [],
        type := statement,value := proof})

/-- The actual emitted polynomial proof is usable by an ordinary module consumer. -/
theorem accepted : reader.toOption.isSome = true := by
  rw [reader_checked]
  rfl
@[expose] def coordinate : DensePoly RootQuoteTests.base.Value := DensePoly.C 1

theorem coordinate_sign : context.signPoly coordinate = 1 :=
  (Algebraic.Context.signPoly_const context coordinate (DensePoly.size_C_le_one _)).trans
    ((congrArg RootQuoteTests.base.sign (DensePoly.coeff_C (1 : RootQuoteTests.base.Value) 0)).trans
      (by decide +kernel))

@[expose] def nonzeroFacts : List (Algebraic.SignFact context) := [⟨coordinate,1,coordinate_sign⟩]
@[expose] def literal : Codec.Json := .array (.cons
  (.array (.cons (.array (.cons RootQuoteTests.j6 .nil)) (.cons (.number 1) .nil))) .nil)
@[expose] def nonzeroReader := Codec.readPoly
  (Algebraic.Element.codec (context := context) RootQuoteTests.base.codec) literal

run_meta do
  withExporting (isExporting := false) do
    let some original ← unfoldDefinition? (mkConst ``nonzeroReader)
      | throwError "public nonzero polynomial reader unavailable"
    let outcome ← RootQuote.runWith
        (ScalarQuote.quotePolyWith original (mkConst ``nonzeroFacts)
          (fun e => liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) e)))
    let result ← match outcome with
      | .ok result => pure result
      | .error error => throwError "public nonzero polynomial quotation failed: {Hex.RealFormula.Reify.Error.toMessageData error}"
    let name := `Hex.RCF.PolynomialQuotePublic.restored
    withExporting (isExporting := true) do
      let declaration := Declaration.defnDecl {
        name,levelParams := [],type := ← inferType result.value,value := result.value,
        hints := .regular 0,safety := .safe}
      addDecl declaration (forceExpose := true)
      compileDecl declaration (logErrors := true)
    let statement ← mkEq (← mkAppM ``Except.toOption #[mkConst ``nonzeroReader])
      (← mkAppM ``Option.some #[mkConst name])
    let proof ← Hex.RCF.checkProof `publicNonzeroPolynomial statement result.proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.PolynomialQuotePublic.nonzero_read_checked,levelParams := [],
        type := statement,value := proof})

/-- A stored nonzero coefficient exercises decoding and the ordinary emitted reader equation. -/
theorem nonzero_accepted : nonzeroReader.toOption.isSome = true := by
  rw [nonzero_read_checked]
  rfl

theorem coefficient_count : nonzeroReader.toOption.map DensePoly.size = some 1 := by
  rw [nonzero_read_checked]
  rfl

end Hex.RCF.PolynomialQuotePublic
