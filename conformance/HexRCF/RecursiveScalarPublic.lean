/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.PolynomialQuotePublic
public meta import HexRCF.RealCoefficients.ScalarQuote
public meta import HexRCF.RealCoefficients.RationalQuote
public section
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
namespace Hex.RCF.RecursiveScalarPublic
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

def literal : Codec.Json := .array (.cons
  (.array (.cons RootQuoteTests.j6 .nil)) (.cons (.number 1) .nil))

def reader (codec : ValueCodec (Algebraic.Element PolynomialQuotePublic.context)) :=
  codec.decode literal

run_meta do
  withExporting (isExporting := false) do
    let some template ← unfoldDefinition? (mkConst ``PolynomialQuotePublic.nonzeroReader)
      | throwError "public canonical codec unavailable"
    let original := mkApp (mkConst ``reader) template.getAppArgs[3]!
    let lookup : Expr → Hex.RealFormula.Reify.ReifyM (Option Expr) := fun _ =>
      pure (some (mkConst ``PolynomialQuotePublic.nonzeroFacts))
    let base : RootQuote.DecoderM := fun expression =>
      liftM (RationalQuote.decoder (mkConst ``RootQuoteTests.registry) expression)
    let .ok quoted ← RootQuote.run original (ScalarQuote.decoderWith lookup base)
      | throwError "ordinary module recursive callback failed"
    withExporting (isExporting := true) do
      let declaration := Declaration.defnDecl {
        name := `Hex.RCF.RecursiveScalarPublic.restored,levelParams := [],
        type := ← inferType quoted.value,value := quoted.value,hints := .regular 0,safety := .safe}
      addDecl declaration (forceExpose := true)
      compileDecl declaration (logErrors := true)
    let statement ← mkEq (← mkAppM ``Except.toOption #[original])
      (← mkAppM ``Option.some #[mkConst `Hex.RCF.RecursiveScalarPublic.restored])
    let proof ← Hex.RCF.checkProof `publicRecursiveReader statement quoted.proof
    withExporting (isExporting := true) do
      addDecl (.thmDecl {
        name := `Hex.RCF.RecursiveScalarPublic.read_checked,levelParams := [],
        type := statement,value := proof})

theorem accepted :
    (reader (Algebraic.Element.codec (context := PolynomialQuotePublic.context)
      RootQuoteTests.base.codec)).toOption.isSome = true := by
  rw [read_checked]
  rfl

theorem sign : restored.sign = 1 := by
  unfold restored
  exact Algebraic.Element.restore_sign _ _ _ _

end Hex.RCF.RecursiveScalarPublic
