/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosure.SignCodec
public import HexRCF.RealCoefficients.RootQuote
public meta import HexRCF.RealCoefficients.RootQuote
public section

namespace Hex.RCF.RealCoefficients.ScalarQuote
open Hex Hex.RealClosure Hex.SignDet

/-- A checked supplied-sign decode authenticates the canonical literal result.
This composes the owner's decoder law; no sign search is part of the proof. -/
theorem accepted {E Ctx : Type} [Zero E] [DecidableEq E]
    [One E] [Add E] [Neg E] [Sub E] [Mul E] [Inv E] [Div E] [NatCast E]
    [DecidableEq Ctx] {sign : E → Int} {parent : Ctx}
    {context : Algebraic.Context E Ctx sign parent}
    (value : ValueCodec E) (facts : List (Algebraic.SignFact context))
    (literal : Codec.Json) (a : Algebraic.Element context)
    (checked : ((Algebraic.Element.signCodec value facts).decode literal).toOption = some a) :
    ((Algebraic.Element.codec value).decode literal).toOption = some a := by
  have strict : (Algebraic.Element.signCodec value facts).decode literal = .ok a := by
    cases equation : (Algebraic.Element.signCodec value facts).decode literal with
    | error message => simp only [equation, Except.toOption] at checked; contradiction
    | ok result =>
      exact congrArg Except.ok (by simpa only [equation, Except.toOption, Option.some.injEq] using checked)
  rw [Algebraic.Element.signCodec_sound value facts literal a strict]
  rfl

end Hex.RCF.RealCoefficients.ScalarQuote

public meta section
namespace Hex.RCF.RealCoefficients.ScalarQuote
open Lean Meta Hex Hex.RealClosure Hex.SignDet Hex.RealFormula.Reify

private def checkFacts (codec facts : Expr) (parameters : Nat) : ReifyM Unit := do
  -- Charge preflight checking separately from the subsequent reader/proof syntax.
  accountProof facts
  let factsType ← withTransparency .reducible <| whnf (← inferType facts)
  unless factsType.isAppOfArity ``List 1 do
    throwError "rcf: scalar quotation expects a list of sign facts"
  let factType ← withTransparency .reducible <| whnf factsType.appArg!
  unless factType.getAppFn.isConstOf ``Algebraic.SignFact && factType.getAppNumArgs > 0 do
    throwError "rcf: scalar quotation expects sign facts for its original context"
  let originalContext := codec.getAppArgs[parameters-2]!
  unless ← withNewMCtxDepth <| withTransparency .reducible <|
      isDefEq factType.getAppArgs.back! originalContext do
    throwError "rcf: scalar facts must use the codec's original context under reducible transparency"

private def finish (codec facts literal : Expr) (result : RootQuote.Result) : ReifyM RootQuote.Result := do
  Core.checkSystem "checked scalar quotation"
  let proof := mkAppN (mkConst ``accepted codec.getAppFn.constLevels!)
    (codec.getAppArgs ++ #[facts,literal,result.value,result.proof])
  accountProof proof
  let codecType ← inferType codec
  let reader := mkApp3 (mkConst ``ValueCodec.decode) codecType.appArg! codec literal
  let statement ← mkEq (← mkAppM ``Except.toOption #[reader])
    (← mkAppM ``Option.some #[result.value])
  let proof ← Hex.RCF.checkProof `ScalarQuote.accepted statement proof
  return {result with proof, usage := (← get).budget.consumed}

private def strictCodec (codec facts : Expr) : ReifyM Expr := do
  unless codec.getAppFn.isConstOf ``Algebraic.Element.codec do
    throwError "rcf: scalar quotation expects an Element.codec application"
  let parameters := (← getConstInfo ``Algebraic.Element.codec).type.getNumHeadForalls
  unless codec.getAppNumArgs == parameters do
    throwError "rcf: scalar quotation expects a complete codec application"
  let strictInfo ← getConstInfo ``Algebraic.Element.signCodec
  let acceptedInfo ← getConstInfo ``accepted
  unless codec.getAppFn.constLevels!.isEmpty && strictInfo.levelParams.isEmpty &&
      acceptedInfo.levelParams.isEmpty && strictInfo.type.getNumHeadForalls == parameters+1 &&
      acceptedInfo.type.getNumHeadForalls == parameters+4 do
    throwError "rcf: scalar quotation codec signatures do not match"
  checkFacts codec facts parameters
  return mkAppN (mkConst ``Algebraic.Element.signCodec codec.getAppFn.constLevels!)
    (codec.getAppArgs.push facts)

/-- Quote a supplied scalar inside an existing reflection request. The strict
reader, predecessor proposals and canonical transport all consume that request.
The caller supplies the enclosing transaction; `quote` provides one for an
ordinary `MetaM` predecessor callback. -/
def quoteWith (codec facts literal : Expr)
    (decode : RootQuote.DecoderM := fun _ => pure none) : ReifyM RootQuote.Result := do
  let codec ← instantiateMVars codec
  let facts ← instantiateMVars facts
  let literal ← instantiateMVars literal
  let strict ← strictCodec codec facts
  let reader := mkApp (.proj ``ValueCodec 1 strict) literal
  let result ← RootQuote.quoteWith reader decode
  finish codec facts literal result

/-- Quote the complete original polynomial reader through the owner's finite
sign codec, then use `Codec.readPoly_refines`. Retain its exact coefficient
type, zero/equality instances, codec arguments and literal. -/
def quotePolyWith (reader facts : Expr)
    (decode : RootQuote.DecoderM := fun _ => pure none) : ReifyM RootQuote.Result := do
  let reader ← instantiateMVars reader
  let facts ← instantiateMVars facts
  unless reader.getAppFn.isConstOf ``Codec.readPoly && reader.getAppNumArgs == 5 do
    throwError "rcf: polynomial quotation expects a complete readPoly application"
  for (name, arity) in #[( ``RootQuote.read_eq,5),( ``RootQuote.read_some,5),
      ( ``Codec.readPoly_refines,9)] do
    let info ← getConstInfo name
    unless info.levelParams.isEmpty && info.type.getNumHeadForalls == arity do
      throwError "rcf: polynomial quotation bridge signature does not match: {name}"
  let args := reader.getAppArgs
  let codec := args[3]!
  let strict ← strictCodec codec facts
  let soundness ← getConstInfo ``Algebraic.Element.signCodec_sound
  unless soundness.levelParams.isEmpty &&
      soundness.type.getNumHeadForalls == codec.getAppNumArgs+4 do
    throwError "rcf: polynomial quotation sign-codec soundness signature does not match"
  let strictReader := mkAppN reader.getAppFn (args.set! 3 strict)
  let result ← RootQuote.quoteWith strictReader decode
  let valueType ← inferType result.value
  let checked := mkAppN (mkConst ``RootQuote.read_eq)
    #[mkConst ``String,valueType,strictReader,result.value,result.proof]
  let refinement := mkAppN (mkConst ``Algebraic.Element.signCodec_sound codec.getAppFn.constLevels!)
    (codec.getAppArgs.push facts)
  let canonical := mkAppN (mkConst ``Codec.readPoly_refines)
    #[args[0]!,strict,codec,args[1]!,args[2]!,refinement,args[4]!,result.value,checked]
  let proof := mkAppN (mkConst ``RootQuote.read_some)
    #[mkConst ``String,valueType,reader,result.value,canonical]
  accountProof proof
  let statement ← mkEq (← mkAppM ``Except.toOption #[reader])
    (← mkAppM ``Option.some #[result.value])
  let proof ← Hex.RCF.checkProof `ScalarQuote.polynomial statement proof
  return {result with proof,usage := (← get).budget.consumed}

/-- Quote the exact demanded decode expression, retaining either its constant
or primitive projection form. A primitive projection is transported through
an equality checked with an abstract codec, so comparison never opens the
concrete canonical codec. The caller supplies the transaction. -/
def quoteDecodeWith (reader facts : Expr)
    (decode : RootQuote.DecoderM := fun _ => pure none) : ReifyM RootQuote.Result := do
  let reader ← instantiateMVars reader
  accountProof reader
  let reader ← Hex.RCF.checkExpr `ScalarQuote.reader reader
  Meta.check reader
  let (codec,literal,projected) ← match reader.getAppFn with
    | .proj ``ValueCodec 1 codec =>
      unless reader.getAppNumArgs == 1 do
        throwError "rcf: scalar quotation expects a complete decode projection"
      pure (codec,reader.appArg!,true)
    | .const ``ValueCodec.decode _ =>
      unless reader.getAppNumArgs == 3 do
        throwError "rcf: scalar quotation expects a complete decode application"
      pure (reader.getAppArgs[1]!,reader.getAppArgs[2]!,false)
    | _ => throwError "rcf: scalar quotation expects a ValueCodec decode"
  let result ← quoteWith codec facts literal decode
  let mut proof := result.proof
  if projected then
    let codecType ← inferType codec
    let (statement,candidate) ← liftM <| withLocalDeclD `codec codecType fun placeholder => do
      let source := mkApp3 (mkConst ``ValueCodec.decode) codecType.appArg! placeholder literal
      let target := mkApp (.proj ``ValueCodec 1 placeholder) literal
      let source ← mkAppM ``Except.toOption #[source]
      let target ← mkAppM ``Except.toOption #[target]
      let statement ← mkEq target source
      let candidate := mkExpectedPropHint (← mkEqRefl source) statement
      return (← mkForallFVars #[placeholder] statement,← mkLambdaFVars #[placeholder] candidate)
    accountProof statement
    accountProof candidate
    let bridge ← Hex.RCF.checkProof `ScalarQuote.projection statement candidate
    proof ← mkEqTrans (mkApp bridge codec) proof
  let statement ← mkEq (← mkAppM ``Except.toOption #[reader])
    (← mkAppM ``Option.some #[result.value])
  accountProof proof
  let checked ← Hex.RCF.checkProof `ScalarQuote.decode statement proof
  return {result with proof := checked,usage := (← get).budget.consumed}

/-- Quote a literal through the owner's finite supplied-sign codec and return
an ordinary-kernel equation for its canonical decoder. The canonical
`Element.codec` application retains all original implicit arguments; reinference
can unfold a native decoder merely to compare definitionally equal aliases.
The predecessor decoder and already checked sign facts are explicit inputs. Missing/mismatched facts
reject; a failed quote never starts the canonical decoder or another solver.
The facts list's declared element type must use the original context under
reducible transparency; aliases in that index need explicit type transport.
Assigned inputs are instantiated before their work is charged.
Reader quotation and final transport continue one reflection request. Failure
restores all state, including auxiliaries from an earlier successful stage.
This does not reconstruct source coefficients, models or context histories. -/
def quote (codec facts literal : Expr) (decode : RootQuote.Decoder := fun _ => pure none)
    (config : Hex.RealFormula.Reify.Config := {})
    (usage : Hex.Reflect.BudgetUsage := Hex.Reflect.Budget.zero) :
    MetaM (Except Hex.RealFormula.Reify.Error RootQuote.Result) :=
  RootQuote.runWith
    (quoteWith codec facts literal (fun expression => liftM (decode expression))) config usage

end Hex.RCF.RealCoefficients.ScalarQuote
