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

/-- A decoded vector already stored by a normalized polynomial is accepted
without computing normalization or coefficient equality in the quoted proof. -/
theorem polynomialAccepted {E : Type} [Zero E] [DecidableEq E]
    (value : ValueCodec E) (literal : Codec.Json) (p : DensePoly E)
    (checked : Codec.readArray value.decode literal = .ok p.toArray) :
    Codec.readPoly value literal = .ok p := by
  unfold Codec.readPoly
  rw [checked]
  simp only [bind, Except.bind, DensePoly.ofCoeffs_toArray]
  simp [pure, Except.pure]

/-- The empty decoded vector already satisfies the normalization invariant. -/
theorem normalizedEmpty {E : Type} [Zero E] [DecidableEq E]
    (values : Array E) (checked : values.size = 0) : DensePolyNormalized values :=
  Or.inl checked

/-- Certify the normalized-vector invariant from its final nonzero entry. -/
theorem normalizedBack {E : Type} [Zero E] [DecidableEq E]
    (values : Array E) (last : E) (checked : values.back? = some last)
    (nonzero : last ≠ 0) : DensePolyNormalized values := by
  right
  intro zero
  exact nonzero (Option.some.inj (checked.symm.trans zero))

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

/-- Quote the coefficient array through the owner's finite sign codec,
certify its normalization, then use `Codec.readPoly_refines`. Retain its exact coefficient
type, zero/equality instances, codec arguments and literal. -/
def quotePolyWith (reader facts : Expr)
    (decode : RootQuote.DecoderM := fun _ => pure none) : ReifyM RootQuote.Result := do
  let reader ← instantiateMVars reader
  let facts ← instantiateMVars facts
  unless reader.getAppFn.isConstOf ``Codec.readPoly && reader.getAppNumArgs == 5 do
    throwError "rcf: polynomial quotation expects a complete readPoly application"
  for (name, arity) in #[( ``RootQuote.read_eq,5),( ``RootQuote.read_some,5),
      ( ``Codec.readPoly_refines,9),( ``polynomialAccepted,7),( ``normalizedBack,7),( ``normalizedEmpty,5)] do
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
  let arrayReader ← mkAppM ``Codec.readArray #[.proj ``ValueCodec 1 strict,args[4]!]
  let arrayResult ← RootQuote.quoteWith arrayReader decode
  -- Construct the normalized polynomial from this exact vector. Public sign
  -- laws certify its last entry, so no private field or normalization proof
  -- is recomputed while comparing dependent array-bound arguments.
  let instances := args.extract 0 3
  charge .proofNodes 1
  let last ← whnf (← mkAppM ``Array.back? #[arrayResult.value])
  let normalizedType := mkAppN (mkConst ``DensePolyNormalized [0])
    (instances.push arrayResult.value)
  let normalized ← if last.isAppOfArity ``Option.none 1 then do
    let sizeZero ← mkEq (← mkAppM ``Array.size #[arrayResult.value]) (mkNatLit 0)
    let empty := mkExpectedPropHint (← mkEqRefl (mkNatLit 0)) sizeZero
    pure (mkAppN (mkConst ``normalizedEmpty) (instances ++ #[arrayResult.value,empty]))
  else do
    unless last.isAppOfArity ``Option.some 2 do
      throwError "rcf: quoted coefficient vector has no literal final entry"
    charge .proofNodes 1
    let value ← withoutModifyingEnv <| withFreshCache do
      setReducibilityStatus ``Algebraic.Element.restore .irreducible
      withTransparency .default (whnf last.appArg!)
    unless value.getAppFn.isConstOf ``Algebraic.Element.restore do
      abort (.providerFailure (.invalidProviderEvidence ⟨`Hex.RCF.RealCoefficients.RootQuote,0⟩
        "literal reader rejected its supplied input") #[])
    let parameters := value.getAppArgs
    let restore ← getConstInfo ``Algebraic.Element.restore
    let sign ← getConstInfo ``Algebraic.Element.restore_sign
    let zero ← getConstInfo ``Algebraic.Element.sign_eq_zero
    unless parameters.size == restore.type.getNumHeadForalls &&
        sign.type.getNumHeadForalls == parameters.size &&
        zero.type.getNumHeadForalls+3 == parameters.size &&
        restore.levelParams.length == value.getAppFn.constLevels!.length &&
        sign.levelParams.length == restore.levelParams.length &&
        zero.levelParams.length == restore.levelParams.length do
      throwError "rcf: polynomial normalization owner signatures do not match"
    let signLaw := mkAppN
      (mkConst ``Algebraic.Element.restore_sign value.getAppFn.constLevels!) parameters
    let zeroLaw := mkAppN
      (mkConst ``Algebraic.Element.sign_eq_zero value.getAppFn.constLevels!)
      ((parameters.extract 0 (parameters.size-4)).push value)
    let zero ← mkAppOptM ``Zero.zero #[some args[0]!,some args[1]!]
    let proposition ← mkEq value zero
    let nonzero ← liftM <| withLocalDeclD `zero proposition fun h => do
      let signZero ← mkAppM ``Iff.mpr #[zeroLaw,h]
      let contradiction := mkApp parameters.back! (← mkEqTrans (← mkEqSymm signLaw) signZero)
      mkLambdaFVars #[h] contradiction
    let back ← mkAppM ``Array.back? #[arrayResult.value]
    let backType ← mkEq back last
    let backProof := mkExpectedPropHint (← mkEqRefl last) backType
    pure (mkAppN (mkConst ``normalizedBack)
      (instances ++ #[arrayResult.value,value,backProof,nonzero]))
  let normalized := mkExpectedPropHint normalized normalizedType
  accountProof normalized
  let normalized ← Hex.RCF.checkProof `ScalarQuote.normalized normalizedType normalized
  let polynomial := mkAppN (mkConst ``DensePoly.mk [0])
    #[args[0]!,args[1]!,args[2]!,arrayResult.value,normalized]
  let arrayType ← inferType arrayResult.value
  let arrayChecked := mkAppN (mkConst ``RootQuote.read_eq)
    #[mkConst ``String,arrayType,arrayReader,arrayResult.value,arrayResult.proof]
  let strictChecked := mkAppN (mkConst ``polynomialAccepted)
    (instances ++ #[strict,args[4]!,polynomial,arrayChecked])
  let strictProof ← mkAppM ``RootQuote.read_some #[strictReader,polynomial,strictChecked]
  let result : RootQuote.Result := {arrayResult with value := polynomial,proof := strictProof}
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

/-- Build a recursive predecessor callback from checked sign-fact inputs.
The lookup receives the exact canonical codec expression; return `none` when
no facts are supplied. Noncanonical decodes are proposed only by `base`.
Every selected-field stage uses `quoteDecodeWith`, preserving the original
codec and charging the same reflection request. Missing facts decline without
running a canonical decoder. Errors, exhaustion and recursion limits remain
terminal. The enclosing `RootQuote.runWith` transaction restores state.
Each callback probe is charged, including probes delegated to `base`. A declining
lookup can be probed again after reduction; lookups must tolerate repeated calls.
This consumes explicit facts; it does not discover or authenticate histories. -/
partial def decoderWith (factsFor : Expr → ReifyM (Option Expr))
    (base : RootQuote.DecoderM := fun _ => pure none) (reader : Expr) :
    ReifyM (Option Expr) := Core.withIncRecDepth do
  charge .proofNodes 1
  Core.checkSystem "recursive scalar quotation"
  let codec? := match reader.getAppFn with
    | .proj ``ValueCodec 1 codec =>
      if reader.getAppNumArgs == 1 then some codec else none
    | .const ``ValueCodec.decode _ =>
      if reader.getAppNumArgs == 3 then some reader.getAppArgs[1]! else none
    | _ => none
  let some codec := codec? | return ← base reader
  unless codec.getAppFn.isConstOf ``Algebraic.Element.codec do return ← base reader
  let some facts ← factsFor codec | return none
  let result ← quoteDecodeWith reader facts (decoderWith factsFor base)
  let valueType ← inferType result.value
  let proof := mkAppN (mkConst ``RootQuote.read_eq)
    #[mkConst ``String,valueType,reader,result.value,result.proof]
  let output := mkAppN (mkConst ``Except.ok [0,0])
    #[mkConst ``String,valueType,result.value]
  let statement ← mkEq reader output
  accountProof proof
  return some (← Hex.RCF.checkProof `ScalarQuote.recursive statement proof)

end Hex.RCF.RealCoefficients.ScalarQuote
