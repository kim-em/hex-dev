/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRealClosure.SignCodec
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
    MetaM (Except Hex.RealFormula.Reify.Error RootQuote.Result) := do
  let saved ← saveState
  let depthLimit := (← readThe Core.Context).maxRecDepth
  let auxName := mkPrivateName (← getEnv) (← mkFreshUserName `ScalarQuote)
  let (result,_) ← tryFinally' (withDeclNameForAuxNaming auxName <| withNewMCtxDepth <|
      Core.withIncRecDepth <| withOptions (fun options => maxRecDepth.set
        (debug.skipKernelTC.set (Elab.async.set options false) false) depthLimit) do
    let codec ← instantiateMVars codec
    let facts ← instantiateMVars facts
    let literal ← instantiateMVars literal
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
    let preflight ← ((checkFacts codec facts parameters).run
      {config,budget := {initial := config.ring.budget,consumed := usage}}).run
    let usage ← match preflight with
      | .error error => return .error error
      | .ok (_,state) => pure state.budget.consumed
    let strict := mkAppN (mkConst ``Algebraic.Element.signCodec codec.getAppFn.constLevels!)
      (codec.getAppArgs.push facts)
    let reader := mkApp (.proj ``ValueCodec 1 strict) literal
    let quoted ← RootQuote.quote reader decode config usage
    let result ← match quoted with
      | .error error => return .error error
      | .ok result => pure result
    let action := (finish codec facts literal result).run
      {config,budget := {initial := config.ring.budget,consumed := result.usage}}
    match ← action.run with
    | .error error => return .error error
    | .ok (result,_) => return .ok result) fun result => do
      match result with
      | some (.ok _) => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed,
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds}
      | _ => saved.restore
  return result

end Hex.RCF.RealCoefficients.ScalarQuote
