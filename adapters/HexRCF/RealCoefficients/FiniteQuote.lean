/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.FiniteSigns
public meta import HexRCF.RealCoefficients.Quote

public meta section
namespace Hex.RCF.RealCoefficients.FiniteQuote
open Lean Meta

/-- Retain the checker's leading type and operation arguments. Additional
implicit indices in a law are inferred from its explicit semantic inputs. -/
private def applyLaw (name : Name) (common inputs : Array Expr) : MetaM Expr := do
  let mut type := (← getConstInfo name).type
  let mut arguments := common.map some
  for _ in [:common.size] do
    unless type.isForall do throwError "rcf: incorrect finite-sign law prefix"
    type := type.bindingBody!
  let mut index := 0
  while type.isForall && index < inputs.size do
    if type.bindingInfo!.isExplicit then
      unless index < inputs.size do throwError "rcf: missing finite-sign law input"
      arguments := arguments.push (some inputs[index]!)
      index := index + 1
    else arguments := arguments.push none
    type := type.bindingBody!
  unless index == inputs.size do throwError "rcf: extra finite-sign law input"
  mkAppOptM name arguments

/-- Quote canonical finite-row acceptance at its authenticated source valuation.
The supplied descriptor, replay and binding proofs establish the joint real
semantics. The supplied guard list must match every original divisor exactly in
source order, with checked identities and nonvanishing conclusions. -/
def finish (target checker accepted read zero unit descriptor replay valuation binding
    valuationIdentity : Expr) (guardIdentities : Array Expr := #[]) : MetaM Expr := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
    let target ← Hex.RCF.checkExpr `FiniteQuote.target target
    let checker ← Hex.RCF.checkExpr `FiniteQuote.checker checker
    unless checker.getAppFn.isConstOf ``FiniteSigns.check do
      throwError "rcf: expected the canonical finite-sign checker"
    let arguments := checker.getAppArgs
    let information ← getFunInfoNArgs checker.getAppFn arguments.size
    let mut explicitArguments : Array Expr := #[]
    for i in [:min arguments.size information.paramInfo.size] do
      if information.paramInfo[i]!.binderInfo.isExplicit then explicitArguments := explicitArguments.push arguments[i]!
    unless explicitArguments.size == 5 do throwError "rcf: incorrect finite-sign checker arity"
    let common := arguments.extract 0
      (information.paramInfo.takeWhile (fun parameter => !parameter.binderInfo.isExplicit)).size
    let context := explicitArguments[0]!
    let guards := explicitArguments[1]!
    let queries := explicitArguments[2]!
    let selected := explicitArguments[3]!
    let matrix := explicitArguments[4]!
    let read ← Hex.RCF.checkExpr `FiniteQuote.read read
    let zero ← Hex.RCF.checkExpr `FiniteQuote.zero zero
    let unit ← Hex.RCF.checkExpr `FiniteQuote.unit unit
    let descriptor ← Hex.RCF.checkExpr `FiniteQuote.descriptor descriptor
    let descriptor ← Hex.RCF.checkProof `FiniteQuote.descriptor (← inferType descriptor) descriptor
    let replay ← Hex.RCF.checkExpr `FiniteQuote.replay replay
    let replay ← Hex.RCF.checkProof `FiniteQuote.replay (← inferType replay) replay
    let binding ← Hex.RCF.checkExpr `FiniteQuote.binding binding
    let binding ← Hex.RCF.checkProof `FiniteQuote.binding (← inferType binding) binding
    let valuation ← Hex.RCF.checkExpr `FiniteQuote.valuation valuation
    let resultType ← whnf (← inferType checker)
    let trueResult := mkAppN (mkConst ``Except.ok [.zero, .zero])
      (resultType.getAppArgs.push (mkConst ``Bool.true))
    let source ← match ← Reify.prepare target with
      | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
      | .ok source => pure source
    unless guardIdentities.size == source.divisors.size do
      throwError "rcf: finite checker has a different original divisor identity count"
    let length ← mkAppM ``List.length #[guards]
    let count ← mkEq length (mkNatLit source.divisors.size)
    let countDecision ← mkDecide count
    let countValue ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) countDecision)
    unless countValue.isConstOf ``Bool.true do
      throwError "rcf: finite checker has a different original divisor count"
    let _ ← Hex.RCF.checkProof `FiniteQuote.guardCount count (← mkDecideProof count)
    let accepted ← Hex.RCF.checkProof `FiniteQuote.accepted (← mkEq checker trueResult) accepted
    let domains ← applyLaw ``FiniteSigns.check_domains common
      #[context, read, zero, unit, descriptor, guards, queries, selected, replay, matrix,
        mkConst ``Bool.true, accepted]
    let domains ← Hex.RCF.checkProof `FiniteQuote.domains (← inferType domains) domains
    for i in [:source.divisors.size] do
      let bound ← mkDecideProof (← mkLt (mkNatLit i) length)
      let index ← mkAppM ``Fin.mk #[mkNatLit i, bound]
      let guard ← mkAppM ``List.get #[guards, index]
      let identity ← Hex.RCF.checkProof `FiniteQuote.guardIdentity
        (← mkEq (mkApp read guard) source.divisors[i]!) guardIdentities[i]!
      let member ← mkAppM ``List.get_mem #[guards, index]
      let nonzero ← mkAppM' domains #[guard, member]
      let realZero := (← inferType nonzero).getAppArgs.back!
      let comparison ← withLocalDeclD `value (← inferType (mkApp read guard)) fun value => do
        let body ← mkAppM ``Ne #[value, realZero]
        mkAppM ``congrArg #[← mkLambdaFVars #[value] body, identity]
      let conclusion ← mkAppM ``Eq.mp #[comparison, nonzero]
      let _ ← Hex.RCF.checkProof `FiniteQuote.divisor
        (← mkAppM ``Ne #[source.divisors[i]!, realZero]) conclusion
    let valuationIdentity ← Hex.RCF.checkProof `FiniteQuote.valuationIdentity
      (← mkEq valuation source.valuation) valuationIdentity
    let formula ← mkAppM ``Hex.RealFormula.Prenex.quant
      #[mkConst ``Hex.RealFormula.Quantifier.existsReal,
        ← mkAppM ``Hex.RealFormula.Prenex.matrix #[matrix]]
    let formulaIdentity ← Quote.formulaEquality formula source.formula
    let formulaIdentity ← Hex.RCF.checkProof `FiniteQuote.formulaIdentity
      (← mkEq formula source.formula) formulaIdentity
    let witness ← applyLaw ``FiniteSigns.check_sound common
      #[context, read, zero, unit, descriptor, guards, queries, selected, replay, valuation,
        matrix, binding, accepted]
    let sentence ← mkAppM ``Hex.RealFormula.Prenex.toProp #[formula, valuation]
    let witness ← Hex.RCF.checkProof `FiniteQuote.witness sentence witness
    let formulaCongr ← withLocalDeclD `sentence (← inferType formula) fun sentence => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[sentence, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[sentence] body, formulaIdentity]
    let fixed ← mkAppM ``Eq.mp #[formulaCongr, witness]
    let valuationCongr ← withLocalDeclD `valuation (← inferType source.valuation) fun valuation => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[valuation] body, valuationIdentity]
    let specialized ← mkAppM ``Eq.mp #[valuationCongr, fixed]
    let proof ← mkAppM ``Iff.mp #[source.proof, specialized]
    Hex.RCF.checkProof `FiniteQuote.source source.original proof)
    (fun result => unless result.isSome do saved.restore)
  return result

end Hex.RCF.RealCoefficients.FiniteQuote
