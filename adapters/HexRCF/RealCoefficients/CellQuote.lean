/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public import HexRCF.RealCoefficients.CellReplay
public import HexRCF.RealCoefficients.CompleteReplay
public meta import HexRCF.RealCoefficients.Quote
public meta section
namespace Hex.RCF.RealCoefficients.CellQuote
open Lean Meta

/-- Shared original-source authentication for typed cells and independently
read complete packets. Both entrypoints retain ordered guards and rollback. -/
private def finishWith (packet : Bool) (target checker accepted model valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
    let target ← Hex.RCF.checkExpr `CellQuote.target target
    let checker ← Hex.RCF.checkExpr `CellQuote.checker checker
    let checkerName := if packet then ``CompleteReplay.check else ``CellReplay.check
    unless checker.getAppFn.isConstOf checkerName do
      throwError "rcf: expected the canonical cell checker"
    let arguments := checker.getAppArgs
    let information ← getFunInfoNArgs checker.getAppFn arguments.size
    let mut inputs : Array Expr := #[]
    for i in [:min arguments.size information.paramInfo.size] do
      if information.paramInfo[i]!.binderInfo.isExplicit then inputs := inputs.push arguments[i]!
    unless inputs.size == (if packet then 8 else 7) do
      throwError "rcf: incorrect cell checker arity"
    let offset := if packet then 1 else 0
    let values := inputs[offset]!
    let matrix := inputs[offset+1]!
    let guards := inputs[offset+2]!
    let quantifier := inputs[if packet then 5 else 6]!
    let model ← Hex.RCF.checkExpr `CellQuote.model model
    let resultType ← whnf (← inferType checker)
    let trueResult := mkAppN (mkConst ``Except.ok [.zero, .zero])
      (resultType.getAppArgs.push (mkConst ``Bool.true))
    let accepted ← Hex.RCF.checkProof `CellQuote.accepted (← mkEq checker trueResult) accepted
    let source ← match ← Reify.prepare target with
      | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
      | .ok source => pure source
    unless guardIdentities.size == source.divisors.size do
      throwError "rcf: cell checker has a different original divisor identity count"
    let length ← mkAppM ``List.length #[guards]
    let count ← mkEq length (mkNatLit source.divisors.size)
    let decision ← mkDecide count
    let result ← ofExceptKernelException (Kernel.whnf (← getEnv) (← getLCtx) decision)
    unless result.isConstOf ``Bool.true do
      throwError "rcf: cell checker has a different original divisor count"
    let _ ← Hex.RCF.checkProof `CellQuote.guardCount count (← mkDecideProof count)
    let proofInputs := #[model] ++ inputs
    let domains ← mkAppM (if packet then ``CompleteReplay.check_domains else ``CellReplay.check_domains)
      ((proofInputs.push (mkConst ``Bool.true)).push accepted)
    let domains ← Hex.RCF.checkProof `CellQuote.domains (← inferType domains) domains
    for i in [:source.divisors.size] do
      let bound ← mkDecideProof (← mkLt (mkNatLit i) length)
      let index ← mkAppM ``Fin.mk #[mkNatLit i, bound]
      let guard ← mkAppM ``List.get #[guards, index]
      let interpreted ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model, guard]
      let identity ← Hex.RCF.checkProof `CellQuote.guardIdentity
        (← mkEq interpreted source.divisors[i]!) guardIdentities[i]!
      let member ← mkAppM ``List.get_mem #[guards, index]
      let nonzero ← mkAppM' domains #[guard, member]
      let realZero := (← inferType nonzero).getAppArgs.back!
      let comparison ← withLocalDeclD `value (← inferType interpreted) fun value => do
        let body ← mkAppM ``Ne #[value, realZero]
        mkAppM ``congrArg #[← mkLambdaFVars #[value] body, identity]
      let conclusion ← mkAppM ``Eq.mp #[comparison, nonzero]
      let _ ← Hex.RCF.checkProof `CellQuote.divisor
        (← mkAppM ``Ne #[source.divisors[i]!, realZero]) conclusion
    let .forallE _ domain _ _ ← whnf (← inferType values)
      | throwError "rcf: cell coefficients are not a finite valuation"
    let valuation ← withLocalDeclD `i domain fun i => do
      let value ← mkAppM ``Hex.RealClosure.Tower.Model.value #[model, mkApp values i]
      mkLambdaFVars #[i] value
    let valuationIdentity ← Hex.RCF.checkProof `CellQuote.valuationIdentity
      (← mkEq valuation source.valuation) valuationIdentity
    let formula ← mkAppM ``Hex.RealFormula.Prenex.quant
      #[quantifier, ← mkAppM ``Hex.RealFormula.Prenex.matrix #[matrix]]
    let formulaIdentity ← Quote.formulaEquality formula source.formula
    let formulaIdentity ← Hex.RCF.checkProof `CellQuote.formulaIdentity
      (← mkEq formula source.formula) formulaIdentity
    let sentence ← mkAppM (if packet then ``CompleteReplay.check_sound else ``CellReplay.check_sound)
      (proofInputs.push accepted)
    let sentence ← Hex.RCF.checkProof `CellQuote.sentence
      (← mkAppM ``Hex.RealFormula.Prenex.toProp #[formula, valuation]) sentence
    let formulaCongr ← withLocalDeclD `sentence (← inferType formula) fun sentence => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[sentence, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[sentence] body, formulaIdentity]
    let fixed ← mkAppM ``Eq.mp #[formulaCongr, sentence]
    let valuationCongr ← withLocalDeclD `valuation (← inferType source.valuation) fun valuation => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[valuation] body, valuationIdentity]
    let specialized ← mkAppM ``Eq.mp #[valuationCongr, fixed]
    let proof ← mkAppM ``Iff.mp #[source.proof, specialized]
    Hex.RCF.checkProof `CellQuote.source source.original proof)
    (fun result => unless result.isSome do saved.restore)
  return result
/-- Quote a checked typed cell fold at the freshly reified original goal. -/
def finish (target checker accepted model valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr :=
  finishWith false target checker accepted model valuationIdentity guardIdentities

/-- Quote independently checked full root/cell packets, retaining the same
source formula, fixed valuation, original divisor and state-restoration checks. -/
def finishPacket (target checker accepted model valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr :=
  finishWith true target checker accepted model valuationIdentity guardIdentities

end Hex.RCF.RealCoefficients.CellQuote
