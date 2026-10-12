/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRCF.RealCoefficients.SectionReplay
public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.Tactic

public meta section
namespace Hex.RCF.RealCoefficients.SectionQuote
open Lean Meta

/-- Compose literal section acceptance with a freshly reified original source.
The caller supplies the fixed valuation equality and an identity for each
original divisor in order. This operation checks every proof and the exact
matrix/quantifier binding before returning an ordinary proof of the target.
It neither produces evidence nor assigns a goal. -/
def finish (target checker accepted valuationIdentity : Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
    let target ← Hex.RCF.checkExpr `SectionQuote.target target
    let checker ← Hex.RCF.checkExpr `SectionQuote.checker checker
    unless checker.getAppFn.isConstOf ``SectionReplay.check do
      throwError "rcf: expected the canonical frozen section checker"
    let arguments := checker.getAppArgs
    unless arguments.size ≥ 8 do throwError "rcf: incomplete section checker"
    let arguments := arguments.extract (arguments.size - 8) arguments.size
    let original := arguments[0]!
    let values := arguments[2]!
    let guards := arguments[3]!
    let matrix := arguments[4]!
    let resultType ← whnf (← inferType checker)
    let trueResult := mkAppN (mkConst ``Except.ok [.zero, .zero])
      (resultType.getAppArgs.push (mkConst ``Bool.true))
    let accepted ← Hex.RCF.checkProof `SectionQuote.accepted
      (← mkEq checker trueResult) accepted
    let source ← match ← Reify.prepare target with
      | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
      | .ok source => pure source
    unless guardIdentities.size == source.divisors.size do
      throwError "rcf: frozen section omitted an original divisor identity"
    let length ← mkAppM ``List.length #[guards]
    let count ← mkEq length (mkNatLit source.divisors.size)
    let countProof ← mkDecideProof count
    let _ ← Hex.RCF.checkProof `SectionQuote.guardCount count countProof
    for i in [:source.divisors.size] do
      let bound ← mkDecideProof (← mkLt (mkNatLit i) length)
      let index ← mkAppM ``Fin.mk #[mkNatLit i, bound]
      let guard ← mkAppM ``List.get #[guards, index]
      let interpreted ← mkAppM ``Hex.RealClosure.Tower.Model.value #[original, guard]
      let _ ← Hex.RCF.checkProof `SectionQuote.guardIdentity
        (← mkEq interpreted source.divisors[i]!) guardIdentities[i]!
    let coordinateType ← inferType values
    let .forallE _ domain _ _ ← whnf coordinateType
      | throwError "rcf: section coefficients are not a finite valuation"
    let valuation ← withLocalDeclD `i domain fun i => do
      let interpreted ← mkAppM ``Hex.RealClosure.Tower.Model.value #[original, mkApp values i]
      mkLambdaFVars #[i] interpreted
    let valuationIdentity ← Hex.RCF.checkProof `SectionQuote.valuation
      (← mkEq valuation source.valuation) valuationIdentity
    let matrixFormula ← mkAppM ``Hex.RealFormula.Prenex.matrix #[matrix]
    let formula ← mkAppM ``Hex.RealFormula.Prenex.quant
      #[mkConst ``Hex.RealFormula.Quantifier.existsReal, matrixFormula]
    let formulaIdentity ← mkDecideProof (← mkEq formula source.formula)
    let _ ← Hex.RCF.checkProof `SectionQuote.formula
      (← mkEq formula source.formula) formulaIdentity
    let witness ← mkAppM ``SectionReplay.check_sound (arguments.push accepted)
    let nativeSentence ← mkAppM ``Hex.RealFormula.Prenex.toProp #[formula, valuation]
    let witness ← Hex.RCF.checkProof `SectionQuote.witness nativeSentence witness
    let formulaCongr ← withLocalDeclD `sentence (← inferType formula) fun sentence => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[sentence, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[sentence] body, formulaIdentity]
    let fixed ← mkAppM ``Eq.mp #[formulaCongr, witness]
    let valuationCongr ← withLocalDeclD `valuation (← inferType source.valuation) fun valuation => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[valuation] body, valuationIdentity]
    let specialized ← mkAppM ``Eq.mp #[valuationCongr, fixed]
    let proof ← mkAppM ``Iff.mp #[source.proof, specialized]
    Hex.RCF.checkProof `SectionQuote.source source.original proof)
    (fun result => unless result.isSome do saved.restore)
  return result

end Hex.RCF.RealCoefficients.SectionQuote
