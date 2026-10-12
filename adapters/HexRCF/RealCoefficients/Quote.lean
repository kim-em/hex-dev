/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerModel
public meta import HexRCF.RealCoefficients.Reify
public meta import HexRCF.Tactic

public meta section
namespace Hex.RCF.RealCoefficients.Quote
open Lean Meta

/-- Check and transport one frozen existential acceptance to its original
source. `arity` is the canonical checker's explicit arity; both supported
checkers have three implicit indices. The caller supplies the original model,
fixed valuation equality and every ordered divisor identity. Guard identities
are mandatory protocol checks; the unconditional source equivalence does not
make them logical premises of the source proposition. -/
def finish (checkerName soundName : Name) (arity : Nat)
    (target checker accepted valuationIdentity : Expr) (original : Option Expr)
    (guardIdentities : Array Expr := #[]) : MetaM Expr := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
    let target ← Hex.RCF.checkExpr `Quote.target target
    let checker ← Hex.RCF.checkExpr `Quote.checker checker
    unless checker.getAppFn.isConstOf checkerName do
      throwError "rcf: expected the canonical frozen checker"
    let arguments := checker.getAppArgs
    unless arguments.size == arity + 3 do throwError "rcf: incorrect frozen checker arity"
    let arguments := arguments.extract 3 arguments.size
    let hasModel := original.isNone
    let original ← Hex.RCF.checkExpr `Quote.original (original.getD arguments[0]!)
    let offset := if hasModel then 1 else 0
    let values := arguments[1 + offset]!
    let guards := arguments[2 + offset]!
    let matrix := arguments[3 + offset]!
    let resultType ← whnf (← inferType checker)
    let trueResult := mkAppN (mkConst ``Except.ok [.zero, .zero])
      (resultType.getAppArgs.push (mkConst ``Bool.true))
    let accepted ← Hex.RCF.checkProof `Quote.accepted
      (← mkEq checker trueResult) accepted
    let source ← match ← Reify.prepare target with
      | .error error => throwError "rcf: {Hex.RealFormula.Reify.Error.toMessageData error}"
      | .ok source => pure source
    unless guardIdentities.size == source.divisors.size do
      throwError "rcf: frozen checker omitted an original divisor identity"
    let length ← mkAppM ``List.length #[guards]
    let count ← mkEq length (mkNatLit source.divisors.size)
    let countProof ← mkDecideProof count
    let _ ← Hex.RCF.checkProof `Quote.guardCount count countProof
    for i in [:source.divisors.size] do
      let bound ← mkDecideProof (← mkLt (mkNatLit i) length)
      let index ← mkAppM ``Fin.mk #[mkNatLit i, bound]
      let guard ← mkAppM ``List.get #[guards, index]
      let interpreted ← mkAppM ``Hex.RealClosure.Tower.Model.value #[original, guard]
      let _ ← Hex.RCF.checkProof `Quote.guardIdentity
        (← mkEq interpreted source.divisors[i]!) guardIdentities[i]!
    let coordinateType ← inferType values
    let .forallE _ domain _ _ ← whnf coordinateType
      | throwError "rcf: frozen coefficients are not a finite valuation"
    let valuation ← withLocalDeclD `i domain fun i => do
      let interpreted ← mkAppM ``Hex.RealClosure.Tower.Model.value #[original, mkApp values i]
      mkLambdaFVars #[i] interpreted
    let valuationIdentity ← Hex.RCF.checkProof `Quote.valuation
      (← mkEq valuation source.valuation) valuationIdentity
    let matrixFormula ← mkAppM ``Hex.RealFormula.Prenex.matrix #[matrix]
    let formula ← mkAppM ``Hex.RealFormula.Prenex.quant
      #[mkConst ``Hex.RealFormula.Quantifier.existsReal, matrixFormula]
    let formulaIdentity ← mkDecideProof (← mkEq formula source.formula)
    let _ ← Hex.RCF.checkProof `Quote.formula
      (← mkEq formula source.formula) formulaIdentity
    let soundArguments := if hasModel then arguments else #[original] ++ arguments
    let witness ← mkAppM soundName (soundArguments.push accepted)
    let nativeSentence ← mkAppM ``Hex.RealFormula.Prenex.toProp #[formula, valuation]
    let witness ← Hex.RCF.checkProof `Quote.witness nativeSentence witness
    let formulaCongr ← withLocalDeclD `sentence (← inferType formula) fun sentence => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[sentence, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[sentence] body, formulaIdentity]
    let fixed ← mkAppM ``Eq.mp #[formulaCongr, witness]
    let valuationCongr ← withLocalDeclD `valuation (← inferType source.valuation) fun valuation => do
      let body ← mkAppM ``Hex.RealFormula.Prenex.toProp #[source.formula, valuation]
      mkAppM ``congrArg #[← mkLambdaFVars #[valuation] body, valuationIdentity]
    let specialized ← mkAppM ``Eq.mp #[valuationCongr, fixed]
    let proof ← mkAppM ``Iff.mp #[source.proof, specialized]
    Hex.RCF.checkProof `Quote.source source.original proof)
    (fun result => unless result.isSome do saved.restore)
  return result

end Hex.RCF.RealCoefficients.Quote
