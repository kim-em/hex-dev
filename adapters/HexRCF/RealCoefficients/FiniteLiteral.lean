/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexRCF.RealCoefficients.FiniteIndex
public meta section

namespace Hex.RCF.RealCoefficients.FiniteLiteral
open Hex Lean Meta Qq

/-- Quote and check finite real-cell evidence. The native field instance is
used only to produce the frozen candidate; its proof is never quoted here.
The expected quantified formula is constructed independently of the candidate.
The caller authenticates the original source and divisor proofs. -/
meta def prove {p : ZPoly} {s : DyadicSquare}
    {hw : atomWitness p s} {hp : (mahlerPrec p : Int) ≤ s.prec}
    [ZPoly.CheckedIrreducible p] {n : Nat}
    (pExpr rootExpr valuesExpr formulaExpr : Expr)
    (values : Fin n → PolyQuot p (SimpleRoot.ofSquare p s hw hp))
    (formula : RealFormula.QF (n + 1)) (quantifier : RealFormula.Quantifier)
    (extraSignKeys : List (PolyQuot p (SimpleRoot.ofSquare p s hw hp)) := []) : MetaM Expr := do
  let query := RepresentationSpecialize.polynomial values
  let data ← FieldLiteral.produceRefining values formula quantifier extraSignKeys
    (fun data => unless FieldCells.check data.signs () query formula data.radical
        data.isolation data.rootSigns do
      throwError "rcf: finite real-cell certificate failed replay")
    (fun data => FieldCells.keys query formula data.radical.core data.isolation data.rootSigns)
  let certificate ← FieldLiteral.resultExpr pExpr rootExpr formulaExpr formula data
  let radical ← mkAppM ``FieldBuild.Result.radical #[certificate]
  let isolation ← mkAppM ``FieldBuild.Result.isolation #[certificate]
  let rows ← mkAppM ``FieldBuild.Result.rootSigns #[certificate]
  let signs ← mkAppM ``FieldBuild.Result.signs #[certificate]
  let queryExpr ← mkAppM ``RepresentationSpecialize.polynomial #[valuesExpr]
  let indexed := FieldLiteral.rcf.algebraic.indexSigns.get (← getOptions)
  let index := if indexed then LiteralSign.Index.build data.signs.entries.toArray Field.keyOrder
    else LiteralSign.Index.empty
  let routing ← mkAppOptM ``Field.keyOrder #[some pExpr,some rootExpr]
  let quotedIndex := FieldLiteral.indexExpr index
  let arguments := #[signs,q(()),queryExpr,formulaExpr,radical,isolation,rows]
  let checkName := if indexed then ``FieldCells.checkIndex else ``FieldCells.check
  let check ← if indexed then
    mkAppM checkName #[signs,routing,quotedIndex,q(()),queryExpr,formulaExpr,radical,isolation,rows]
  else mkAppM checkName arguments
  let candidate ← mkFreshExprMVar (← mkEq check q(true))
  let lemmas ← FieldLiteral.evidenceLemmas
  let checker := mkIdent checkName
  let remaining ← profileitM Exception "rcf finite literal replay" (← getOptions) do
    Elab.runTactic' candidate.mvarId! (← `(tactic|
      (simp only [$checker:ident,FieldIsolation.check,FieldQuery.check,FieldQuery.covered,
        FieldRootSigns.Table.checkTransport,FieldRootSigns.Table.checkRows,
        FieldTransport.leadingCheck,$lemmas,*,Bool.and_eq_true];
       repeat' (any_goals (apply And.intro)); all_goals try (decide +kernel))))
  unless remaining.isEmpty do throwError "rcf: finite real-cell replay left unproved obligations"
  let accepted ← instantiateMVars candidate
  let accepted ← if indexed then do
    let same ← mkAppM ``FieldCells.checkIndex_eq
      #[signs,routing,quotedIndex,q(()),queryExpr,formulaExpr,radical,isolation,rows]
    mkEqTrans (← mkEqSymm same) accepted
  else pure accepted
  let header ← mkAppM ``FieldCells.signs_checked
    #[signs,q(()),queryExpr,formulaExpr,radical,isolation,rows,accepted]
  let specialization ← mkAppM ``FieldCells.specialize #[signs,header,valuesExpr]
  let rootArgs := rootExpr.getAppArgs
  let rep ← mkAppM ``Field.literalRep rootArgs
  let arity := mkApp (mkConst ``Fin) (mkNatLit n)
  let realValues ← withLocalDeclD `i arity fun i => do
    mkLambdaFVars #[i] (← mkAppM ``Field.value #[rep,mkApp valuesExpr i])
  let valuation ← withLocalDeclD `x q(ℝ) fun x => do
    mkLambdaFVars #[x] (← mkAppM ``RealFormula.append #[realValues,x])
  let law := match quantifier with
    | .forallReal => ``FieldCells.forall_formula
    | .existsReal => ``FieldCells.exists_formula
  let equivalence ← mkAppM law
    #[signs,q(()),queryExpr,formulaExpr,radical,isolation,rows,valuation,specialization,accepted]
  let verdictType := (← inferType equivalence).getAppArgs[0]!
  let verdict ← mkFreshExprMVar verdictType
  if indexed then
    let same ← mkAppM ``FieldQuery.cachedIndex_eq #[signs,routing,quotedIndex,header]
    let rewritten ← verdict.mvarId!.rewrite verdictType same (symm := true)
    unless rewritten.mvarIds.isEmpty do throwError "rcf: indexed fold left unresolved parameters"
    let decision ← mkFreshExprMVar rewritten.eNew
    let remaining ← Elab.runTactic' decision.mvarId! (← `(tactic| decide +kernel))
    unless remaining.isEmpty do throwError "rcf: indexed real-cell verdict did not check"
    verdict.mvarId!.assign (← mkEqMP (← mkEqSymm rewritten.eqProof) (← instantiateMVars decision))
  else
    let remaining ← Elab.runTactic' verdict.mvarId! (← `(tactic| decide +kernel))
    unless remaining.isEmpty do throwError "rcf: finite real-cell verdict did not check"
  let proof ← mkAppM ``Iff.mp #[equivalence,← instantiateMVars verdict]
  let expected ← withLocalDeclD `x q(ℝ) fun x => do
    let body ← mkAppM ``RealFormula.QF.toProp #[formulaExpr,mkApp valuation x]
    match quantifier with
    | .forallReal => mkForallFVars #[x] body
    | .existsReal => mkAppM ``Exists #[← mkLambdaFVars #[x] body]
  Hex.RCF.checkProof `Hex.RCF.RealCoefficients.FiniteLiteral.prove expected proof

end Hex.RCF.RealCoefficients.FiniteLiteral
