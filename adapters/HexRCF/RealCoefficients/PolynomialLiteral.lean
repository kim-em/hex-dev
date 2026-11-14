/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public meta import HexRCF.RealCoefficients.PolynomialSoundness
public meta import HexRCF.RealCoefficients.FieldLiteral
public meta import HexMvPoly.Ring
public meta section

namespace Hex.RCF.RealCoefficients.PolynomialLiteral
open Hex Lean Meta Hex.OrderedFn.Oracle
open Hex.RealFormula (QF Quantifier)

/-- Quote the existing sparse polynomial representation as ordinary terms. -/
meta def coefficientExpr {n : Nat} (p : PolynomialBounds.Poly n) : MetaM Expr := do
  let terms ← p.termsList.mapM fun (m, c) => do
    let monomial ← FieldLiteral.vectorLit (mkConst ``Nat) (m.map mkNatLit)
    let coefficient ← mkAppM ``mkRat #[mkIntLit c.num, mkNatLit c.den]
    mkAppM ``Prod.mk #[monomial, coefficient]
  let monomialTy ← mkAppM ``Mono #[mkNatLit n]
  let termTy ← mkAppM ``Prod #[monomialTy, mkConst ``Rat]
  let cmp ← mkAppOptM ``Mono.lex #[some (mkNatLit n)]
  let constructor ← mkAppOptM ``MvPoly.ofTerms #[some (mkNatLit n), some (mkConst ``Rat), some cmp]
  mkAppM' constructor #[← mkListLit termTy terms]

/-- Quote frozen numerical data; no producer is executed during replay. -/
meta def certificateExpr (formulaExpr : Expr) (formula : QF (n + 1))
    (cert : PolynomialBuild.Certificate n) : MetaM Expr := do
  let radical ← FieldLiteral.radicalExpr coefficientExpr cert.radical
  let isolation ← FieldLiteral.isolationExpr coefficientExpr cert.isolation
  let rows ← FieldLiteral.rowsExpr coefficientExpr formulaExpr formula.polys cert.rows
  let evidenceTy ← mkAppOptM ``TarskiCertificate
    #[some (mkConst ``Rat), some (mkConst ``Rat), some (mkConst ``Unit), none, none]
  let absent ← mkAppOptM ``Option.none #[some evidenceTy]
  let entries ← cert.entries.toList.mapM fun entry => do
    unless entry.evidence.isNone do throwError "rcf: polynomial sign entry has unrelated root evidence"
    mkAppM ``LiteralSign.Entry.mk #[← coefficientExpr entry.key, mkIntLit entry.value, absent]
  let ty ← mkAppM ``PolynomialBounds.Poly #[mkNatLit n]
  let entryTy ← mkAppM ``LiteralSign.Entry #[ty]
  mkAppM ``PolynomialBuild.Certificate.mk
    #[radical, isolation, rows, ← mkArrayLit entryTy entries, FieldLiteral.indexExpr cert.index]

private meta def runStrict (goal : MVarId) (code : Syntax) : MetaM (List MVarId) := do
  instantiateMVarDeclMVars goal
  let action : Elab.TermElabM (List MVarId) := Elab.Term.withSynthesize do
    Elab.Tactic.run goal <| Elab.Tactic.withoutRecover
      (Elab.Tactic.evalTactic code *> Elab.Tactic.pruneSolvedGoals)
  action.run' {} {}

private meta def prove (target : Expr) (script : Syntax) : MetaM Expr := do
  let candidate ← mkFreshExprMVar target
  let remaining ← runStrict candidate.mvarId! script
  unless remaining.isEmpty do throwError "rcf: polynomial certificate replay left unproved checks"
  Hex.RCF.checkProof `Hex.RCF.RealCoefficients.PolynomialLiteral target (← instantiateMVars candidate)

private meta def checkCore (bounds : Fin n → Bounds) (formula : QF (n + 1))
    (quantifier : Quantifier) (cert : PolynomialBuild.Certificate n)
    (boundsExpr valuationExpr containedExpr formulaExpr : Expr) : MetaM Expr := do
  unless PolynomialBuild.check bounds formula cert do
    throwError "rcf: polynomial certificate failed replay"
  match PolynomialBuild.run formula quantifier cert with
  | none => throwError "rcf: polynomial cell evaluation remains unresolved"
  | some false => throwError "rcf: real-coefficient statement is false"
  | some true => pure ()
  let literal ← instantiateMVars (← certificateExpr formulaExpr formula cert)
  if literal.hasMVar || literal.hasFVar then
    throwError "rcf: polynomial certificate data is not closed"
  let frozenName := mkPrivateName (← getEnv) (← mkFreshUserName `PolynomialData)
  let frozen ← mkAuxDefinitionFor frozenName literal (compile := false)
  enableRealizationsForConst frozenName
  setReducibilityStatus frozenName .reducible
  let test ← mkAppM ``PolynomialBuild.check #[boundsExpr, formulaExpr, frozen]
  let checkedTarget ← mkEq test (mkConst ``Bool.true)
  let frozenId := mkIdent frozenName
  let lemmas ← FieldLiteral.evidenceLemmas
  let checked ← prove checkedTarget (← `(tactic|
    (simp only [$frozenId:ident, PolynomialBuild.check, PolynomialSigns.check,
      QueryCells.check, QueryCells.checkRows, IsolationTransport.check,
      FieldRootSigns.Table.checkRows, $lemmas,*,Bool.and_eq_true];
      repeat' (any_goals (apply And.intro)); all_goals decide +kernel)))
  let quantifierExpr := mkConst (match quantifier with
    | .forallReal => ``Quantifier.forallReal | .existsReal => ``Quantifier.existsReal)
  let verdict ← mkAppM ``PolynomialBuild.run #[formulaExpr, quantifierExpr, frozen]
  let trueValue ← mkAppOptM ``Option.some #[some (mkConst ``Bool), some (mkConst ``Bool.true)]
  let folded ← prove (← mkEq verdict trueValue) (← `(tactic| decide +kernel))
  let proof ← mkAppM ``PolynomialBuild.check_sound
    #[boundsExpr, valuationExpr, containedExpr, formulaExpr, quantifierExpr, frozen, checked, folded]
  Hex.RCF.checkProof `Hex.RCF.RealCoefficients.PolynomialLiteral (← inferType proof) proof

/-- Check frozen evidence and emit an ordinary-kernel proof of the fixed shared
formula. Failure restores the complete state; success restores caller metavariables. -/
meta def check (bounds : Fin n → Bounds) (formula : QF (n + 1))
    (quantifier : Quantifier) (cert : PolynomialBuild.Certificate n)
    (boundsExpr valuationExpr containedExpr formulaExpr : Expr) : MetaM Expr := do
  let saved ← saveState
  let (result, _) ← tryFinally' (withNewMCtxDepth <| withOptions (fun options =>
      debug.skipKernelTC.set (Elab.async.set options false) false) do
      checkCore bounds formula quantifier cert boundsExpr valuationExpr containedExpr formulaExpr)
    (fun result => do
      match result with
      | none => saved.restore
      | some _ => modify fun state => {state with
          mctx := saved.meta.mctx, postponed := saved.meta.postponed
          zetaDeltaFVarIds := saved.meta.zetaDeltaFVarIds})
  return result

end Hex.RCF.RealCoefficients.PolynomialLiteral
