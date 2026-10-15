/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Boolean
import HexRCF.RealCoefficients.CellQuote
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanSources
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.RealFormula
open Hex.RCF.RealCoefficients
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic
open Lean Meta Elab Command Term
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

elab "#boolean_source_quotes" : command => liftTermElabM do
  let goals := #[
    (← `(∀ x : ℝ, (x ^ 2 - Real.sqrt 2 < 0 ∨ x ^ 2 - Real.sqrt 2 ≥ 0) ∧ (0 : ℝ) = 0)),
    (← `(∀ x : ℝ, (x ^ 2 - Real.sqrt 2 = 0 ∨ x ^ 2 - Real.sqrt 2 ≠ 0) ∧ (0 : ℝ) = 0)),
    (← `(∃ x : ℝ, (x ^ 2 - Real.sqrt 2 > 0 ∧ x ^ 2 - Real.sqrt 2 ≠ 0) ∧ (0 : ℝ) = 0)),
    (← `(∃ x : ℝ, (x ^ 2 - Real.sqrt 2 ≤ 0 ∧ x ^ 2 - Real.sqrt 2 ≠ 0) ∧ (0 : ℝ) = 0))]
  for i in [:goals.size] do
    let suffix := #["lt_or_ge", "eq_or_ne", "positive", "negative"][i]!
    let args : Array (Array Expr) := #[
      #[mkConst ``RealFormula.Cmp.lt,mkConst ``RealFormula.Cmp.ge,toExpr true,toExpr false],
      #[mkConst ``RealFormula.Cmp.eq,mkConst ``RealFormula.Cmp.ne,toExpr true,toExpr false],
      #[mkConst ``RealFormula.Cmp.gt,mkConst ``RealFormula.Cmp.ne,toExpr false,toExpr false],
      #[mkConst ``RealFormula.Cmp.le,mkConst ``RealFormula.Cmp.ne,toExpr false,toExpr false]]
    let formula := mkAppN (mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean.matrix) args[i]!
    let data := mkAppN (mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean.evidence) args[i]!
    let quantifier := Lean.mkConst (if i < 2 then ``Quantifier.forallReal else ``Quantifier.existsReal)
    let checker ← mkAppM ``CellReplay.check #[mkConst ``Schema.values,formula,
      ← elabTerm (← `(([] : List Schema.parent.Value))) none,
      mkConst ``Canonical.cert,mkConst ``Canonical.roots,data,quantifier]
    let acceptedType ← mkEq checker (← mkAppOptM ``Except.ok #[some (Lean.mkConst ``Replay.Error), some (Lean.mkConst ``Bool), some (toExpr true)])
    let candidate ← mkFreshExprMVar acceptedType
    let folded : TSyntax `term := ⟨(mkIdent (Name.str `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Boolean suffix)).raw⟩
    let rule ← `(Lean.Parser.Tactic.rwRule| $folded:term)
    let rest ← Lean.Elab.runTactic' candidate.mvarId!
      (← `(tactic| unfold CellReplay.check; erw [Radical.checked, $rule:rwRule]; rfl))
    unless rest.isEmpty do throwError "Boolean checker acceptance did not close"
    let accepted ← instantiateMVars candidate
    let target ← elabType goals[i]!
    synthesizeSyntheticMVarsNoPostponing
    let target ← instantiateMVars target
    let source ← match ← Reify.prepare target with
      | .error e => throwError "{Hex.RealFormula.Reify.Error.toMessageData e}"
      | .ok source => pure source
    let valuation ← elabTerm (← `(fun j : Fin 1 => Schema.original.value (Schema.values j))) none
    synthesizeSyntheticMVarsNoPostponing
    let valuation ← instantiateMVars valuation
    let identity ← elabTermEnsuringType (← `(by funext j; fin_cases j; exact Schema.coefficient))
      (← mkEq valuation source.valuation)
    synthesizeSyntheticMVarsNoPostponing
    let proof ← CellQuote.finish target (← instantiateMVars checker) (← instantiateMVars accepted)
      (mkConst ``Schema.original) (← instantiateMVars identity)
    let name := Name.str `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanSources suffix
    let proof ← Hex.RCF.checkProof name target proof
    addDecl (.thmDecl {name,levelParams:=[],type:=target,value:=proof})
    let axioms ← collectAxioms name
    unless axioms.size == 3 && axioms.all (fun a => #[``propext,``Classical.choice,``Quot.sound].contains a) do
      throwError "unexpected source axioms"
    logInfo m!"fresh Boolean original source {suffix} checked with standard three axioms"
#boolean_source_quotes
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.BooleanSources
