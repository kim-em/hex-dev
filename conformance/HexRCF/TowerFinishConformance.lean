/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.CompleteQuote
import HexRCF.RealCoefficients.TowerCompile

open Lean Meta Qq Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.RealCoefficients.CellReplayTests.Algebraic

namespace Hex.RCF.TowerFinishConformance
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

/-- Align a compiled stored representative with the fixture's existing one
using their ordinary-real interpretation, not literal equality of raw values. -/
private meta def align (stored : Expr) (term : TowerCompile.Term) :
    Hex.RealFormula.Reify.ReifyM Expr := do
  let model := mkConst ``Schema.original
  let left ← mkAppM ``Tower.Model.value #[model,stored]
  let kind ← whnf (← inferType term.proof)
  let original := kind.getAppArgs[2]!
  let atom ← mkAppM ``Tower.Model.value #[model,mkConst ``Hex.RCF.SelectedRootTests.Data.alpha]
  let relative := original.replace fun expression =>
    if expression == q(Real.sqrt 2) then some atom else none
  let interpreted ← TowerCompile.compile model (fun expression => do
    if expression != atom then return none
    return some ⟨mkConst ``Hex.RCF.SelectedRootTests.Data.alpha,← mkEqRefl atom⟩) relative
  unless interpreted.expression == term.expression do
    throwError "relative interpretation changed the compiled representative"
  let target ← mkEq left relative
  Hex.RealFormula.Reify.accountProof target
  let hole ← mkFreshExprMVar target
  let goals ← Elab.runTactic' hole.mvarId! (← `(tactic| (
    simp only [Schema.values, Guards.negativeOne_value]
    norm_num <;> ring)))
  unless goals.isEmpty do
    throwError "compiled representative alignment left goals: {← ppExpr (← goals[0]!.getType)}"
  let candidate ← instantiateMVars hole
  Hex.RealFormula.Reify.accountProof candidate
  let equality ← Hex.RCF.checkProof `compiledCoordinate target candidate
  let result ← mkEqTrans equality (← mkEqTrans (← mkEqSymm interpreted.proof) term.proof)
  Hex.RealFormula.Reify.accountProof result
  pure result

run_meta do
  let target : Q(Prop) := q(∃ x : ℝ,
    x^2 - ((Real.sqrt 2 + 1) - 1) ≥ 0 ∧
    x^2 - ((Real.sqrt 2 + 1) - 1) ≤ 0 ∧
    0 / ((-1 : ℝ) + 0) = 0)
  let .ok source ← Reify.prepare target
    | throwError "compound original source did not prepare"
  unless source.coefficients.size == 1 && source.divisors.size == 1 do
    throwError "compound original source changed its coefficient or divisor inventory"
  let .ok result ← RootQuote.runWith (do
      let (coefficients,divisors) ← TowerCompile.prepareWith source
        (mkConst ``Schema.original) fun expression => do
          if expression != q(Real.sqrt 2) then return none
          return some ⟨mkConst ``Hex.RCF.SelectedRootTests.Data.alpha,
            mkConst ``Hex.RCF.SelectedRootTests.Data.alpha_value⟩
      let some compiled := coefficients[0]? | throwError "missing compound coefficient"
      let some originalDivisor := divisors[0]? | throwError "missing original divisor"
      let coefficient ← align q(Schema.values 0) compiled
      let divisor ← align (mkConst ``Guards.negativeOne) originalDivisor
      let valuation ← CellQuote.valuationWith source (mkConst ``Schema.original)
        (mkConst ``Schema.values) #[coefficient]
      let checker := q(CompleteReplay.check Schema.parent.codec Schema.values Schema.formula
        [Guards.negativeOne] Canonical.cert .existsReal CompleteQuote.rootGraph CompleteQuote.cells)
      let before := (← (← getEnv).getLocalConstantInfos).map (·.name)
      let completed ← CellQuote.finishPacketWith source target checker
        (mkConst ``CompleteQuote.guarded_checked) (mkConst ``Schema.original) valuation #[divisor]
      -- Retain the actual preflight conclusion even though total real division
      -- means the final source theorem need not depend on this separate proof.
      let expected ← mkAppM ``Ne #[source.divisors[0]!,q((0 : ℝ))]
      let mut domains : Array Expr := #[]
      for info in (← (← getEnv).getLocalConstantInfos) do
        if before.contains info.name then continue
        let .thmInfo declaration ← getConstInfo info.name | continue
        if ← isDefEq declaration.type expected then domains := domains.push (mkConst info.name)
      unless domains.size == 1 do
        throwError "source finishing emitted {domains.size} original-divisor proofs; expected one"
      let domainProof := domains[0]!
      addDecl (.thmDecl {
        name := `Hex.RCF.TowerFinishConformance.domain,
        levelParams := [],type := expected,value := domainProof})
      pure completed) {} source.usage
    | throwError "compound source finishing refused"
  let proof ← Hex.RCF.checkProof `compoundOriginal target result.proof
  addDecl (.thmDecl {name := `Hex.RCF.TowerFinishConformance.source,levelParams := [],type := target,value := proof})
  logInfo m!"compiled compound coefficient and original divisor finished: proofNodes={result.usage.proofNodes}"

end Hex.RCF.TowerFinishConformance
