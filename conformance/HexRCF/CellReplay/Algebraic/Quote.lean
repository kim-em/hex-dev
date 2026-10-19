/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Check
import HexRCF.RealCoefficients.CellQuote
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Quote
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients Schema Canonical
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
elab "#algebraic_original_quote" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let source ← match ← Reify.prepare target with
    | .error error => throwError "{Hex.RealFormula.Reify.Error.toMessageData error}"
    | .ok source => pure source
  let valuation ← elabTerm (← `(fun i : Fin 1 => original.value (values i))) none
  synthesizeSyntheticMVarsNoPostponing
  let valuation ← instantiateMVars valuation
  let expected ← mkEq valuation source.valuation
  let identity ← elabTermEnsuringType (← `(by funext i; fin_cases i; exact Schema.coefficient)) expected
  let checker ← elabTerm (← `(CellReplay.check values formula [] Canonical.cert roots evidence .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  let proof ← CellQuote.finish target (← instantiateMVars checker)
    (Lean.mkConst ``Check.exists_checked) (Lean.mkConst ``original) (← instantiateMVars identity)
  let proof ← Hex.RCF.checkProof `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Quote.source target proof
  addDecl (.thmDecl {name := `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Quote.source, levelParams := [], type := target, value := proof})
#algebraic_original_quote
#print axioms source
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Quote
