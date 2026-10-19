/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Ordinary
import HexRCF.RealCoefficients.CellQuote
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open RootReplayConformance Hex.RCF.RealCoefficients.CellReplayTests.Schema Hex.RCF.RealCoefficients.CellReplayTests.Check
open Lean Meta Elab Command Term
namespace Hex.RCF.RealCoefficients.CellReplayTests.Quote
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

meta def prove (target : Expr) (accepted : Expr := mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.exists_checked)
    (checkerOverride : Option Expr := none) (guardIdentities : Array Expr := #[]) : TermElabM Expr := do
  let source ← match ← Reify.prepare target with
    | .error error => throwError "{Hex.RealFormula.Reify.Error.toMessageData error}"
    | .ok source => pure source
  let valuation ← elabTerm (← `(fun i : Fin 0 => Data.rational.value (values i))) none
  synthesizeSyntheticMVarsNoPostponing
  let valuation ← instantiateMVars valuation
  let expected ← mkEq valuation source.valuation
  let identity ← elabTermEnsuringType (← `(by funext i; exact Fin.elim0 i)) expected
  let checker ← match checkerOverride with
    | some checker => pure checker
    | none => elabTerm (← `(CellReplay.check values formula [] cert wholeResult evidence .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  CellQuote.finish target (← instantiateMVars checker) accepted (mkConst ``Data.rational)
    (← instantiateMVars identity) guardIdentities

elab "#cell_source_quote" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - 2 ≥ 0 ∧ x ^ 2 - 2 ≤ 0 ∧ (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let proof ← prove target
  let proof ← Hex.RCF.checkProof `Hex.RCF.RealCoefficients.CellReplayTests.Quote.original target proof
  addDecl (.thmDecl { name := `Hex.RCF.RealCoefficients.CellReplayTests.Quote.original, levelParams := [], type := target, value := proof })
#cell_source_quote
#print axioms original
end Hex.RCF.RealCoefficients.CellReplayTests.Quote

namespace Hex.RCF.RealCoefficients.CellReplayTests.Quote
elab "#cell_universal_quote" : command => liftTermElabM do
  let target ← elabType (← `(∀ x : ℝ, (x ^ 2 - 2 ≥ 0 ∧ x ^ 2 - 2 ≤ 0 ∧ (0 : ℝ) = 0) ∨ True))
  let checker ← elabTerm (← `(CellReplay.check values trueMatrix [] cert wholeResult trueEvidence .forallReal)) none
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let checker ← instantiateMVars checker
  let proof ← prove target (Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.forall_checked) (some checker)
  let proof ← Hex.RCF.checkProof `Hex.RCF.RealCoefficients.CellReplayTests.Quote.universal target proof
  addDecl (.thmDecl { name := `Hex.RCF.RealCoefficients.CellReplayTests.Quote.universal, levelParams := [], type := target, value := proof })
#cell_universal_quote
#print axioms universal
end Hex.RCF.RealCoefficients.CellReplayTests.Quote

namespace Hex.RCF.RealCoefficients.CellReplayTests.Quote
elab "#cell_guarded_quote" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - 2 ≥ 0 ∧ x ^ 2 - 2 ≤ 0 ∧ 0 / (-1 : ℝ) = 0))
  let checker ← elabTerm (← `(CellReplay.check values formula [-1] cert wholeResult evidence .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let checker ← instantiateMVars checker
  let proof ← prove target (Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.guarded_checked) (some checker)
    #[Lean.mkConst ``Hex.RCF.RealCoefficients.CellReplayTests.Check.negative_guard]
  let proof ← Hex.RCF.checkProof `Hex.RCF.RealCoefficients.CellReplayTests.Quote.guarded target proof
  addDecl (.thmDecl { name := `Hex.RCF.RealCoefficients.CellReplayTests.Quote.guarded, levelParams := [], type := target, value := proof })
#cell_guarded_quote
#print axioms guarded
end Hex.RCF.RealCoefficients.CellReplayTests.Quote
