/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Check
import HexRCF.CellReplay.ZeroLiterals
import HexRCF.RealCoefficients.CellQuote
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open RootReplayConformance Hex.RCF.RealCoefficients.CellReplayTests.Schema
open Lean Meta Elab Command Term
namespace Hex.RCF.RealCoefficients.CellReplayTests.Zero
set_option maxHeartbeats 12000000
set_option maxRecDepth 32768
def matrix : RealFormula.QF 1 := .atom ⟨0, .eq⟩
def radical : RadicalCert Data.base.Value Signature := ⟨Data.base.signature, 1, 1, 1, 0⟩
def packet : Codec.Json := .arr #[ZeroLiterals.sections, ZeroLiterals.sectors]
def restored := CellRead.read Data.base.codec [] constantResult values matrix packet
#root_check restored.toOption.isSome = true => accepted
def rows := restored.toOption.get accepted
#root_check CellReplay.check values matrix [] radical constantResult rows .forallReal = .ok true => all_checked
#root_check CellReplay.check values matrix [] radical constantResult rows .existsReal = .ok true => exists_checked
def falseMatrix : RealFormula.QF 1 := .atom ⟨0, .gt⟩
def falseRows : CellReplay.Evidence constantResult values falseMatrix :=
  ⟨rows.sections, rows.sectors, fun cut =>
    ⟨(rows.sectorRows cut).root, (rows.sectorRows cut).bound, (rows.sectorRows cut).signs⟩⟩
#root_check CellReplay.check values falseMatrix [] radical constantResult falseRows .forallReal = .ok false => all_false
#root_check CellReplay.check values falseMatrix [] radical constantResult falseRows .existsReal = .ok false => exists_false
#root_check CellReplay.check values matrix [0] radical constantResult rows .forallReal = .error .divisor => zero_guard
#root_check (match CellRead.read Data.base.codec [0] constantResult values matrix Codec.Json.Value.null
  with | .error .divisor => true | _ => false) = true => guard_before_constant
theorem specialized : ∀ x : ℝ, matrix.toProp (RealFormula.append (fun i => Data.rational.value (values i)) x) :=
  CellReplay.check_sound Data.rational values matrix [] radical constantResult rows .forallReal all_checked

elab "#cell_zero_quote" : command => liftTermElabM do
  let target ← elabType (← `(∀ _x : ℝ, (0 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let .ok prepared ← Reify.prepare target | throwError "expected constant source recognition"
  let valuation ← elabTerm (← `(fun i : Fin 0 => Data.rational.value (values i))) none
  synthesizeSyntheticMVarsNoPostponing
  let expected ← mkEq (← instantiateMVars valuation) prepared.valuation
  let identity ← elabTermEnsuringType (← `(by funext i; exact Fin.elim0 i)) expected
  let checker ← elabTerm (← `(CellReplay.check values matrix [] radical constantResult rows .forallReal)) none
  synthesizeSyntheticMVarsNoPostponing
  let proof ← CellQuote.finish target (← instantiateMVars checker) (Lean.mkConst ``all_checked)
    (Lean.mkConst ``Data.rational) (← instantiateMVars identity)
  addDecl (.thmDecl {
    name := `Hex.RCF.RealCoefficients.CellReplayTests.Zero.source
    levelParams := []
    type := target
    value := proof })
#cell_zero_quote
end Hex.RCF.RealCoefficients.CellReplayTests.Zero
