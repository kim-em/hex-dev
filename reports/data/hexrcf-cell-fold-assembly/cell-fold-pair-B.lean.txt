/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Radical
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Check
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients Schema Canonical
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

elab "#algebraic_cell_fold" : command => liftTermElabM do
  for (quantifier, verdict, name) in #[
      (``Hex.RealFormula.Quantifier.existsReal, true, `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Check.exists_run),
      (``Hex.RealFormula.Quantifier.forallReal, false, `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Check.forall_run)] do
    let run ← mkAppM ``CellReplay.Evidence.run #[Lean.mkConst ``evidence, Lean.mkConst quantifier]
    let rhs ← mkAppM ``Option.some #[toExpr verdict]
    let type ← mkEq run rhs
    let dictionary ← synthInstance (mkApp (mkConst ``Decidable) type)
    let reflexive ← mkEqRefl (mkConst ``Bool.true)
    let proof := mkAppN (mkConst ``of_decide_eq_true) #[type, dictionary, reflexive]
    KernelCheck.addChecked name type proof #[``Descriptor.ofReplay?] #[``CellReplay.Evidence.run]
#algebraic_cell_fold

theorem exists_checked : CellReplay.check values formula [] Canonical.cert roots evidence .existsReal = .ok true := by
  unfold CellReplay.check
  erw [Radical.checked, exists_run]
  rfl

theorem forall_false : CellReplay.check values formula [] Canonical.cert roots evidence .forallReal = .ok false := by
  unfold CellReplay.check
  erw [Radical.checked, forall_run]
  rfl

theorem source : ∃ x : ℝ, formula.toProp (RealFormula.append (fun i => original.value (values i)) x) :=
  CellReplay.check_sound original values formula [] Canonical.cert roots evidence .existsReal exists_checked
#print axioms source
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Check
