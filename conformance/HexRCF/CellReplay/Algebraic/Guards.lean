/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.CellReplay.Algebraic.Quote
namespace Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Guards
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.RealCoefficients
open Schema Canonical
open Lean Meta Elab Command Term
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

def negativeOne : parent.Value :=
  (Algebraic.Element.cachedNeg Data.reduction Data.reduction_eq facts).neg
    (Algebraic.Element.cachedOne Data.reduction Data.reduction_eq facts).one

theorem negativeOne_eq : negativeOne = (-1 : parent.Value) :=
  congrArg₂ (fun (neg : Neg parent.Value) (one : One parent.Value) =>
    @Neg.neg parent.Value neg (@One.one parent.Value one))
    (Algebraic.Element.cachedNeg_eq Data.reduction Data.reduction_eq facts)
    (Algebraic.Element.cachedOne_eq Data.reduction Data.reduction_eq facts)

theorem negativeOne_value : original.value negativeOne = (-1 : ℝ) := by
  erw [negativeOne_eq, original.neg, original.one]

theorem nonzero : negativeOne ≠ 0 := by
  intro h
  have zero : original.value (0 : parent.Value) = 0 := (original.zero_iff 0).mpr rfl
  have impossible : (-1 : ℝ) = 0 := negativeOne_value.symm.trans ((congrArg original.value h).trans zero)
  norm_num at impossible

theorem accepted : CellReplay.check values formula [negativeOne] cert roots evidence .existsReal = .ok true := by
  have guard : (([negativeOne] : List parent.Value).all fun d => Decidable.decide (d ≠ 0)) = true := by
    simp only [List.all_cons, List.all_nil, Bool.and_true]
    exact _root_.decide_eq_true nonzero
  unfold CellReplay.check
  erw [guard, Radical.checked, Check.exists_run]
  rfl

theorem zero_refused : CellReplay.check values formula [0] cert roots evidence .existsReal = .error .divisor := by rfl

theorem zero_before_decode :
    (CellRead.read (Algebraic.Element.signCodec Data.base.codec facts) [0] roots values formula
      Codec.Json.Value.null).map (fun _ => ()) = .error .divisor := by rfl

elab "#algebraic_guarded_quote" : command => liftTermElabM do
  let target ← elabType (← `(∃ x : ℝ, x ^ 2 - Real.sqrt 2 ≥ 0 ∧ x ^ 2 - Real.sqrt 2 ≤ 0 ∧ 0 / (-1 : ℝ) = 0))
  synthesizeSyntheticMVarsNoPostponing
  let target ← instantiateMVars target
  let source ← match ← Reify.prepare target with
    | .error error => throwError "{Hex.RealFormula.Reify.Error.toMessageData error}"
    | .ok source => pure source
  let valuation ← elabTerm (← `(fun i : Fin 1 => original.value (values i))) none
  synthesizeSyntheticMVarsNoPostponing
  let valuation ← instantiateMVars valuation
  let identity ← elabTermEnsuringType (← `(by funext i; fin_cases i; exact Schema.coefficient))
    (← mkEq valuation source.valuation)
  let checker ← elabTerm (← `(CellReplay.check values formula [negativeOne] cert roots evidence .existsReal)) none
  synthesizeSyntheticMVarsNoPostponing
  let proof ← CellQuote.finish target (← instantiateMVars checker) (Lean.mkConst ``accepted)
    (Lean.mkConst ``original) (← instantiateMVars identity) #[Lean.mkConst ``negativeOne_value]
  let proof ← Hex.RCF.checkProof `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Guards.source target proof
  addDecl (.thmDecl { name := `Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Guards.source, levelParams := [], type := target, value := proof })
#algebraic_guarded_quote
#print axioms source
end Hex.RCF.RealCoefficients.CellReplayTests.Algebraic.Guards
