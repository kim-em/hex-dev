/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
import HexRCF.RealCoefficients.PointReplay
import HexRCF.SelectedRoot.RowCollect
import HexRCF.SelectedRoot.RowTools
import HexRCF.SelectedRoot.Upper
open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
namespace Hex.RCF.RealCoefficients.PointReplayConformance

def formula : RealFormula.QF 2 := .atom ⟨
  RealFormula.Poly.project (#v[some (1 : Fin 2), some (0 : Fin 2)]).get
    (Reflect.ofIntTerms id [(#v[1, 0], 1), (#v[0, 1], -1)]), .eq⟩
def subject : Codec.Json := .arr #[Codec.poly base.codec coordinate, Codec.Json.of (1 : Int)]
def resultAt (facts : List (Algebraic.SignFact native))
    (guards : List parent.Value) (matrix : RealFormula.QF 2) : Except Replay.Error Bool :=
  PointReplay.checkWith (Algebraic.Element.signCodec base.codec facts) values guards matrix
    (Algebraic.Element.cachedOne reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd reduction reduction_eq facts)
    (Algebraic.Element.cachedMul reduction reduction_eq facts)
    (Algebraic.Element.cachedNeg reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedOne_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedAdd_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedMul_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedNeg_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedNatCast_eq reduction reduction_eq facts) subject

def result (facts : List (Algebraic.SignFact native)) : Except Replay.Error Bool :=
  resultAt facts [] formula

def negative : RealFormula.QF 2 := .atom ⟨
  RealFormula.Poly.project (#v[some (1 : Fin 2), some (0 : Fin 2)]).get
    (Reflect.ofIntTerms id [(#v[1, 0], 1), (#v[0, 1], -1)]), .lt⟩

def test (guards : List parent.Value) (matrix : RealFormula.QF 2) (expected : Bool)
    (facts : List (Algebraic.SignFact native)) : Bool :=
  match resultAt facts guards matrix with
  | .ok value => Decidable.decide (value = expected)
  | _ => false

theorem test_ok (guards : List parent.Value) (matrix : RealFormula.QF 2) (expected : Bool)
    (facts : List (Algebraic.SignFact native)) (accepted : test guards matrix expected facts = true) :
    resultAt facts guards matrix = .ok expected := by
  unfold test at accepted
  cases h : resultAt facts guards matrix with
  | error e => simp only [h, Bool.false_eq_true] at accepted
  | ok b => cases b <;> cases expected <;> simp_all

def falseProgram := test [] negative false
def guardProgram := test [alpha] formula true

def program (facts : List (Algebraic.SignFact native)) : Bool :=
  match result facts with
  | .ok true => true
  | _ => false

theorem program_ok (facts : List (Algebraic.SignFact native))
    (accepted : program facts = true) : result facts = .ok true := by
  unfold program at accepted
  cases h : result facts with
  | error e => simp only [h, Bool.false_eq_true] at accepted
  | ok b => cases b <;> simp_all

open Lean Meta Elab Command in
elab "#point_check" acceptance:ident program:ident : command => liftTermElabM do
  let programName ← Lean.Elab.realizeGlobalConstNoOverloadWithInfo program
  let acceptanceName := (← getCurrNamespace) ++ acceptance.getId
  let mut rules ← RowTools.rules
  for name in #[programName, ``test, ``result, ``resultAt, ``PointReplay.checkWith, ``PointReplay.rowWith,
      ``PointReplay.signs] do
    rules ← rules.addDeclToUnfold name
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let collected ← Algebraic.KernelReplay.collectMany 0 (mkConst programName)
    #[⟨mkConst ``RowCollect.facts⟩] context (fun _ _ => pure none)
  match collected.outcome with
  | .checked true proof axioms =>
    let type ← mkEq (mkApp (mkConst programName) (mkConst ``RowCollect.facts))
      (mkConst ``Bool.true)
    KernelCheck.addChecked acceptanceName type proof
    logInfo m!"frozen point true; requests={collected.requests.size}; axioms={axioms}"
  | .checked false .. => throwError "frozen point rejected"
  | .missing application => throwError "frozen point needs a recorded fact: {application}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
#point_check accepted program

theorem checked : PointReplay.check
    (Algebraic.Element.signCodec base.codec RowCollect.facts) values [] formula subject = .ok true := by
  have checked := program_ok RowCollect.facts accepted
  unfold result resultAt at checked
  erw [PointReplay.checkWith_eq] at checked
  exact checked

theorem witness : ∃ x : ℝ, formula.toProp (Samples.valuation original values x) :=
  PointReplay.check_sound original _ values [] formula subject checked

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
#point_check falseAccepted falseProgram

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
#point_check guardAccepted guardProgram

theorem false_checked : PointReplay.check
    (Algebraic.Element.signCodec base.codec RowCollect.facts) values [] negative subject = .ok false := by
  have h := test_ok [] negative false RowCollect.facts falseAccepted
  unfold resultAt at h
  erw [PointReplay.checkWith_eq] at h
  exact h

theorem counterexample : ¬ ∀ x : ℝ, negative.toProp (Samples.valuation original values x) :=
  PointReplay.check_false original _ values [] negative subject false_checked

theorem guard_checked : PointReplay.check
    (Algebraic.Element.signCodec base.codec RowCollect.facts) values [alpha] formula subject = .ok true := by
  have h := test_ok [alpha] formula true RowCollect.facts guardAccepted
  unfold resultAt at h
  erw [PointReplay.checkWith_eq] at h
  exact h

theorem domains : ∀ d ∈ [alpha], original.value d ≠ 0 :=
  PointReplay.check_domains original _ values [alpha] formula subject true guard_checked

#print axioms counterexample
#print axioms domains

theorem zero_before_malformed : PointReplay.check
    (Algebraic.Element.signCodec base.codec RowCollect.facts) values [0] formula
    .null = .error .divisor :=
  PointReplay.check_zero _ values [0] formula .null (by simp)

set_option maxRecDepth 32768 in
theorem missing_literal : PointReplay.check
    (Algebraic.Element.signCodec base.codec ([] : List (Algebraic.SignFact native)))
    values [] formula subject = .error .evidence := by
  decide +kernel

theorem false_point : PointReplay.check
    (Algebraic.Element.signCodec base.codec RowCollect.facts) values [] .ff subject = .ok false := by
  obtain ⟨sample, parsed, _, _⟩ := PointReplay.check_fields _ values [] formula subject true checked
  simp [PointReplay.check, parsed, PointReplay.row, PointReplay.signs,
    RepresentationSpecialize.prepare, Samples.Row.eval, RealFormula.QF.polys,
    RealFormula.QF.evalSigns]

#print axioms zero_before_malformed
#print axioms missing_literal
#print axioms false_point


#print axioms witness
run_meta do
  for name in #[``zero_before_malformed, ``missing_literal, ``false_point, ``witness,
      ``false_checked, ``counterexample, ``guard_checked, ``domains] do
    let axioms ← Lean.collectAxioms name
    unless axioms.all (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "point control has a forbidden axiom"
end Hex.RCF.RealCoefficients.PointReplayConformance
