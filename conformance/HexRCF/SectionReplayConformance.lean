/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RealCoefficients.SectionReplay
import HexRCF.SelectedRoot.RowCollect
import HexRCF.SelectedRoot.Source
import HexRCF.SelectedRoot.RowTools
import HexRCF.SelectedRoot.Controls
import HexRCF.ProofEvidence
import HexRCF.Tactic

open Hex Hex.RealClosure Hex.SignDet Hex.RCF.RealCoefficients
open Hex.RCF.SelectedRootTests
open Hex.RCF.SelectedRootTests.Data Hex.RCF.SelectedRootTests.Upper
namespace Hex.RCF.RealCoefficients.SectionReplayConformance

def resultAt (facts : List (Algebraic.SignFact native))
    (coefficients : Fin 1 → parent.Value) (guards : List parent.Value)
    (formula : RealFormula.QF 2) (subject graph row : Codec.Json) : Except Replay.Error Bool :=
  SectionReplay.checkWith original (Algebraic.Element.signCodec base.codec facts)
    coefficients guards formula
    (Algebraic.Element.cachedOne reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd reduction reduction_eq facts)
    (Algebraic.Element.cachedNeg reduction reduction_eq facts)
    (Algebraic.Element.cachedSub reduction reduction_eq facts)
    (Algebraic.Element.cachedMul reduction reduction_eq facts)
    (Algebraic.Element.cachedInv reduction reduction_eq facts)
    (Algebraic.Element.cachedDiv reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedOne_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedAdd_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedNeg_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedSub_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedMul_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedInv_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedDiv_eq reduction reduction_eq facts)
    (by exact Algebraic.Element.cachedNatCast_eq reduction reduction_eq facts)
    subject graph row

def result (facts : List (Algebraic.SignFact native)) : Except Replay.Error Bool :=
  resultAt facts values [] schema Literals.upperSubject Literals.upperGraph Literals.rowPacket

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
elab "#section_check" : command => liftTermElabM do
  let mut rules ← RowTools.rules
  for name in #[``program, ``result, ``resultAt, ``SectionReplay.checkWith, ``SectionReplay.rowCodec,
      ``Algebraic.RootReplay.readContext, ``Algebraic.Context.changeOps] do
    rules ← rules.addDeclToUnfold name
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let collected ← Algebraic.KernelReplay.collectMany 0 (mkConst ``program)
    #[⟨mkConst ``RowCollect.facts⟩] context (fun _ _ => pure none)
  match collected.outcome with
  | .checked true proof axioms =>
    let type ← mkEq (mkApp (mkConst ``program) (mkConst ``RowCollect.facts))
      (mkConst ``Bool.true)
    KernelCheck.addChecked `Hex.RCF.RealCoefficients.SectionReplayConformance.accepted type proof
    logInfo m!"frozen section true; requests={collected.requests.size}; axioms={axioms}"
  | .checked false .. => throwError "frozen section rejected"
  | .missing application => throwError "frozen section needs a recorded fact: {application}"

set_option maxRecDepth 32768 in
set_option maxHeartbeats 12000000 in
#section_check

theorem checked : SectionReplay.check original
    (Algebraic.Element.signCodec base.codec RowCollect.facts) values [] schema
    Literals.upperSubject Literals.upperGraph Literals.rowPacket = .ok true := by
  have checked := program_ok RowCollect.facts accepted
  unfold result resultAt at checked
  erw [SectionReplay.checkWith_eq] at checked
  exact checked

theorem source : ∃ x : ℝ, x^2 = Real.sqrt 2 ∧ 1 < x ∧ x < 2 := by
  obtain ⟨x, truth⟩ := SectionReplay.check_sound original _ values [] schema
    Literals.upperSubject Literals.upperGraph Literals.rowPacket checked
  exact ⟨x, (Source.schema_real x).mp truth⟩

#print axioms source

open Lean Meta Elab Command in
elab "#section_control " name:ident " := " term:term : command => liftTermElabM do
  let proposition ← Term.elabTerm term (some (mkSort .zero))
  Term.synthesizeSyntheticMVarsNoPostponing
  let proposition ← instantiateMVars proposition
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let decision := mkAppN (mkConst ``Decidable.decide) #[proposition, dictionary]
  let mut rules ← RowTools.rules
  for law in #[``resultAt, ``SectionReplay.checkWith, ``SectionReplay.rowCodec,
      ``Algebraic.RootReplay.readContext, ``Algebraic.Context.changeOps] do
    rules ← rules.addDeclToUnfold law
  let context ← Simp.mkContext (simpTheorems := #[rules])
    (congrTheorems := ← getSimpCongrTheorems)
  let (outcome, _) ← Algebraic.KernelReplay.assemble decision context
  match outcome with
  | .checked true proof _ =>
    let conclusion := mkAppN (mkConst ``of_decide_eq_true) #[proposition, dictionary, proof]
    KernelCheck.addChecked name.getId proposition conclusion
  | .checked false .. => throwError "section control failed"
  | .missing application => throwError "section control demands evidence: {application}"

set_option maxRecDepth 32768
set_option maxHeartbeats 16000000

#section_control Hex.RCF.RealCoefficients.SectionReplayConformance.badSubject :=
  resultAt RowCollect.facts values [] schema .null Literals.upperGraph Literals.rowPacket =
    .error .evidence
#section_control Hex.RCF.RealCoefficients.SectionReplayConformance.badGraph :=
  resultAt RowCollect.facts values [] schema Literals.upperSubject .null Literals.rowPacket =
    .error .evidence
#section_control Hex.RCF.RealCoefficients.SectionReplayConformance.badRow :=
  resultAt RowCollect.facts values [] schema Literals.upperSubject Literals.upperGraph .null =
    .error .evidence
#section_control Hex.RCF.RealCoefficients.SectionReplayConformance.zeroFirst :=
  resultAt RowCollect.facts values [0] schema .null .null .null = .error .divisor
#section_control Hex.RCF.RealCoefficients.SectionReplayConformance.falseRow :=
  resultAt RowCollect.facts values [] Controls.falseSchema Literals.upperSubject
    Literals.upperGraph Literals.rowPacket = .ok false
#section_control Hex.RCF.RealCoefficients.SectionReplayConformance.wrongCoefficient :=
  resultAt RowCollect.facts (fun _ => Controls.negative) [] schema Literals.upperSubject
    Literals.upperGraph Literals.rowPacket = .error .evidence

run_meta do
  for name in #[``source, ``checked, ``program_ok, ``SectionReplay.checkWith_eq,
      ``SectionReplay.check_fields, ``SectionReplay.check_domains, ``SectionReplay.check_sound,
      ``SectionReplay.check_false, ``SectionReplay.check_zero, ``badSubject, ``badGraph,
      ``badRow, ``zeroFirst, ``falseRow, ``wrongCoefficient] do
    let proof := Lean.mkConst name
    let _ ← Hex.RCF.checkProof name (← Lean.Meta.inferType proof) proof
    let axioms ← Lean.collectAxioms name
    unless axioms.size == 3 && axioms.all
        (fun a => [``propext, ``Classical.choice, ``Quot.sound].contains a) do
      Lean.throwError "section theorem has an unexpected complete inventory: {name}"
  unless ← Hex.RCF.ProofEvidence.contains ``source
      (fun e => e.isConstOf ``SectionReplay.check_sound) do
    Lean.throwError "section source omitted frozen soundness"

end Hex.RCF.RealCoefficients.SectionReplayConformance
