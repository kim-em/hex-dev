/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexRCF.RootTransportData
import HexRCF.RootTransportLiterals
import HexRCF.SelectedRoot.Data
import HexRCF.SelectedRoot.KernelCheck
import Lean.Elab.Command
import HexRCF.ProofEvidence
import HexRCF.RealCoefficients.ScalarPacket
open Hex Hex.RealClosure Hex.RealClosure.Tower Hex.SignDet
open Hex.RCF.SelectedRootTests Hex.RCF.SelectedRootTests.Data
namespace Hex.RCF.RealCoefficients.RootTransportConformance
def constant (a : base.Value) : Algebraic.SignFact native :=
  ⟨DensePoly.C a, base.sign a, by
    rw [Algebraic.Context.signPoly_const native (DensePoly.C a)
      (DensePoly.size_ofCoeffs_le #[a]), DensePoly.coeff_C]
    rfl⟩
def seeds : List (Algebraic.SignFact native) :=
  [constant (-2), constant 1, constant 2]
def readAt (facts : List (Algebraic.SignFact native)) (guards : List base.Value)
    (subject graph : Codec.Json) :=
  RootTransport.readWith RootTransportData.conversion lower
    (Algebraic.Element.signCodec base.codec facts)
    (RootTransportData.mapped facts) (RootTransportData.mapped_eq facts)
    (Algebraic.Element.cachedOne reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd reduction reduction_eq facts)
    (Algebraic.Element.cachedSub reduction reduction_eq facts)
    (Algebraic.Element.cachedMul reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast reduction reduction_eq facts)
    (Algebraic.Element.cachedOne_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedAdd_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedSub_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedMul_eq reduction reduction_eq facts)
    (Algebraic.Element.cachedNatCast_eq reduction reduction_eq facts)
    guards subject graph
def resultAt (facts : List (Algebraic.SignFact native)) :=
  readAt facts [2, -1] RootTransportLiterals.subject RootTransportLiterals.graph
open Lean Meta Elab Command
meta section
private def addControl (name : Name) (proposition : Lean.Expr) : Lean.MetaM Unit := do
  let dictionary ← synthInstance (mkApp (mkConst ``Decidable) proposition)
  let proof := mkAppN (mkConst ``of_decide_eq_true)
    #[proposition, dictionary, ← mkEqRefl (mkConst ``Bool.true)]
  KernelCheck.addChecked name proposition proof #[``Descriptor.validate, ``Descriptor.ofReplay?,
    ``Hex.RCF.RealCoefficients.ScalarPacket.build, ``Hex.RCF.RealCoefficients.ScalarPacket.buildLiteral]
elab "#transport_check" : command => liftTermElabM do
  let result ← mkAppM ``resultAt #[mkConst ``seeds]
  let predicate ← mkAppM ``Option.isSome #[← mkAppM ``Except.toOption #[result]]
  addControl `Hex.RCF.RealCoefficients.RootTransportConformance.accepted (← mkEq predicate (mkConst ``Bool.true))
end
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
#transport_check
def descriptorAt (facts : List (Algebraic.SignFact native)) (subject graph : Codec.Json) :=
  letI := Algebraic.Element.cachedOne reduction reduction_eq facts
  letI := Algebraic.Element.cachedAdd reduction reduction_eq facts
  letI := Algebraic.Element.cachedSub reduction reduction_eq facts
  letI := Algebraic.Element.cachedMul reduction reduction_eq facts
  letI := Algebraic.Element.cachedNatCast reduction reduction_eq facts
  Algebraic.RootReplay.readDescriptor (Algebraic.Element.signCodec base.codec facts)
    Signature.codec parent.sign parent.signature subject graph
def negativeRead := descriptorAt (constant (-1) :: seeds)
  RootTransportLiterals.negativeSubject RootTransportLiterals.negativeGraph
def wordFacts := constant 4 :: seeds
def wordRead := descriptorAt wordFacts RootTransportLiterals.wordSubject RootTransportLiterals.wordGraph
def word := readAt wordFacts [2,-1] RootTransportLiterals.wordSubject RootTransportLiterals.wordGraph
def conjugate := readAt (constant (-1) :: seeds) []
  RootTransportLiterals.negativeSubject RootTransportLiterals.negativeGraph
def missing := resultAt []
def staleSubject : Codec.Json :=
  match RootTransportLiterals.subject with
  | .array (.cons _ fields) => .array (.cons (Signature.codec.encode base.signature) fields)
  | _ => .null
def staleParsed := Algebraic.SignRequests.readRoot
  (Algebraic.Element.signCodec base.codec seeds) Signature.codec staleSubject
def stale := readAt seeds [] staleSubject RootTransportLiterals.graph
def zeroGuard := readAt seeds [0] .null .null
meta section
elab "#transport_refusals" : command => liftTermElabM do
  let parsed ← mkAppM ``Option.isSome #[← mkAppM ``Except.toOption #[mkConst ``staleParsed]]
  addControl `Hex.RCF.RealCoefficients.RootTransportConformance.stale_valid
    (← mkEq parsed (mkConst ``Bool.true))
  for (reader,name) in #[( ``negativeRead, `Hex.RCF.RealCoefficients.RootTransportConformance.negative_valid),
      (``wordRead, `Hex.RCF.RealCoefficients.RootTransportConformance.word_valid)] do
    let valid ← mkAppM ``Option.isSome #[← mkAppM ``Except.toOption #[mkConst reader]]
    addControl name (← mkEq valid (mkConst ``Bool.true))
  for (result, name, error) in #[( ``conjugate, `Hex.RCF.RealCoefficients.RootTransportConformance.wrong_conjugate,
      ``Hex.RCF.RealCoefficients.Replay.Error.binding),
      (``word, `Hex.RCF.RealCoefficients.RootTransportConformance.changed_word,
        ``Hex.RCF.RealCoefficients.Replay.Error.binding),
      (``missing, `Hex.RCF.RealCoefficients.RootTransportConformance.missing_record, ``Hex.RCF.RealCoefficients.Replay.Error.evidence),
      (``stale, `Hex.RCF.RealCoefficients.RootTransportConformance.stale_context, ``Hex.RCF.RealCoefficients.Replay.Error.evidence),
      (``zeroGuard, `Hex.RCF.RealCoefficients.RootTransportConformance.zero_guard, ``Hex.RCF.RealCoefficients.Replay.Error.divisor)] do
    let resultType ← whnf (← inferType (mkConst result))
    let function ← withLocalDeclD `value resultType.getAppArgs.back! fun value =>
      mkLambdaFVars #[value] (mkConst ``Unit.unit)
    let mapped ← mkAppM ``Except.map #[function, mkConst result]
    let type ← inferType mapped
    let expected := mkAppN (mkConst ``Except.error [.zero, .zero])
      #[type.getAppArgs[0]!, type.getAppArgs[1]!, mkConst error]
    addControl name (← mkEq mapped expected)
end
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
#transport_refusals
/-- info: 'Hex.RCF.RealCoefficients.RootTransportConformance.accepted' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms accepted
def checked := (resultAt seeds).toOption.get accepted
noncomputable def model := RootTransport.model RootTransportData.interpretation
  lower checked.converted checked.binding

theorem values (a : Data.extension.context.Value) :
    model.target.value ((RootTransport.step RootTransportData.conversion
      lower checked.converted checked.binding).value a) =
      (rational.adjoin lower).value a := model.value a

theorem selected : checked.converted.root original.value original.zero_iff original.one
    original.add original.sub original.mul original.nat original.sign = Real.sqrt 2 := by
  exact (RootTransportData.interpretation.root lower checked.converted checked.binding).trans
    selectedSqrt
/-- info: 'Hex.RCF.RealCoefficients.RootTransportConformance.values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms values
/-- info: 'Hex.RCF.RealCoefficients.RootTransportConformance.selected' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms selected
/-- The checked result retains and transports each actual source guard. -/
theorem guards : ∀ a ∈ [2, -1], RootTransportData.conversion.value a ≠ 0 :=
  checked.transported RootTransportData.interpretation
run_meta do
  for name in #[``accepted, ``negative_valid, ``word_valid, ``changed_word, ``wrong_conjugate, ``missing_record, ``stale_context, ``zero_guard,
      ``values, ``selected, ``guards, ``stale_valid, ``RootTransport.step_spec,
      ``RootTransport.step_native, ``RootTransport.read_zero, ``RootTransport.read_binding,
      ``RootTransport.read_evidence, ``RootTransport.readWith_eq,
      ``RootTransport.Checked.domains, ``RootTransport.Checked.transported,
      ``RootTransport.read_fields, ``RootTransport.read_subject,
      ``RootTransport.model, ``RootTransportData.interpretation] do
    let axioms ← collectAxioms name
    unless axioms.all (fun a => #[``propext, ``Classical.choice, ``Quot.sound].contains a) do
      throwError "unapproved root transport axiom"
    logInfo m!"{name}: {axioms}"
  unless ← Hex.RCF.ProofEvidence.contains ``selected
      (fun e => e.isConstOf ``Conversion.Model.root) do
    throwError "selected-root preservation omitted actual owner law"
end Hex.RCF.RealCoefficients.RootTransportConformance
