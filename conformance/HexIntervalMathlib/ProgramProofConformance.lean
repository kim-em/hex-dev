/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.Proof

/-!
# Supported program/proof conformance

This canary exercises a complete function-agnostic chronology: an authenticated
reflexive program instance, a fact theorem, an equality theorem, equality
transport, exact target closure, and a separately owned refuter. Mutated quote
fields fail before they can alter the immutable proof state.
-/

namespace Hex.IntervalMathlib.ProgramProofConformance

open Hex.Interval
open Hex.Interval.Proof

inductive TestFact where
  | all | yes | no | empty
  deriving DecidableEq, Repr

def domain : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "proof-source", version := 1 }
def operation : Operation := { key := sourceKey, inputs := [], output := domain }
def sourceNode : Node := { domain, op := { index := 0 }, args := [] }
def node0 : NodeId := { index := 0 }
def node1 : NodeId := { index := 1 }
def program : Program := { operations := #[operation], nodes := #[sourceNode, sourceNode] }

#guard program.check

def meaning : Hex.Interval.Program.Meaning Bool :=
  { operation, relation := fun _ result => result = true }

example : Hex.Interval.Program.Aligned [meaning] [operation] := by
  simp [Hex.Interval.Program.Aligned, meaning]

/-- The exact aligned operation meaning has a nonempty model on both nodes. -/
theorem programModel :
    Hex.Interval.Program.Models #[meaning] program (fun _ => true) := by
  apply Hex.Interval.Program.modelsOfMeanings #[meaning] program (fun _ => true)
  · simp [program, meaning]
  · simp [Hex.Interval.Program.Meanings, Hex.Interval.Program.MeaningAt, meaning,
      program, sourceNode]

example : ¬ Hex.Interval.Program.Models #[] program (fun _ => true) := by
  intro model
  simpa [Hex.Interval.Program.Models, program] using model.1

def scope : Policy.ScopeId := { index := 7 }
def factRule : RuleKey := { name := "proof-fact", schema := 3 }
def equalityRule : RuleKey := { name := "proof-equality", schema := 3 }
def instanceRule : RuleKey := { name := "proof-instance", schema := 3 }
def refuteRule : RuleKey := { name := "proof-refute", schema := 3 }

def factRegistration : Registration :=
  { key := factRule
    head := sourceKey
    kind := .forward
    watches := [.result]
    writes := [.result] }

def equalityRegistration : Registration :=
  { key := equalityRule
    head := sourceKey
    kind := .rewrite
    watches := [.result]
    writes := [] }

def instanceRegistration : Registration :=
  { key := instanceRule
    head := sourceKey
    kind := .instantiate
    watches := []
    writes := []
    binding := .scoped }

def refuteRegistration : Registration :=
  { key := refuteRule
    head := sourceKey
    kind := .backward
    watches := []
    writes := []
    binding := .scoped }

def seen (node : NodeId) (version : Nat) : SeenVersion := { node, version }

def action (serial programVersion ruleIndex : Nat) (key : RuleKey) (kind : ActionKind)
    (node : NodeId)
    (inputs : List SeenVersion) (writes : List NodeId) : Action :=
  { serial
    programVersion
    application := { index := serial }
    rule := { index := ruleIndex }
    key
    node
    kind
    effort := 0
    inputs
    writes }

def contains : TestFact → Bool → Prop
  | .all, _ => True
  | .yes, value => value = true
  | .no, value => value = false
  | .empty, _ => False

def semantics : Proof.Semantics TestFact :=
  { Value := Bool
    models := fun checked valuation =>
      checked = program ∧ valuation node0 = valuation node1
    holds := fun _ valuation fact => contains fact.fact (valuation fact.node)
    holdsAgree := by
      intro checked left right fact within _ _ agree
      rw [agree fact.node within] }

def factDomain : Proof.Domain semantics :=
  { top := fun _ => .all
    topSound := by simp [semantics, contains]
    meet := fun checked node previous proposed installed =>
      if shape : (previous = .all ∨ previous = .yes) ∧ proposed = .yes ∧
          installed = .yes then
        some
          { proof := by
              rcases shape with ⟨previousShape, rfl, rfl⟩
              rcases previousShape with rfl | rfl
              · intro valuation model
                simp [semantics, contains]
              · intro valuation model
                simp [semantics, contains] }
      else none }

theorem laws : Proof.Laws semantics :=
  { holdsEq := by
      intro checked valuation left right fact model equal
      simp only [semantics, contains]
      rw [equal] }

def factKey : Proof.Key := { rule := factRule, role := .fact, bodySchema := 1 }
def equalityKey : Proof.Key := { rule := equalityRule, role := .equality, bodySchema := 2 }
def instanceKey : Proof.Key := { rule := instanceRule, role := .instance, bodySchema := 3 }
def refuteKey : Proof.Key := { rule := refuteRule, role := .refute, bodySchema := 4 }

def decode (expected : Nat) (body : List Nat) : Option Unit :=
  if body = [expected] then some () else none

def factSchema : Proof.FactSchema semantics :=
  { key := factKey
    Certificate := Unit
    decode := decode 11
    prove := fun context _ =>
      if shape : context.scope = scope ∧ context.program = program ∧
          context.proposed.fact = .yes ∧ context.proposed.node = node0 ∧
          context.assumptions = [{ node := node0, fact := .yes }] then
        some
          { proof := by
              rcases shape with ⟨_, programEq, factEq, nodeEq, assumptionsEq⟩
              intro valuation model assumptions
              have proposedEq : context.proposed = { node := node0, fact := .yes } := by
                cases h : context.proposed with
                | mk node fact =>
                    have nodeEq' : node = node0 := by simpa [h] using nodeEq
                    have factEq' : fact = .yes := by simpa [h] using factEq
                    subst node
                    subst fact
                    rfl
              have source := assumptions { node := node0, fact := .yes } (by
                simp [assumptionsEq])
              simpa [proposedEq] using source }
      else none }

def equalitySchema : Proof.EqualitySchema semantics :=
  { key := equalityKey
    Certificate := Unit
    decode := decode 22
    prove := fun context _ =>
      if shape : context.scope = scope ∧ context.program = program ∧
          context.left = node0 ∧ context.right = node1 ∧
          context.assumptions = [{ node := node0, fact := .yes }] then
        some
          { proof := by
              rcases shape with ⟨_, programEq, leftEq, rightEq, _⟩
              intro valuation model _
              simpa [semantics, programEq, leftEq, rightEq] using model.2 }
      else none }

def instanceSchema : Proof.InstanceSchema semantics :=
  { key := instanceKey
    Certificate := Unit
    decode := decode 33
    prove := fun context _ =>
      if shape : context.scope = scope ∧ context.beforeVersion = 0 ∧
          context.afterVersion = 1 ∧ context.before = program ∧
          context.after = program ∧ context.newNodes = [] then
        some
          { stable := by
              rcases shape with ⟨_, _, _, beforeEq, afterEq, _⟩
              simpa [beforeEq, afterEq] using Proof.stableRefl semantics program
            extension := by
              rcases shape with ⟨_, _, _, beforeEq, afterEq, _⟩
              simpa [beforeEq, afterEq] using Proof.extendsRefl semantics program }
      else none }

def refuteSchema : Proof.RefuteSchema semantics :=
  { key := refuteKey
    Certificate := Unit
    decode := decode 44
    prove := fun context _ =>
      if shape : context.scope = scope ∧ context.program = program ∧
          context.fact = .empty then
        some
          { proof := by
              rcases shape with ⟨_, _, factEq⟩
              intro _ _ impossible
              rw [factEq] at impossible
              exact impossible }
      else none }

def package : Proof.Package semantics :=
  { registrations := #[factRegistration, equalityRegistration, instanceRegistration,
      refuteRegistration]
    facts := #[factSchema]
    equalities := #[equalitySchema]
    instances := #[instanceSchema]
    refuters := #[refuteSchema] }

def limits : Proof.Limits :=
  { maxPackages := 1, maxSchemas := 4, maxBodyCells := 1,
    maxDependencies := 1, maxChronology := 4 }

def builtRegistry := Proof.Registry.buildWithin limits program #[package]

#guard match builtRegistry with
  | .ok built => built.registrations.size == 4 && built.facts.size == 1 &&
      built.equalities.size == 1 && built.instances.size == 1 && built.refuters.size == 1
  | .error _ => false

#guard match Proof.Registry.buildWithin { limits with maxPackages := 0 } program #[package] with
  | .error .packageLimit => true
  | _ => false

#guard match Proof.Registry.buildWithin { limits with maxSchemas := 3 } program #[package] with
  | .error .schemaLimit => true
  | _ => false

def orphanRule : RuleKey := { name := "proof-orphan", schema := 3 }
def orphanSchema : Proof.FactSchema semantics := { factSchema with
  key := { role := .fact, rule := orphanRule, bodySchema := 9 } }
def orphanPackage : Proof.Package semantics := { package with facts := #[orphanSchema] }
def duplicatePackage : Proof.Package semantics := { package with facts := #[factSchema, factSchema] }
def duplicateRegistrationPackage : Proof.Package semantics := { package with registrations :=
  #[factRegistration, equalityRegistration, instanceRegistration, refuteRegistration,
    factRegistration] }
def globalRule : RuleKey := { name := "proof-global", schema := 3 }
def globalRegistration : Registration :=
  { key := globalRule
    head := sourceKey
    kind := .instantiate
    watches := []
    writes := []
    binding := .global
    watchesProgram := true
    matchWatch := .network }
def globalPackage : Proof.Package semantics := { registrations := #[globalRegistration] }
def globalRegistry := Proof.Registry.buildWithin limits program #[globalPackage]
def badGlobalRegistration : Registration := { globalRegistration with watches := [.result] }
def badGlobalPackage : Proof.Package semantics := { registrations := #[badGlobalRegistration] }

#guard match Proof.Registry.buildWithin limits program #[orphanPackage] with
  | .error (.foreignSchema 0 key) => key == orphanSchema.key
  | _ => false

#guard match Proof.Registry.buildWithin { limits with maxSchemas := 5 } program
    #[duplicatePackage] with
  | .error (.duplicateSchema key) => key == factKey
  | _ => false

#guard match Proof.Registry.buildWithin limits program #[duplicateRegistrationPackage] with
  | .error (.duplicateRegistration key) => key == factRule
  | _ => false

#guard match Proof.Registry.buildWithin limits program #[badGlobalPackage] with
  | .error (.invalidRegistration _) => true
  | _ => false

def input : Proof.Input TestFact :=
  { scope, program, facts := #[.yes, .all], target := { node := node1, fact := .yes } }

def instanceAction := action 0 0 2 instanceRule .instantiate node0 [] []
def factAction := action 1 1 0 factRule .forward node0 [seen node0 0] [node0]
def equalityAction := action 2 1 1 equalityRule .rewrite node0 [seen node0 1] []

def globalAction : Action :=
  { action 0 0 0 globalRule .instantiate node0 [] [] with
    structuralInputs := [{ key := .node node0, generation := 0 }]
    matcherEpoch := some 0 }

#guard match globalRegistry with
  | .ok registry => registry.acceptsAction program globalAction []
  | .error _ => false
#guard match globalRegistry with
  | .ok registry => !registry.acceptsAction program
      { globalAction with inputs := [seen node0 0] } [node0]
  | .error _ => false

def instanceStep : Proof.InstanceStep :=
  { scope, beforeVersion := 0, afterVersion := 1, action := instanceAction,
    after := program, newNodes := [], schema := instanceKey, body := [33] }

def factStep : Proof.FactStep TestFact :=
  { scope, programVersion := 1, action := factAction, node := node0,
    previous := seen node0 0, version := 1, proposed := .yes, installed := .yes,
    assumptions := [seen node0 0], schema := factKey, body := [11] }

def equalityStep : Proof.EqualityStep :=
  { scope, programVersion := 1, action := equalityAction, equality := { index := 0 },
    left := node0, right := node1, assumptions := [seen node0 1],
    schema := equalityKey, body := [22] }

def transportStep : Proof.TransportStep TestFact :=
  { scope, programVersion := 1, node := node1, previous := seen node1 0,
    version := 1, equality := { index := 0 }, source := seen node0 1, installed := .yes }

def events : List (Proof.Event TestFact) :=
  [.instance instanceStep, .fact factStep, .equality equalityStep, .transport transportStep]

def run (quoted := events) :=
  match builtRegistry with
  | .ok registry =>
      Proof.replay limits registry factDomain laws input quoted 1 program (seen node1 1)
  | .error _ => .error .invalidInput

def succeeds : Bool := match run with | .ok _ => true | .error _ => false

#guard succeeds
#guard !(match run (events.set 0 (.instance { instanceStep with body := [34] })) with
  | .ok _ => true | .error _ => false)
#guard !(match run (events.set 1 (.fact { factStep with previous := seen node0 1 })) with
  | .ok _ => true | .error _ => false)
#guard !(match run (events.set 1 (.fact { factStep with body := [12] })) with
  | .ok _ => true | .error _ => false)
#guard match run (events.set 1 (.fact { factStep with body := [11, 12] })) with
  | .error .bodyLimit => true
  | _ => false
#guard !(match run (events.set 1 (.fact { factStep with scope := { index := 8 } })) with
  | .ok _ => true | .error _ => false)
#guard !(match run (events.set 1 (.fact { factStep with
    action := { factAction with rule := { index := 1 } } })) with
  | .ok _ => true | .error _ => false)
#guard !(match run (events.set 1 (.fact { factStep with
    action := { factAction with inputs := [seen node0 2] }
    assumptions := [seen node0 2] })) with
  | .ok _ => true | .error _ => false)
#guard match run (events.set 1 (.fact { factStep with
    action := { factAction with inputs := [seen node0 0, seen node1 0] }
    assumptions := [seen node0 0, seen node1 0] })) with
  | .error .dependencyLimit => true
  | _ => false
#guard !(match run (events.set 2 (.equality { equalityStep with right := node0 })) with
  | .ok _ => true | .error _ => false)
#guard !(match run (events.set 2 (.equality { equalityStep with body := [23] })) with
  | .ok _ => true | .error _ => false)
#guard !(match run (events.set 3 (.transport { transportStep with source := seen node1 0 })) with
  | .ok _ => true | .error _ => false)
#guard !(match builtRegistry with
  | .ok registry =>
      match Proof.replay limits registry factDomain laws input events 0 program (seen node1 1) with
      | .ok _ => true | .error _ => false
  | .error _ => true)
#guard !(match run (events ++ [.fact factStep]) with
  | .ok _ => true | .error _ => false)

/-- A rejected transition cannot alter the state subsequently used by a valid
transition. -/
def restores : Bool :=
  match builtRegistry with
  | .error _ => false
  | .ok registry =>
      match Proof.replayInstance limits registry factDomain input
          (Proof.State.start semantics input rfl) instanceStep with
      | .error _ => false
      | .ok afterInstance =>
          let bad := { factStep with body := [12] }
          match Proof.replayFact limits registry factDomain input afterInstance bad with
          | .ok _ => false
          | .error _ =>
              match Proof.replayFact limits registry factDomain input afterInstance factStep with
              | .ok _ => true
              | .error _ => false

#guard restores

/-- The successful generic replay produces an ordinary theorem. -/
def replayEvidence : Proof.Evidence
    (semantics.Entails input.program (Proof.initialBase input) input.target) :=
  match run with
  | .ok evidence => evidence
  | .error _ =>
      { proof := by
          intro valuation model assumptions
          have source := assumptions { node := node0, fact := .yes } (by
            simp [Proof.initialBase, input, node0])
          simpa [semantics, contains, input, node1, model.2] using source }

theorem replayCanary :
    semantics.Entails input.program (Proof.initialBase input) input.target :=
  replayEvidence.proof

#print axioms replayCanary

def impossibleInput : Proof.Input TestFact :=
  { scope, program, facts := #[.empty, .all], target := { node := node1, fact := .no } }

def refuteStep : Proof.RefuteStep :=
  { scope, programVersion := 0, seen := seen node0 0, schema := refuteKey, body := [44] }

def refutes : Bool :=
  match builtRegistry with
  | .error _ => false
  | .ok registry =>
      match Proof.replayRefute limits registry impossibleInput
          (Proof.State.start semantics impossibleInput rfl) refuteStep impossibleInput.target with
      | .ok _ => true
      | .error _ => false

#guard refutes

def unowned : Proof.Package semantics := { registrations := #[], refuters := #[refuteSchema] }

#guard match Proof.Registry.buildWithin limits program #[unowned] with
  | .error (.emptyRefuterOwner 0 key) => key == refuteKey
  | _ => false

open Lean Meta Elab Tactic

/-- A failing emitter cannot retain even a valid assignment it made before
returning an expression of the wrong type. -/
elab "proof_emit_restore" : tactic => do
  let goal ← getMainGoal
  let expected ← goal.getType
  let emitter : Proof.Emitter Unit :=
    { emit := fun _ => do
        goal.assign (mkConst ``True.intro)
        pure (mkNatLit 0) }
  let accepted ← try
    let _ ← Proof.emitChecked emitter () expected
    pure true
  catch _ => pure false
  if accepted then throwError "wrongly typed proof emitter was accepted"
  if ← goal.isAssigned then
    throwError "failed proof emitter leaked its Meta assignment"
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by proof_emit_restore

/-- Structural checking rejects an application whose explicit argument has the
wrong type, even though the raw expression can be constructed. -/
elab "proof_emit_reject_ill_typed" : tactic => do
  let goal ← getMainGoal
  let expected ← goal.getType
  let illTyped := mkApp2 (mkConst ``id [Level.zero]) (mkConst ``Bool) (mkNatLit 0)
  let emitter : Proof.Emitter Unit := { emit := fun _ => pure illTyped }
  let accepted ← try
    let _ ← Proof.emitChecked emitter () expected
    pure true
  catch _ => pure false
  if accepted then throwError "ill-typed proof emitter expression was accepted"
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by proof_emit_reject_ill_typed

/-- Synthetic placeholder expressions are rejected even at the expected type. -/
elab "proof_emit_reject_placeholder" : tactic => do
  let goal ← getMainGoal
  let expected ← goal.getType
  let emitter : Proof.Emitter Unit := { emit := fun _ => mkSorry expected true }
  let accepted ← try
    let _ ← Proof.emitChecked emitter () expected
    pure true
  catch _ => pure false
  if accepted then throwError "placeholder proof emitter expression was accepted"
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by proof_emit_reject_placeholder

/-- Open candidate and expected metavariables are both rejected without being
assigned by definitional equality. -/
elab "proof_emit_reject_mvars" : tactic => do
  let goal ← getMainGoal
  let expected ← goal.getType
  let openCandidate ← mkFreshExprMVar expected
  let candidateId := openCandidate.mvarId!
  let candidateEmitter : Proof.Emitter Unit := { emit := fun _ => pure openCandidate }
  let candidateAccepted ← try
    let _ ← Proof.emitChecked candidateEmitter () expected
    pure true
  catch _ => pure false
  if candidateAccepted then throwError "open proof emitter metavariable was accepted"
  if ← candidateId.isAssigned then
    throwError "rejected proof emitter metavariable was assigned"
  let openExpected ← mkFreshExprMVar (mkSort Level.zero)
  let expectedId := openExpected.mvarId!
  let expectedEmitter : Proof.Emitter Unit :=
    { emit := fun _ => pure (mkConst ``True.intro) }
  let expectedAccepted ← try
    let _ ← Proof.emitChecked expectedEmitter () openExpected
    pure true
  catch _ => pure false
  if expectedAccepted then throwError "open expected proposition was accepted"
  if ← expectedId.isAssigned then
    throwError "rejected expected metavariable was assigned"
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by proof_emit_reject_mvars

elab "proof_emit_accept" : tactic => do
  let goal ← getMainGoal
  let expected ← goal.getType
  let scratch ← mkFreshExprMVar (mkConst ``Nat)
  let scratchId := scratch.mvarId!
  let emitter : Proof.Emitter Unit :=
    { emit := fun _ => do
        scratchId.assign (mkNatLit 0)
        pure (mkConst ``replayCanary) }
  let evidence ← Proof.emitChecked emitter () expected
  if ← scratchId.isAssigned then
    throwError "successful proof emitter leaked a Meta assignment"
  goal.assign evidence
  replaceMainGoal []

example : semantics.Entails input.program (Proof.initialBase input) input.target := by
  proof_emit_accept

end Hex.IntervalMathlib.ProgramProofConformance
