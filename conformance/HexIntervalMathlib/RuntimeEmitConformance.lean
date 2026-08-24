/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.RuntimeRuleEmit
import HexIntervalMathlib.RuntimeRuleConformance
import HexIntervalMathlib.RuntimeProofConformance

/-!
# Typed runtime expression-emission conformance

The theorem canary below is installed only from the expression returned by the
sealed root-target runtime emitter. Its chronology contains all eleven built-in
arithmetic rules, including binary applications with repeated input nodes.
The imported runtime-proof conformance owns the constructible action, body,
proposed/installed fact, event-order, and event-role mutations before a checked
token exists. This module adds emitter-schema and whole-input transplants plus
a self-consistent wrong fact quoter rejected at exact caller-input correlation;
private checked chronology fields cannot be mutated by an ordinary importer.
-/

namespace Hex.IntervalMathlib.RuntimeEmitConformance

open Lean Meta Elab Tactic
open Hex.Interval
open Hex.Interval.Executable
open Hex.Interval.Rule
open Hex.Interval.Rule.Runtime

/-- error: Unknown constant `Hex.Interval.RuntimeEmit.Registry.mk` -/
#guard_msgs in
#check RuntimeEmit.Registry.mk

/-- error: Unknown constant `Hex.Interval.RuntimeEmit.Active.mk` -/
#guard_msgs in
#check RuntimeEmit.Active.mk

/-- error: Unknown constant `Hex.Interval.RuntimeEmit.Lineage.mk` -/
#guard_msgs in
#check RuntimeEmit.Lineage.mk

/-- error: Unknown constant `Hex.Interval.RuntimeEmit.Checked.mk` -/
#guard_msgs in
#check RuntimeEmit.Checked.mk

/-- error: Unknown constant `Hex.Interval.RuntimeEmit.Emitted.mk` -/
#guard_msgs in
#check RuntimeEmit.Emitted.mk

section SealedPrivateConstruction

variable
  (registry : RuntimeEmit.Registry Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat))
  (active : RuntimeEmit.Active Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat))
  (lineage : RuntimeEmit.Lineage Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat))
  (checked : RuntimeEmit.Checked Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat))

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Registry` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Registry Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  { runtime := registry.runtime, quoter := registry.quoter, packages := registry.packages }

/-- error: Invalid `⟨...⟩` notation: Constructor for `Hex.Interval.RuntimeEmit.Registry` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Registry Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  ⟨registry.runtime, registry.quoter, registry.packages⟩

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Registry` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Registry Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  { registry with packages := registry.packages }

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Active` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Active Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  { registry := active.registry, terminal := active.terminal }

/-- error: Invalid `⟨...⟩` notation: Constructor for `Hex.Interval.RuntimeEmit.Active` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Active Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  ⟨active.registry, active.terminal⟩

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Active` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Active Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  { active with terminal := active.terminal }

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Lineage` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Lineage Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  { registry := lineage.registry, terminal := lineage.terminal }

/-- error: Invalid `⟨...⟩` notation: Constructor for `Hex.Interval.RuntimeEmit.Lineage` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Lineage Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  ⟨lineage.registry, lineage.terminal⟩

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Lineage` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Lineage Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  { lineage with terminal := lineage.terminal }

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Checked` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Checked Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  { registry := checked.registry, terminal := checked.terminal }

/-- error: Invalid `⟨...⟩` notation: Constructor for `Hex.Interval.RuntimeEmit.Checked` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Checked Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  ⟨checked.registry, checked.terminal⟩

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Checked` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Checked Hex.Interval
    (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat) :=
  { checked with terminal := checked.terminal }

end SealedPrivateConstruction

section EmittedPrivateConstruction

variable (input evidence : Expr) (emitted : RuntimeEmit.Emitted)

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Emitted` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Emitted :=
  { input := input, evidence := evidence }

/-- error: Invalid `⟨...⟩` notation: Constructor for `Hex.Interval.RuntimeEmit.Emitted` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Emitted :=
  ⟨input, evidence⟩

/-- error: invalid {...} notation, constructor for `RuntimeEmit.Emitted` is marked as private -/
#guard_msgs in
example : RuntimeEmit.Emitted :=
  { emitted with input }

end EmittedPrivateConstruction

def emitLimits : RuntimeEmit.Limits :=
  { proof := RuntimeRuleConformance.proofLimits, maxSchemas := 11, maxChronology := 11,
    maxExpressionCells := 1000000 }

def policyLimits : Policy.Limits :=
  { maxOffers := 11, maxBytes := 4096, maxPairs := 144, maxWork := 4096,
    maxScore := 0 }

def traceLimits : Trace.Limit :=
  { maxEvents := 0, maxBytes := 0, maxWork := 0, maxCode := 8 }

def terminalSearchLimits : Search.Limits :=
  { RuntimeRuleConformance.searchLimits with maxSteps := 13, leafFuel := 13 }

def envelope : Search.Envelope :=
  { state := RuntimeRuleConformance.stateLimits, policy := policyLimits, trace := traceLimits,
    search := terminalSearchLimits }

def terminalResultLimits : Search.Result.Limits :=
  { RuntimeRuleConformance.resultLimits with search := terminalSearchLimits }

def terminalAdapterLimits : RuntimeProof.Limits :=
  { RuntimeRuleConformance.adapterLimits with result := terminalResultLimits }

def controllerLimits : Runtime.Controller.Limits :=
  { maxChoices := 0, result := terminalResultLimits }

def quotedPoint : Hex.Interval :=
  Rule.Runtime.Quote.getValue
    (ofRawWithin RuntimeRuleConformance.endpoint
      (.bounds (.finite (RuntimeRuleConformance.d 1) false)
        (.finite (RuntimeRuleConformance.d 1) false))) (by decide)

def quotedWhole : Hex.Interval :=
  Rule.Runtime.Quote.getValue
    (ofRawWithin RuntimeRuleConformance.endpoint (.bounds .unbounded .unbounded)) (by decide)

def quotedTwo : Hex.Interval :=
  Rule.Runtime.Quote.getValue
    (ofRawWithin RuntimeRuleConformance.endpoint
      (.bounds (.finite (RuntimeRuleConformance.d 2) false)
        (.finite (RuntimeRuleConformance.d 2) false))) (by decide)

def quotedFacts : Array Hex.Interval :=
  #[quotedPoint, quotedTwo, quotedWhole, quotedWhole, quotedWhole, quotedWhole,
    quotedWhole, quotedWhole, quotedWhole, quotedWhole, quotedWhole, quotedWhole,
    quotedWhole]

def input : Proof.Input Hex.Interval :=
  { scope := { index := 0 }, program := RuntimeRuleConformance.program,
    facts := quotedFacts,
    target := { node := { index := 12 }, fact := quotedPoint } }

def changedInput : Proof.Input Hex.Interval :=
  { input with target := { input.target with node := { index := 11 } } }

private def liftOption {α : Type} : Option α → Option (ULift.{1, 0} α)
  | some value => some ⟨value⟩
  | none => none

private def runTree
    (tree : Search.Result.Tree Hex.Interval Rule.Runtime.Cause (List Nat) Proof.Key)
    (state : Runtime.State Hex.Interval Rule.Runtime.Cause) :
    List Action → Option
      (Search.Result.Tree Hex.Interval Rule.Runtime.Cause (List Nat) Proof.Key ×
        Runtime.State Hex.Interval Rule.Runtime.Cause)
  | [] => some (tree, state)
  | next :: rest => do
      let (transition, state) ← (state.stepWithin RuntimeRuleConformance.runtimeLimits next).toOption
      let tree := (← liftOption
        (Search.Result.advanceRuntimeWithin RuntimeRuleConformance.resultLimits
          RuntimeRuleConformance.measure tree transition).toOption).down
      runTree tree state rest

private def controllerFor
    (assembly : RuntimeProof.Assembly Hex.Interval Rule.Runtime.Cause) :
    Option (Runtime.Controller.State Hex.Interval Rule.Runtime.Cause (List Nat) Proof.Key) := do
  let branch := (← liftOption RuntimeRuleConformance.branch?).down
  let runtime ← (Runtime.State.startWithin RuntimeRuleConformance.runtimeLimits assembly branch).toOption
  let tree := (← liftOption ((Search.Result.startWithin RuntimeRuleConformance.resultLimits
    RuntimeRuleConformance.measure
    { index := 0 } branch).toOption)).down
  let (tree, runtime) ← runTree tree runtime RuntimeRuleConformance.actions
  (Runtime.Controller.State.startWithin controllerLimits envelope
    RuntimeRuleConformance.measure runtime tree).toOption

/-- Version-zero source target used to exercise initial evidence without any
runtime chronology. Its fact is quoted through the ordinary opaque interval
quoter. -/
def initialInput : Proof.Input Hex.Interval :=
  { RuntimeRuleConformance.input with
    target := { node := { index := 0 }, fact := RuntimeRuleConformance.point 1 } }

private def initialControllerFor
    (assembly : RuntimeProof.Assembly Hex.Interval Rule.Runtime.Cause) :
    Option (Runtime.Controller.State Hex.Interval Rule.Runtime.Cause (List Nat) Proof.Key) := do
  let branch := (← liftOption RuntimeRuleConformance.branch?).down
  let runtime ← (Runtime.State.startWithin RuntimeRuleConformance.runtimeLimits
    assembly branch).toOption
  let tree := (← liftOption ((Search.Result.startWithin terminalResultLimits
    RuntimeRuleConformance.measure { index := 0 } branch).toOption)).down
  (Runtime.Controller.State.startWithin controllerLimits envelope
    RuntimeRuleConformance.measure runtime tree).toOption

meta def checkedFor
    (registry : RuntimeEmit.Registry Hex.Interval
      (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat)) :
    Except RuntimeEmit.Error
      (RuntimeEmit.Checked Hex.Interval (Rule.semantics RuntimeRuleConformance.config)
        Rule.Runtime.Cause (List Nat)) := do
  let some controller := controllerFor registry.runtime.assembly
    | throw .malformed
  let active ← RuntimeEmit.Active.startWithin registry input controller
  let lineage ← active.targetWithin terminalResultLimits
    RuntimeRuleConformance.measure { node := { index := 12 }, version := 1 }
  lineage.quoteWithin terminalAdapterLimits RuntimeRuleConformance.measure

meta def initialLineageFor
    (registry : RuntimeEmit.Registry Hex.Interval
      (Rule.semantics RuntimeRuleConformance.config) Rule.Runtime.Cause (List Nat)) :
    Except RuntimeEmit.Error
      (RuntimeEmit.Lineage Hex.Interval (Rule.semantics RuntimeRuleConformance.config)
        Rule.Runtime.Cause (List Nat)) := do
  let some controller := initialControllerFor registry.runtime.assembly
    | throw .malformed
  let active ← RuntimeEmit.Active.startWithin registry initialInput controller
  active.targetWithin terminalResultLimits RuntimeRuleConformance.measure
    { node := { index := 0 }, version := 0 }

meta def initialCheckedWith (limits : RuntimeProof.Limits) :
    Except RuntimeEmit.Error
      (RuntimeEmit.Checked Hex.Interval (Rule.semantics RuntimeRuleConformance.config)
        Rule.Runtime.Cause (List Nat)) := do
  let assembly ← Rule.Runtime.assemblyWithin RuntimeRuleConformance.executableLimits
      RuntimeRuleConformance.config RuntimeRuleConformance.program
    |>.mapError fun _ => RuntimeEmit.Error.malformed
  let registry ← RuntimeEmit.Registry.buildWithin
    RuntimeRuleConformance.executableLimits emitLimits RuntimeRuleConformance.key assembly
    (Rule.Runtime.quoter RuntimeRuleConformance.config)
    #[Rule.Runtime.emitPackage RuntimeRuleConformance.config]
  let lineage ← initialLineageFor registry
  lineage.quoteWithin limits RuntimeRuleConformance.measure

meta def registryError
    (packages : Array
      (RuntimeEmit.Package (Rule.semantics RuntimeRuleConformance.config) (List Nat))) :
    Option RuntimeEmit.Error :=
  match Rule.Runtime.assemblyWithin RuntimeRuleConformance.executableLimits
      RuntimeRuleConformance.config RuntimeRuleConformance.program with
  | .error _ => some .malformed
  | .ok assembly =>
      match RuntimeEmit.Registry.buildWithin RuntimeRuleConformance.executableLimits
          emitLimits RuntimeRuleConformance.key assembly
          (Rule.Runtime.quoter RuntimeRuleConformance.config) packages with
      | .error error => some error
      | .ok _ => none

meta def emitResultWith (limits : RuntimeEmit.Limits)
    (package : RuntimeEmit.Package
      (Rule.semantics RuntimeRuleConformance.config) (List Nat)) :
    MetaM (Except RuntimeEmit.Error RuntimeEmit.Emitted) :=
  match Rule.Runtime.assemblyWithin RuntimeRuleConformance.executableLimits
      RuntimeRuleConformance.config RuntimeRuleConformance.program with
  | .error _ => pure (.error .malformed)
  | .ok assembly =>
      match RuntimeEmit.Registry.buildWithin RuntimeRuleConformance.executableLimits
          limits RuntimeRuleConformance.key assembly
          (Rule.Runtime.quoter RuntimeRuleConformance.config) #[package] with
      | .error error => pure (.error error)
      | .ok registry => match checkedFor registry with
        | .error error => pure (.error error)
        | .ok checked => RuntimeEmit.Checked.emitResultWithin limits checked

meta def emitWith (limits : RuntimeEmit.Limits)
    (package : RuntimeEmit.Package
      (Rule.semantics RuntimeRuleConformance.config) (List Nat)) :
    MetaM (Except RuntimeEmit.Error Expr) := do
  match ← emitResultWith limits package with
  | .error error => return .error error
  | .ok emitted => return .ok emitted.evidence

meta def emitInitialWith (limits : RuntimeEmit.Limits) :
    MetaM (Except RuntimeEmit.Error RuntimeEmit.Emitted) :=
  match initialCheckedWith terminalAdapterLimits with
  | .error error => pure (.error error)
  | .ok checked => checked.emitInitialTargetWithin limits

meta def emitInitialReplayWith (limits : RuntimeEmit.Limits) :
    MetaM (Except RuntimeEmit.Error RuntimeEmit.Emitted) :=
  match initialCheckedWith terminalAdapterLimits with
  | .error error => pure (.error error)
  | .ok checked => checked.emitResultWithin limits

meta def emitComputedAsInitial (limits : RuntimeEmit.Limits) :
    MetaM (Except RuntimeEmit.Error RuntimeEmit.Emitted) :=
  match Rule.Runtime.assemblyWithin RuntimeRuleConformance.executableLimits
      RuntimeRuleConformance.config RuntimeRuleConformance.program with
  | .error _ => pure (.error .malformed)
  | .ok assembly =>
      match RuntimeEmit.Registry.buildWithin RuntimeRuleConformance.executableLimits
          limits RuntimeRuleConformance.key assembly
          (Rule.Runtime.quoter RuntimeRuleConformance.config)
          #[Rule.Runtime.emitPackage RuntimeRuleConformance.config] with
      | .error error => pure (.error error)
      | .ok registry => match checkedFor registry with
        | .error error => pure (.error error)
        | .ok checked => checked.emitInitialTargetWithin limits

meta def activeError (changed : Proof.Input Hex.Interval) : Option RuntimeEmit.Error :=
  match Rule.Runtime.buildEmitWithin RuntimeRuleConformance.executableLimits
      emitLimits RuntimeRuleConformance.key RuntimeRuleConformance.config
      RuntimeRuleConformance.program with
  | .error _ => some .malformed
  | .ok registry => match controllerFor registry.runtime.assembly with
    | none => some .malformed
    | some controller => match RuntimeEmit.Active.startWithin registry changed controller with
      | .error error => some error
      | .ok _ => none

meta def targetError (changed : Proof.Input Hex.Interval) : Option RuntimeEmit.Error :=
  match Rule.Runtime.buildEmitWithin RuntimeRuleConformance.executableLimits
      emitLimits RuntimeRuleConformance.key RuntimeRuleConformance.config
      RuntimeRuleConformance.program with
  | .error _ => some .malformed
  | .ok registry => match controllerFor registry.runtime.assembly with
    | none => some .malformed
    | some controller => match RuntimeEmit.Active.startWithin registry changed controller with
      | .error error => some error
      | .ok active => match active.targetWithin terminalResultLimits
          RuntimeRuleConformance.measure { node := { index := 12 }, version := 1 } with
        | .error error => some error
        | .ok _ => none

meta def replaceFirst
    (package : RuntimeEmit.Package
      (Rule.semantics RuntimeRuleConformance.config) (List Nat))
    (handle : RuntimeEmit.Handle) :
    RuntimeEmit.Package (Rule.semantics RuntimeRuleConformance.config) (List Nat) :=
  { package with facts := package.facts.set! 0 handle }

elab "runtime_emit_canary" : tactic => do
  let goal ← getMainGoal
  let emitted ← match Rule.Runtime.buildEmitWithin RuntimeRuleConformance.executableLimits
      emitLimits RuntimeRuleConformance.key RuntimeRuleConformance.config
      RuntimeRuleConformance.program with
    | .error error => throwError "unified runtime emitter registry failed: {repr error}"
    | .ok registry => match checkedFor registry with
      | .error error => throwError "runtime emitter lineage failed: {repr error}"
      | .ok checked => RuntimeEmit.Checked.emitResultWithin emitLimits checked
  let emitted ← match emitted with
    | .error error => throwError "runtime expression emission failed: {repr error}"
    | .ok emitted => pure emitted
  let inputType ← mkAppM ``Proof.Input #[mkConst ``Hex.Interval]
  unless ← isDefEq (← inferType emitted.input) inputType do
    throwError "runtime emitter returned an ill-typed proof input"
  unless ← isDefEq emitted.input (mkConst ``input) do
    throwError "runtime emitter input differs from its sealed input"
  let semantics ← mkAppM ``Rule.semantics
    #[← Rule.Runtime.Quote.configExpr RuntimeRuleConformance.config]
  let evidenceType (input : Expr) : MetaM Expr := do
    let program ← mkAppM ``Proof.Input.program #[input]
    let base ← mkAppM ``Proof.initialBase #[input]
    let target ← mkAppM ``Proof.Input.target #[input]
    let claim ← mkAppM ``Proof.Semantics.Entails #[semantics, program, base, target]
    mkAppM ``Proof.Evidence #[claim]
  let actual ← inferType emitted.evidence
  unless ← isDefEq actual (← evidenceType emitted.input) do
    throwError "runtime emitter evidence is not correlated with its emitted input"
  if ← isDefEq actual (← evidenceType (mkConst ``changedInput)) then
    throwError "runtime emitter evidence admitted a changed input"
  let expected ← goal.getType
  unless ← isDefEq actual expected do
    throwError "runtime emitter returned the wrong theorem type\nactual: {actual}\nexpected: {expected}"
  goal.assign emitted.evidence
  replaceMainGoal []

/-- All eleven built-in runtime actions are load-bearing in this evidence. -/
def allBuiltinsEvidence : Proof.Evidence
    ((Rule.semantics RuntimeRuleConformance.config).Entails input.program
      (Proof.initialBase input) input.target) := by
  runtime_emit_canary

theorem allBuiltins :
    (Rule.semantics RuntimeRuleConformance.config).Entails input.program
      (Proof.initialBase input) input.target := by
  exact allBuiltinsEvidence.proof

/-- info: 'Hex.IntervalMathlib.RuntimeEmitConformance.allBuiltins' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms allBuiltins

elab "runtime_emit_initial_canary" : tactic => do
  let goal ← getMainGoal
  let emitted ← match ← emitInitialWith emitLimits with
    | .error error => throwError "initial-target emission failed: {repr error}"
    | .ok emitted => pure emitted
  let inputType ← mkAppM ``Proof.Input #[mkConst ``Hex.Interval]
  unless ← isDefEq (← inferType emitted.input) inputType do
    throwError "initial-target emitter returned an ill-typed proof input"
  unless ← isDefEq emitted.input (mkConst ``initialInput) do
    throwError "initial-target emitter changed its sealed input"
  let target ← mkAppM ``Proof.Input.target #[emitted.input]
  let fact ← withTransparency .reducible <|
    whnf (← mkAppM ``Proof.NodeFact.fact #[target])
  unless fact.getAppFn.constName? == some ``Rule.Runtime.Quote.getValue do
    throwError "initial-target canary did not retain the opaque checked interval encoding"
  let actual ← inferType emitted.evidence
  unless ← isDefEq actual (← goal.getType) do
    throwError "initial-target emitter returned the wrong Evidence claim"
  goal.assign emitted.evidence
  replaceMainGoal []

/-- A checked opaque interval already present at version zero needs no runtime
chronology or theorem schema authority. -/
def initialEvidence : Proof.Evidence
    ((Rule.semantics RuntimeRuleConformance.config).Entails initialInput.program
      (Proof.initialBase initialInput) initialInput.target) := by
  runtime_emit_initial_canary

theorem initialTarget :
    (Rule.semantics RuntimeRuleConformance.config).Entails initialInput.program
      (Proof.initialBase initialInput) initialInput.target :=
  initialEvidence.proof

/-- info: 'Hex.Interval.Proof.initialTarget' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Proof.initialTarget

/-- info: 'Hex.IntervalMathlib.RuntimeEmitConformance.initialTarget' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms initialTarget

elab "runtime_emit_initial_guards" : tactic => do
  let expectCheckedError (label : String)
      (actual : Except RuntimeEmit.Error
        (RuntimeEmit.Checked Hex.Interval (Rule.semantics RuntimeRuleConformance.config)
          Rule.Runtime.Cause (List Nat))) (expected : RuntimeEmit.Error) := do
    match actual with
    | .error error => unless error == expected do
        throwError "{label}: expected {repr expected}, got {repr error}"
    | .ok _ => throwError "{label}: unexpectedly admitted"
  let expectEmitError (label : String)
      (actual : Except RuntimeEmit.Error RuntimeEmit.Emitted)
      (expected : RuntimeEmit.Error) := do
    match actual with
    | .error error => unless error == expected do
        throwError "{label}: expected {repr expected}, got {repr error}"
    | .ok _ => throwError "{label}: unexpectedly admitted"
  let expectChecked (label : String)
      (actual : Except RuntimeEmit.Error
        (RuntimeEmit.Checked Hex.Interval (Rule.semantics RuntimeRuleConformance.config)
          Rule.Runtime.Cause (List Nat))) := do
    match actual with
    | .ok _ => pure ()
    | .error error => throwError "{label}: unexpectedly refused with {repr error}"
  let minimalProof : Proof.Limits :=
    { maxPackages := 1, maxSchemas := 11, maxBodyCells := 0,
      maxDependencies := 0, maxChronology := 0 }
  let minimalTree : Proof.TreeLimits :=
    { maxNodes := 1, maxDepth := 0, maxBodyCells := 0, maxWork := 2 }
  let minimalAdapter : RuntimeProof.Limits :=
    { result := terminalAdapterLimits.result, proof := minimalProof, tree := minimalTree,
      maxTransitions := 0, maxEvents := 0, maxStructuralCells := 0 }
  expectChecked "exact singleton quotation limits" (initialCheckedWith minimalAdapter)
  expectCheckedError "result node one-under"
    (initialCheckedWith
      { terminalAdapterLimits with
        result := { terminalAdapterLimits.result with maxNodes := 0 } })
    (.terminal (.runtimeProof (.malformed .tree)))
  expectCheckedError "proof-tree node one-under"
    (initialCheckedWith
      { terminalAdapterLimits with
        tree := { terminalAdapterLimits.tree with maxNodes := 0 } })
    (.terminal (.runtimeProof (.proof .proofNodeLimit)))
  -- The singleton root has depth zero, so no smaller depth exists. Its one
  -- node plus one edge make proof work two; one-under pins the edge charge.
  expectCheckedError "proof-tree edge-inclusive work one-under"
    (initialCheckedWith
      { terminalAdapterLimits with
        tree := { terminalAdapterLimits.tree with maxWork := 1 } })
    (.terminal (.runtimeProof (.proof .proofWorkLimit)))
  expectEmitError "computed chronology/version refusal"
    (← emitComputedAsInitial emitLimits) .malformed
  expectEmitError "emitter schema one-under"
    (← emitInitialWith { emitLimits with maxSchemas := 10 }) (.resource .schemas)
  expectEmitError "proof package one-under"
    (← emitInitialWith
      { emitLimits with proof := { emitLimits.proof with maxPackages := 0 } })
    (.proofBuild .packageLimit)
  expectEmitError "proof schema one-under"
    (← emitInitialWith
      { emitLimits with proof := { emitLimits.proof with maxSchemas := 10 } })
    (.proofBuild .schemaLimit)
  let minimalEmit : RuntimeEmit.Limits :=
    { proof := minimalProof, maxSchemas := 11, maxChronology := 0,
      maxExpressionCells := emitLimits.maxExpressionCells }
  let emitted ← match ← emitInitialWith minimalEmit with
    | .error error => throwError "empty chronology minimum refused: {repr error}"
    | .ok emitted => pure emitted
  let replayed ← match ← emitInitialReplayWith emitLimits with
    | .error error => throwError "ordinary empty replay refused: {repr error}"
    | .ok emitted => pure emitted
  unless ← isDefEq emitted.input replayed.input do
    throwError "initial-target and ordinary replay quoted different inputs"
  unless ← isDefEq (← inferType emitted.evidence) (← inferType replayed.evidence) do
    throwError "initial-target and ordinary replay emitted different claims"
  let inputCells := RuntimeEmit.expressionCells emitted.input
  let evidenceCells := RuntimeEmit.expressionCells emitted.evidence
  if inputCells == 0 || evidenceCells ≤ inputCells then
    throwError "initial-target expression accounting lost its two-stage boundary"
  if RuntimeEmit.expressionCells replayed.evidence ≤ evidenceCells then
    throwError "initial-target evidence did not stay smaller than empty replay"
  expectEmitError "input expression one-under"
    (← emitInitialWith { emitLimits with maxExpressionCells := inputCells - 1 })
    (.resource .expression)
  expectEmitError "evidence expression one-under"
    (← emitInitialWith { emitLimits with maxExpressionCells := evidenceCells - 1 })
    (.resource .expression)
  -- The preceding failures must roll Meta state back: the same exact request
  -- remains admissible after both expression-cap failures.
  match ← emitInitialWith emitLimits with
  | .error error => throwError "initial-target rollback failed: {repr error}"
  | .ok _ => pure ()
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by runtime_emit_initial_guards

elab "runtime_emit_registry_guards" : tactic => do
  let package := Rule.Runtime.emitPackage RuntimeRuleConformance.config
  let first := package.facts[0]'(by decide)
  let second := package.facts[1]'(by decide)
  let expect (label : String) (actual expected : Option RuntimeEmit.Error) := do
    unless actual == expected do
      throwError "{label}: expected {repr expected}, got {repr actual}"
  expect "missing package handle"
    (registryError #[{ package with facts := package.facts.eraseIdx 0 }])
    (some (.missingHandle first.key))
  let extraKey : Proof.Key :=
    { rule := { name := "conformance.runtime.emit.extra" }, role := .fact,
      bodySchema := 1 }
  expect "extra package handle"
    (registryError #[{ package with facts := package.facts.push { first with key := extraKey } }])
    (some (.extraHandle extraKey))
  expect "duplicate package handle"
    (registryError #[{ package with facts := package.facts.push first }])
    (some (.duplicateHandle first.key))
  let wrongRoleKey := { first.key with role := Proof.Role.equality }
  expect "wrong-role handle"
    (registryError #[replaceFirst package { first with key := wrongRoleKey }])
    (some (.wrongRole wrongRoleKey))
  let negProof : Proof.Package (Rule.semantics RuntimeRuleConformance.config) (List Nat) :=
    { registrations := #[], facts := #[Rule.negSchema RuntimeRuleConformance.config] }
  let addProof : Proof.Package (Rule.semantics RuntimeRuleConformance.config) (List Nat) :=
    { registrations := #[], facts := #[Rule.addSchema RuntimeRuleConformance.config] }
  let negPackage : RuntimeEmit.Package
      (Rule.semantics RuntimeRuleConformance.config) (List Nat) :=
    { proof := negProof, facts := #[first] }
  let addPackage : RuntimeEmit.Package
      (Rule.semantics RuntimeRuleConformance.config) (List Nat) :=
    { proof := addProof, facts := #[second] }
  expect "global duplicate handle"
    (registryError #[negPackage, negPackage])
    (some (.duplicateHandle first.key))
  expect "cross-package handle transplant"
    (registryError #[{ negPackage with facts := #[second] },
      { addPackage with facts := #[first] }])
    (some (.extraHandle second.key))
  expect "fact-input transplant"
    (activeError { input with facts := input.facts.set! 0 Hex.Interval.empty })
    (some (.terminal .mismatch))
  expect "target-input transplant"
    (targetError { input with target := { input.target with node := { index := 11 } } })
    (some (.terminal .mismatch))
  expect "scope-input transplant"
    (activeError { input with scope := { index := 1 } })
    (some (.terminal .mismatch))
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by runtime_emit_registry_guards

elab "runtime_emit_failure_guards" : tactic => do
  let package := Rule.Runtime.emitPackage RuntimeRuleConformance.config
  let first := package.facts[0]'(by decide)
  let expect (label : String) (actual : Except RuntimeEmit.Error Expr)
      (expected : RuntimeEmit.Error) := do
    match actual with
    | .error error => unless error == expected do
        throwError "{label}: expected {repr expected}, got {repr error}"
    | .ok _ => throwError "{label}: malformed emission was accepted"
  let wrongType : RuntimeEmit.Handle :=
    { first with schema := { emit := fun _ => pure (mkNatLit 0) } }
  expect "wrong emitter type" (← emitWith emitLimits (replaceFirst package wrongType)) .emitter
  let openMVar : RuntimeEmit.Handle :=
    { first with schema := { emit := fun _ => do
        let semantics ← mkAppM ``Rule.semantics
          #[← Rule.Runtime.Quote.configExpr RuntimeRuleConformance.config]
        let expected ← mkAppM ``Proof.FactSchema #[semantics]
        mkFreshExprMVar expected } }
  expect "open emitter metavariable"
    (← emitWith emitLimits (replaceFirst package openMVar)) .emitter
  let placeholder : RuntimeEmit.Handle :=
    { first with schema := { emit := fun _ => do
        let semantics ← mkAppM ``Rule.semantics
          #[← Rule.Runtime.Quote.configExpr RuntimeRuleConformance.config]
        let expected ← mkAppM ``Proof.FactSchema #[semantics]
        mkSorry expected true } }
  expect "synthetic emitter placeholder"
    (← emitWith emitLimits (replaceFirst package placeholder)) .emitter
  let transientName :=
    `Hex.IntervalMathlib.RuntimeEmitConformance.transientEmitterSchema
  let temporary : RuntimeEmit.Handle :=
    { first with schema := { emit := fun _ => do
        let value ← mkAppM ``Rule.negSchema
          #[← Rule.Runtime.Quote.configExpr RuntimeRuleConformance.config]
        let type ← inferType value
        addDecl <| .defnDecl
          { name := transientName, levelParams := [], type, value,
            hints := .abbrev, safety := .safe }
        pure (mkConst transientName) } }
  expect "temporary emitter declaration"
    (← emitWith emitLimits (replaceFirst package temporary)) .emitter
  if (← getEnv).contains transientName then
    throwError "failed runtime emitter leaked a temporary declaration"
  let scratch ← mkFreshExprMVar (mkConst ``Nat)
  let scratchId := scratch.mvarId!
  let assigning : RuntimeEmit.Handle :=
    { first with schema := { emit := fun _ => do
        scratchId.assign (mkNatLit 0)
        mkAppM ``Rule.negSchema
          #[← Rule.Runtime.Quote.configExpr RuntimeRuleConformance.config] } }
  match ← emitWith emitLimits (replaceFirst package assigning) with
  | .error error => throwError "assigning emitter baseline failed: {repr error}"
  | .ok _ => pure ()
  if ← scratchId.isAssigned then
    throwError "successful runtime emitter leaked a Meta assignment"
  let wrongSchema : RuntimeEmit.Handle :=
    { first with schema := { emit := fun _ => do
        mkAppM ``Rule.addSchema
          #[← Rule.Runtime.Quote.configExpr RuntimeRuleConformance.config] } }
  expect "schema expression transplant"
    (← emitWith emitLimits (replaceFirst package wrongSchema)) (.handleKey first.key)
  expect "schema count one-under"
    (← emitWith { emitLimits with maxSchemas := 10 } package) (.resource .schemas)
  expect "chronology count one-under"
    (← emitWith { emitLimits with maxChronology := 10 } package) (.resource .chronology)
  expect "body count one-under"
    (← emitWith { emitLimits with proof :=
      { RuntimeRuleConformance.proofLimits with maxBodyCells := 0 } } package)
    (.proof .bodyLimit)
  expect "dependency count one-under"
    (← emitWith { emitLimits with proof :=
      { RuntimeRuleConformance.proofLimits with maxDependencies := 1 } } package)
    (.proof .dependencyLimit)
  let accepted ← emitResultWith emitLimits package
  let emitted ← match accepted with
    | .error error => throwError "expression-size baseline failed: {repr error}"
    | .ok emitted => pure emitted
  let inputCells := RuntimeEmit.expressionCells emitted.input
  let evidenceCells := RuntimeEmit.expressionCells emitted.evidence
  if inputCells == 0 || evidenceCells == 0 then
    throwError "runtime emitter reported a zero-sized expression"
  expect "input expression count one-under"
    (← emitWith { emitLimits with maxExpressionCells := inputCells - 1 } package)
    (.resource .expression)
  if evidenceCells ≤ inputCells then
    throwError "evidence-size guard did not reach the second emitted expression"
  expect "evidence expression count one-under"
    (← emitWith { emitLimits with maxExpressionCells := evidenceCells - 1 } package)
    (.resource .expression)
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by runtime_emit_failure_guards

/-! ## Mixed instance/equality/fact/transport chronology -/

namespace Mixed

open Hex.Interval.Experiment.SineSign
def emitLimits : RuntimeEmit.Limits :=
  { proof := RuntimeProofConformance.proofLimits, maxSchemas := 4, maxChronology := 4,
    maxExpressionCells := 1000000 }

def policyLimits : Policy.Limits :=
  { maxOffers := 8, maxBytes := 4096, maxPairs := 64, maxWork := 4096,
    maxScore := 0 }

def traceLimits : Trace.Limit :=
  { maxEvents := 0, maxBytes := 0, maxWork := 0, maxCode := 8 }

def envelope : Search.Envelope :=
  { state := RuntimeProofConformance.stateLimits, policy := policyLimits, trace := traceLimits,
    search := RuntimeProofConformance.searchLimits }

def controllerLimits : Runtime.Controller.Limits :=
  { maxChoices := 0, result := RuntimeProofConformance.resultLimits }

meta def factExpr : Range → MetaM Expr
  | .all => pure (mkConst ``Range.all)
  | .unit => pure (mkConst ``Range.unit)
  | .nonnegative => pure (mkConst ``Range.nonnegative)
  | .nonpositive => pure (mkConst ``Range.nonpositive)
  | .zero => pure (mkConst ``Range.zero)
  | .empty => pure (mkConst ``Range.empty)

meta def factHandle : RuntimeEmit.Handle :=
  { key := RuntimeProofConformance.factProofKey
    schema := { emit := fun _ => pure (mkConst ``RuntimeProofConformance.factSchema) } }

meta def equalityHandle : RuntimeEmit.Handle :=
  { key := RuntimeProofConformance.equalityProofKey
    schema := { emit := fun _ => pure (mkConst ``RuntimeProofConformance.equalitySchema) } }

meta def instanceHandle : RuntimeEmit.Handle :=
  { key := RuntimeProofConformance.instanceProofKey
    schema := { emit := fun _ => pure (mkConst ``RuntimeProofConformance.instanceSchema) } }

meta def package : RuntimeEmit.Package RuntimeProofConformance.semantics Nat :=
  { proof := RuntimeProofConformance.proofPackage
    facts := #[factHandle]
    equalities := #[equalityHandle]
    instances := #[instanceHandle] }

meta def quoter : RuntimeEmit.Quoter Range RuntimeProofConformance.semantics :=
  { factType := { emit := fun _ => pure (mkConst ``Range) }
    fact := { emit := factExpr }
    semantics := { emit := fun _ => pure (mkConst ``RuntimeProofConformance.semantics) }
    domain := { emit := fun _ => pure (mkConst ``RuntimeProofConformance.domain) }
    laws := { emit := fun _ => pure (mkConst ``RuntimeProofConformance.laws) } }

/-- Deliberately misquote one uniquely marked, unused seed fact as the strictly
smaller zero fact. Replay remains internally valid while the emitted input
differs from the caller's claim. -/
meta def shiftedQuoter : RuntimeEmit.Quoter Range RuntimeProofConformance.semantics :=
  { quoter with fact := { emit := fun
      | .nonnegative => pure (mkConst ``Range.zero)
      | fact => factExpr fact } }

def correlationInput : Proof.Input Range :=
  { RuntimeProofConformance.input with facts := #[.unit, .nonnegative, .all] }

def shiftedInput : Proof.Input Range :=
  { RuntimeProofConformance.input with facts := #[.unit, .zero, .all] }

private def advance
    (tree : Search.Result.Tree Range Nat Nat Proof.Key)
    (runtime : Runtime.State Range Nat) : List Action →
    Option (Search.Result.Tree Range Nat Nat Proof.Key × Runtime.State Range Nat)
  | [] => some (tree, runtime)
  | action :: rest => do
      let (transition, runtime) ← (runtime.stepWithin RuntimeProofConformance.runtimeLimits action).toOption
      let tree := (← liftOption
        (Search.Result.advanceRuntimeWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure tree transition).toOption).down
      advance tree runtime rest

private def controllerFor (assembly : RuntimeProof.Assembly Range Nat)
    (facts : Array Range) :
    Option (Runtime.Controller.State Range Nat Nat Proof.Key) := do
  let branch := (← liftOption (RuntimeProofConformance.branchWith? facts)).down
  let runtime ← (Runtime.State.startWithin RuntimeProofConformance.runtimeLimits assembly branch).toOption
  let tree := (← liftOption ((Search.Result.startWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure
    RuntimeProofConformance.scope branch).toOption)).down
  let (tree, runtime) ← advance tree runtime
    [RuntimeProofConformance.instanceAction, RuntimeProofConformance.equalityAction, RuntimeProofConformance.factAction, RuntimeProofConformance.transportAction]
  (Runtime.Controller.State.startWithin controllerLimits envelope RuntimeProofConformance.measure runtime tree).toOption

meta def emitResultWith (limits : RuntimeEmit.Limits)
    (selectedQuoter : RuntimeEmit.Quoter Range RuntimeProofConformance.semantics)
    (sealedInput : Proof.Input Range) :
    MetaM (Except RuntimeEmit.Error RuntimeEmit.Emitted) :=
  match RuntimeProofConformance.assembly? with
  | none => pure (.error .malformed)
  | some assembly =>
      match RuntimeEmit.Registry.buildWithin RuntimeProofConformance.executableLimits limits
          RuntimeProofConformance.adapterKey assembly selectedQuoter #[package] with
      | .error error => pure (.error error)
      | .ok registry => match controllerFor registry.runtime.assembly sealedInput.facts with
        | none => pure (.error .malformed)
        | some controller =>
          match RuntimeEmit.Active.startWithin registry sealedInput controller with
          | .error error => pure (.error error)
          | .ok active => match (RuntimeEmit.Active.targetWithin
              RuntimeProofConformance.resultLimits RuntimeProofConformance.measure active
              { node := node 2, version := 1 }) with
            | .error error => pure (.error error)
            | .ok lineage => match lineage.quoteWithin RuntimeProofConformance.adapterLimits
                RuntimeProofConformance.measure with
              | .error error => pure (.error error)
              | .ok checked => RuntimeEmit.Checked.emitResultWithin limits checked

meta def emitWith (limits : RuntimeEmit.Limits) :
    MetaM (Except RuntimeEmit.Error Expr) := do
  match ← emitResultWith limits quoter RuntimeProofConformance.input with
  | .error error => return .error error
  | .ok emitted => return .ok emitted.evidence

elab "runtime_emit_mixed_canary" : tactic => do
  let goal ← getMainGoal
  let emitted ← emitWith emitLimits
  let candidate ← match emitted with
    | .error error => throwError "mixed runtime expression failed: {repr error}"
    | .ok candidate => pure candidate
  let expected ← goal.getType
  unless ← isDefEq (← inferType candidate) expected do
    throwError "mixed runtime emitter returned the wrong Evidence type"
  goal.assign candidate
  replaceMainGoal []

elab "runtime_emit_mixed_guards" : tactic => do
  match ← emitWith { emitLimits with maxSchemas := 2 } with
  | .error (.resource .schemas) => pure ()
  | .error error =>
      throwError "mixed schema limit returned the wrong error: {repr error}"
  | .ok _ =>
      throwError "mixed fact/equality/instance handles exceeded the global schema limit"
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

example : True := by runtime_emit_mixed_guards

elab "runtime_emit_input_correlation_guards" : tactic => do
  let emitted ← match ← emitResultWith emitLimits shiftedQuoter correlationInput with
    | .error error => throwError "shifted fact quoter failed to emit: {repr error}"
    | .ok emitted => pure emitted
  unless ← isDefEq emitted.input (mkConst ``shiftedInput) do
    throwError "shifted fact quoter did not produce the deliberately shifted input"
  if ← isDefEq emitted.input (mkConst ``correlationInput) then
    throwError "exact input correlation accepted a shifted fact quoter"
  let evidenceType (quotedInput : Expr) : MetaM Expr := do
    let program ← mkAppM ``Proof.Input.program #[quotedInput]
    let base ← mkAppM ``Proof.initialBase #[quotedInput]
    let target ← mkAppM ``Proof.Input.target #[quotedInput]
    let claim ← mkAppM ``Proof.Semantics.Entails
      #[mkConst ``RuntimeProofConformance.semantics, program, base, target]
    mkAppM ``Proof.Evidence #[claim]
  let actual ← inferType emitted.evidence
  unless ← isDefEq actual (← evidenceType emitted.input) do
    throwError "shifted evidence lost correlation with its emitted input"
  if ← isDefEq actual (← evidenceType (mkConst ``correlationInput)) then
    throwError "shifted evidence was mistaken for the expected exact-input claim"
  let goal ← getMainGoal
  goal.assign (mkConst ``True.intro)
  replaceMainGoal []

/-- A self-consistent wrong quoter can emit, but exact claim-input correlation
rejects both its quoted input and its evidence type. -/
example : True := by runtime_emit_input_correlation_guards

def evidence : Proof.Evidence
    (RuntimeProofConformance.semantics.Entails RuntimeProofConformance.input.program (Proof.initialBase RuntimeProofConformance.input) RuntimeProofConformance.input.target) := by
  runtime_emit_mixed_canary

theorem target :
    RuntimeProofConformance.semantics.Entails RuntimeProofConformance.input.program (Proof.initialBase RuntimeProofConformance.input) RuntimeProofConformance.input.target :=
  evidence.proof

/-- info: 'Hex.IntervalMathlib.RuntimeEmitConformance.Mixed.target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms target

end Mixed

end Hex.IntervalMathlib.RuntimeEmitConformance
