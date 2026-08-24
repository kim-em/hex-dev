/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.RuntimeTerminal
import HexIntervalMathlib.RuntimeProofConformance

/-!
# Typed runtime-terminal conformance

Target settlement is exercised after the ordinary instance/equality/fact/
transport chronology both at the root and in two restarted split children.
Refutation is exercised against an exact established empty interval and a
package-owned theorem schema. The guards below, rather than the final fallback
theorems, prove that the terminal adapter actually admitted and replayed each
tree.
-/

namespace Hex.IntervalMathlib.RuntimeTerminalConformance

open Hex.Interval
open Hex.Interval.Executable
open Hex.Interval.Runtime
open Hex.Interval.RuntimeTerminal
open Hex.Interval.Experiment.SineSign


/-- error: Unknown constant `Hex.Interval.RuntimeTerminal.Active.mk` -/
#guard_msgs in
#check RuntimeTerminal.Active.mk

/-- error: Unknown constant `Hex.Interval.RuntimeTerminal.Lineage.mk` -/
#guard_msgs in
#check RuntimeTerminal.Lineage.mk

/-- error: Unknown constant `Hex.Interval.RuntimeTerminal.Checked.mk` -/
#guard_msgs in
#check RuntimeTerminal.Checked.mk

section PrivateConstruction

variable (registry : RuntimeProof.Registry Range RuntimeProofConformance.semantics Nat Nat)
  (input : Proof.Input Range)
  (controller : Runtime.Controller.State Range Nat Nat Proof.Key)
  (active : RuntimeTerminal.Active Range RuntimeProofConformance.semantics Nat Nat)

/-- error: invalid {...} notation, constructor for `Active` is marked as private -/
#guard_msgs in
example : RuntimeTerminal.Active Range RuntimeProofConformance.semantics Nat Nat :=
  { registry := registry, input := input, controller := controller }

/-- error: Invalid `⟨...⟩` notation: Constructor for `Hex.Interval.RuntimeTerminal.Active` is marked as private -/
#guard_msgs in
example : RuntimeTerminal.Active Range RuntimeProofConformance.semantics Nat Nat :=
  ⟨registry, input, controller⟩

/-- error: invalid {...} notation, constructor for `Active` is marked as private -/
#guard_msgs in
example : RuntimeTerminal.Active Range RuntimeProofConformance.semantics Nat Nat :=
  { active with input }

end PrivateConstruction

def policyLimits : Policy.Limits :=
  { maxOffers := 8, maxBytes := 1024, maxPairs := 64, maxWork := 64,
    maxScore := 0 }

def traceLimits : Trace.Limit :=
  { maxEvents := 0, maxBytes := 0, maxWork := 0, maxCode := 8 }

def envelope : Search.Envelope :=
  { state := RuntimeProofConformance.stateLimits, policy := policyLimits, trace := traceLimits,
    search := RuntimeProofConformance.searchLimits }

def controllerLimits : Runtime.Controller.Limits :=
  { maxChoices := 4, result := RuntimeProofConformance.resultLimits }

def policy : Policy.Interface Range (List Nat) ApplicationId RuleKey :=
  { choose := fun plan view => match plan with
    | [] => .stop []
    | wanted :: rest => match view.offers.find? fun offer => offer.id.index == wanted with
      | none => .stop plan
      | some offer => .select offer rest }

private def liftOption.{u, v} {α : Type u} (value : Option α) : Option (ULift.{v} α) :=
  value.map ULift.up

private def runPlan (plan : List Nat)
    (state : Runtime.Controller.State Range Nat Nat Proof.Key) :
    Option (Runtime.Controller.State Range Nat Nat Proof.Key) :=
  match Runtime.Controller.runWithin controllerLimits envelope RuntimeProofConformance.measure policy
      plan state with
  | .ok (.stopped _ state []) => some state
  | _ => none

private def runController := runPlan [0, 1, 3, 2]

private def runtimeFor (branch : State.Branch Range Nat) :
    Option (Runtime.State Range Nat) :=
  match RuntimeProofConformance.assembly? with
  | some assembly =>
      (Runtime.State.startWithin RuntimeProofConformance.runtimeLimits assembly branch).toOption
  | none => none

private def initialRootController :
    Option (Runtime.Controller.State Range Nat Nat Proof.Key) := do
  let branch := (← liftOption.{0, 1} RuntimeProofConformance.branch?).down
  let runtime ← runtimeFor branch
  let tree := (← liftOption.{0, 1} ((Search.Result.startWithin
    RuntimeProofConformance.resultLimits RuntimeProofConformance.measure
    RuntimeProofConformance.scope branch).toOption)).down
  let state ← (Runtime.Controller.State.startWithin controllerLimits envelope
    RuntimeProofConformance.measure runtime tree).toOption
  pure state

private def startRootController :
    Option (Runtime.Controller.State Range Nat Nat Proof.Key) := do
  let state ← initialRootController
  runController state

def rootLineage? : Option
    (RuntimeTerminal.Lineage Range RuntimeProofConformance.semantics Nat Nat) := do
  let registry ← RuntimeProofConformance.registry?
  let controller ← startRootController
  let active ← (RuntimeTerminal.Active.startWithin registry RuntimeProofConformance.input controller).toOption
  (RuntimeTerminal.Active.targetWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure active
    { node := node 2, version := 1 }).toOption

def rootChecked? : Option
    (RuntimeTerminal.Checked Range RuntimeProofConformance.semantics Nat Nat) := do
  let lineage ← rootLineage?
  (lineage.quoteWithin RuntimeProofConformance.adapterLimits RuntimeProofConformance.measure).toOption

def rootReplay? : Option
    (Proof.Evidence (RuntimeProofConformance.semantics.Entails RuntimeProofConformance.input.program
      (Proof.initialBase RuntimeProofConformance.input) RuntimeProofConformance.input.target)) := do
  match rootChecked? with
  | some checked =>
      (checked.replayWithin RuntimeProofConformance.adapterLimits
        RuntimeProofConformance.measure RuntimeProofConformance.domain
        RuntimeProofConformance.laws RuntimeProofConformance.input).toOption
  | none => none

#guard rootReplay?.isSome

#guard match RuntimeProofConformance.registry?, startRootController with
  | some registry, some controller =>
      (match RuntimeTerminal.Active.startWithin registry
          { RuntimeProofConformance.input with facts := #[.unit, .empty, .all] }
          controller with
        | .error .mismatch => true
        | _ => false) &&
      (match RuntimeTerminal.Active.startWithin registry
          { RuntimeProofConformance.input with scope := { index := 1 } }
          controller with
        | .error .mismatch => true
        | _ => false) &&
      (match RuntimeTerminal.Active.startWithin registry
          { scope := RuntimeProofConformance.scope, program := extendedProgram,
            facts := #[.unit, .all, .all, .all, .all],
            target := RuntimeProofConformance.input.target }
          controller with
        | .error .mismatch => true
        | _ => false) &&
      (match RuntimeTerminal.Active.startWithin registry
          { RuntimeProofConformance.input with target :=
            { node := node 3, fact := .nonpositive } }
          controller with
        | .error .mismatch => true
        | _ => false) &&
      (match RuntimeTerminal.Active.startWithin registry RuntimeProofConformance.input
          controller with
        | .ok active =>
            match active.targetWithin RuntimeProofConformance.resultLimits
                  RuntimeProofConformance.measure { node := node 1, version := 0 } with
              | .error .mismatch => true
              | _ => false
        | _ => false)
  | _, _ => false

def targetResourceError? : Option RuntimeTerminal.Error :=
  match RuntimeProofConformance.registry?, startRootController with
  | some registry, some controller =>
      match RuntimeTerminal.Active.startWithin registry RuntimeProofConformance.input
          controller with
      | .ok active =>
          match active.targetWithin
              { RuntimeProofConformance.resultLimits with
                search := { RuntimeProofConformance.searchLimits with
                  maxSteps := active.controller.tree.accounting.steps } }
              RuntimeProofConformance.measure { node := node 2, version := 1 } with
          | .error error => some error
          | .ok _ => none
      | .error error => some error
  | _, _ => none

#guard targetResourceError? == some (.result (.search .steps))

-- Complete quotation resources remain fail-closed at the transactional edge.
#guard match rootLineage? with
  | some lineage =>
      match lineage.quoteWithin
          { RuntimeProofConformance.adapterLimits with maxEvents := 3 }
          RuntimeProofConformance.measure with
      | .error (.runtimeProof (.resource .events)) => true
      | _ => false
  | none => false

private def pendingSplit? : Option
    (Search.Result.Tree Range Nat Nat Proof.Key) := do
  let branch ← RuntimeProofConformance.branch?
  let root := (← liftOption
    ((Search.Result.startWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure RuntimeProofConformance.scope branch).toOption)).down
  (Search.Result.splitWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure .depthFirst root RuntimeProofConformance.splitRecipe
    RuntimeProofConformance.leftSeed RuntimeProofConformance.rightSeed).toOption

private def startCurrentController
    (tree : Search.Result.Tree Range Nat Nat Proof.Key) :
    Option (Runtime.Controller.State Range Nat Nat Proof.Key) := do
  let (_, source) := (← liftOption.{0, 1} (Search.Result.current? tree)).down
  let runtime ← runtimeFor source.branch
  (Runtime.Controller.State.startWithin controllerLimits envelope RuntimeProofConformance.measure runtime tree).toOption

private def settleFirstChild : Option
    (RuntimeTerminal.Lineage Range RuntimeProofConformance.semantics Nat Nat) := do
  let registry ← RuntimeProofConformance.registry?
  let tree := (← liftOption.{0, 1} pendingSplit?).down
  let controller ← startCurrentController tree >>= runController
  let active ← (RuntimeTerminal.Active.startWithin registry RuntimeProofConformance.input controller).toOption
  (active.targetWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure
    { node := node 2, version := 1 }).toOption

def splitChecked? : Option
    (RuntimeTerminal.Checked Range RuntimeProofConformance.semantics Nat Nat) := do
  let lineage ← settleFirstChild
  let (_, source) := (← liftOption.{0, 1} (Search.Result.current? lineage.tree)).down
  let runtime ← runtimeFor source.branch
  -- The restart is bound to the first terminal's retained tree. Runtime starts
  -- with serial/equality identity zero; this split occurs before parent events.
  let resumed ← (lineage.resumeWithin controllerLimits envelope RuntimeProofConformance.measure runtime).toOption
  let controller ← runController resumed.controller
  let active ← (RuntimeTerminal.Active.startWithin resumed.registry resumed.input controller).toOption
  let complete ← (active.targetWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure
    { node := node 2, version := 1 }).toOption
  (complete.quoteWithin RuntimeProofConformance.adapterLimits RuntimeProofConformance.measure).toOption

def splitReplay? : Option
    (Proof.Evidence (RuntimeProofConformance.semantics.Entails RuntimeProofConformance.input.program
      (Proof.initialBase RuntimeProofConformance.input) RuntimeProofConformance.input.target)) := do
  match splitChecked? with
  | some checked =>
      (checked.replayWithin RuntimeProofConformance.adapterLimits
        RuntimeProofConformance.measure RuntimeProofConformance.domain
        RuntimeProofConformance.laws RuntimeProofConformance.input).toOption
  | none => none

#guard splitReplay?.isSome

-- A runtime from the already-settled sibling or a different root lineage
-- cannot resume the retained current child.
#guard match settleFirstChild with
  | some lineage =>
      match pendingSplit? with
      | some other =>
        match Search.Result.current? other with
        | some (_, left) =>
          match runtimeFor left.branch with
          | some leftRuntime =>
              (match lineage.resumeWithin controllerLimits envelope
                  RuntimeProofConformance.measure leftRuntime with
                | .error (.controller .mismatch) => true
                | _ => false) &&
              (match startRootController with
                | some root =>
                    match lineage.resumeWithin controllerLimits envelope
                        RuntimeProofConformance.measure root.runtime with
                    | .error (.controller .mismatch) => true
                    | _ => false
                | none => false)
          | none => false
        | none => false
      | none => false
  | none => false

/-! ## Inherited equality refusal -/

def postEqualitySplitAction : Action :=
  RuntimeProofConformance.action 2 1 0 4 RuntimeProofConformance.splitKey
    (node 2) .split 1 [{ node := node 2, version := 0 }]

def postEqualitySplitRecipe : Search.Result.Split Nat Proof.Key :=
  { scope := RuntimeProofConformance.scope, programVersion := 1,
    action := postEqualitySplitAction,
    parent := { node := node 2, version := 0 }, plan := 1,
    schema := RuntimeProofConformance.splitProofKey, body := [1] }

def postEqualityLeft : Search.Result.Seed Range :=
  { node := node 2, previous := postEqualitySplitRecipe.parent, fact := .nonpositive }

def postEqualityRight : Search.Result.Seed Range :=
  { node := node 2, previous := postEqualitySplitRecipe.parent, fact := .nonnegative }

private def hazardousResume? : Option
    (RuntimeTerminal.Lineage Range RuntimeProofConformance.semantics Nat Nat ×
      Runtime.State Range Nat) := do
  let registry ← RuntimeProofConformance.registry?
  let parent ← initialRootController >>= runPlan [0, 1]
  let tree := (← liftOption.{0, 1} ((Search.Result.splitWithin
    RuntimeProofConformance.resultLimits RuntimeProofConformance.measure .depthFirst
    parent.tree postEqualitySplitRecipe postEqualityLeft postEqualityRight).toOption)).down
  let (_, left) := (← liftOption.{0, 1} (Search.Result.current? tree)).down
  let leftRuntime ← (Runtime.State.startWithin RuntimeProofConformance.runtimeLimits
    parent.runtime.assembly left.branch).toOption
  let leftController ← (Runtime.Controller.State.startWithin controllerLimits envelope
    RuntimeProofConformance.measure leftRuntime tree).toOption
  let active ← (RuntimeTerminal.Active.startWithin registry RuntimeProofConformance.input
    leftController).toOption
  let lineage ← (active.targetWithin RuntimeProofConformance.resultLimits
    RuntimeProofConformance.measure { node := node 2, version := 0 }).toOption
  let (_, right) := (← liftOption.{0, 1} (Search.Result.current? lineage.tree)).down
  let rightRuntime ← (Runtime.State.startWithin RuntimeProofConformance.runtimeLimits
    parent.runtime.assembly right.branch).toOption
  pure (lineage, rightRuntime)

#guard match hazardousResume? with
  | some (lineage, runtime) =>
      match lineage.resumeWithin controllerLimits envelope
          RuntimeProofConformance.measure runtime with
      | .error .inheritedEqualities => true
      | _ => false
  | none => false

/-! ## Exact refutation -/

def refuteKey : Proof.Key :=
  { rule := RuntimeProofConformance.splitKey, role := .refute, bodySchema := 1 }

def refuteSchema : Proof.RefuteSchema RuntimeProofConformance.semantics :=
  { key := refuteKey, Certificate := Unit, decode := RuntimeProofConformance.decode,
    prove := fun context _ =>
      if shape : context.program = baseProgram ∧ context.node = node 1 ∧
          context.fact = .empty then
        some
          { proof := by
              intro valuation model holds
              have impossible := holds
              simp [shape.1, shape.2.1, shape.2.2,
                RuntimeProofConformance.semantics, Contains] at impossible }
      else none }

def refutePackage : Proof.Package RuntimeProofConformance.semantics Nat :=
  { RuntimeProofConformance.proofPackage with refuters := #[refuteSchema] }

def refuteProofLimits : Proof.Limits :=
  { RuntimeProofConformance.proofLimits with maxSchemas := 5 }

def refuteLimits : RuntimeProof.Limits :=
  { RuntimeProofConformance.adapterLimits with proof := refuteProofLimits }

def refuteRegistry? : Option
    (RuntimeProof.Registry Range RuntimeProofConformance.semantics Nat Nat) := do
  let assembly ← RuntimeProofConformance.assembly?
  let proof ← (Proof.Registry.buildWithin refuteProofLimits baseProgram
    #[refutePackage]).toOption
  (RuntimeProof.Registry.buildWithin RuntimeProofConformance.executableLimits
    { name := "sine-runtime-terminal", version := 1 } assembly proof).toOption

def refuteInput : Proof.Input Range :=
  { scope := RuntimeProofConformance.scope, program := baseProgram, facts := #[.unit, .empty, .all],
    target := { node := node 2, fact := .nonpositive } }

private def ordinaryRefuteActive? : Option
    (RuntimeTerminal.Active Range RuntimeProofConformance.semantics Nat Nat) := do
  let registry ← refuteRegistry?
  let controller ← startRootController
  (RuntimeTerminal.Active.startWithin registry RuntimeProofConformance.input controller).toOption

def refuteChecked? : Option
    (RuntimeTerminal.Checked Range RuntimeProofConformance.semantics Nat Nat) := do
  let registry ← refuteRegistry?
  let branch := (← liftOption.{0, 1}
    (RuntimeProofConformance.branchWith? refuteInput.facts)).down
  let runtime ← runtimeFor branch
  let tree := (← liftOption.{0, 1}
    ((Search.Result.startWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure RuntimeProofConformance.scope branch).toOption)).down
  let controller ← (Runtime.Controller.State.startWithin controllerLimits
    envelope RuntimeProofConformance.measure runtime tree).toOption
  let active ← (RuntimeTerminal.Active.startWithin registry refuteInput controller).toOption
  let lineage ← (active.refuteWithin refuteLimits RuntimeProofConformance.measure
    { node := node 1, version := 0 } refuteKey [1]).toOption
  (lineage.quoteWithin refuteLimits RuntimeProofConformance.measure).toOption

def refuteReplay? : Option
    (Proof.Evidence (RuntimeProofConformance.semantics.Entails refuteInput.program
      (Proof.initialBase refuteInput) refuteInput.target)) := do
  match refuteChecked? with
  | some checked =>
      (checked.replayWithin refuteLimits RuntimeProofConformance.measure
        RuntimeProofConformance.domain RuntimeProofConformance.laws refuteInput).toOption
  | none => none

#guard refuteReplay?.isSome

-- Version zero at node two remains historically resolvable after transport,
-- but is not the exact current version one and is rejected before decoding.
#guard match ordinaryRefuteActive? with
  | some active =>
      (match active.refuteWithin refuteLimits RuntimeProofConformance.measure
          { node := node 2, version := 0 } refuteKey [1] with
        | .error .mismatch => true
        | _ => false) &&
      (match active.refuteWithin refuteLimits RuntimeProofConformance.measure
          { node := node 1, version := 0 } refuteKey [0] with
        | .error (.proof .malformedBody) => true
        | _ => false) &&
      (match active.refuteWithin refuteLimits RuntimeProofConformance.measure
          { node := node 1, version := 0 } refuteKey [1] with
        | .error (.proof .malformedBody) => true
        | _ => false) &&
      (match active.refuteWithin
          { refuteLimits with result :=
            { RuntimeProofConformance.resultLimits with maxBytes := 0 } }
          RuntimeProofConformance.measure { node := node 1, version := 0 }
          refuteKey [1] with
        | .error (.result .malformed) => true
        | _ => false)
  | none => false

#guard match rootChecked? with
  | some checked =>
      match checked.replayWithin RuntimeProofConformance.adapterLimits
          RuntimeProofConformance.measure RuntimeProofConformance.domain
          RuntimeProofConformance.laws refuteInput with
      | .error .mismatch => true
      | _ => false
  | none => false

-- Cross-schema and stale/current-fact substitutions fail before settlement.
#guard match refuteRegistry?, RuntimeProofConformance.assembly?, RuntimeProofConformance.branchWith? refuteInput.facts with
  | some registry, some assembly, some branch =>
      match Runtime.State.startWithin RuntimeProofConformance.runtimeLimits assembly branch with
      | .error _ => false
      | .ok runtime =>
          match Search.Result.startWithin RuntimeProofConformance.resultLimits RuntimeProofConformance.measure RuntimeProofConformance.scope branch with
          | .error _ => false
          | .ok tree =>
              match Runtime.Controller.State.startWithin controllerLimits envelope RuntimeProofConformance.measure
                  runtime tree with
              | .error _ => false
              | .ok controller =>
                  match RuntimeTerminal.Active.startWithin registry refuteInput controller with
                  | .error _ => false
                  | .ok active =>
                      (match active.refuteWithin refuteLimits RuntimeProofConformance.measure
                          { node := node 1, version := 0 }
                          { refuteKey with bodySchema := 0 } [1] with
                        | .error (.proof .missingSchema) => true
                        | _ => false) &&
                      (match active.refuteWithin refuteLimits RuntimeProofConformance.measure
                          { node := node 1, version := 1 } refuteKey [1] with
                        | .error .mismatch => true
                        | _ => false) &&
                      (match active.refuteWithin
                          { refuteLimits with proof :=
                            { refuteProofLimits with maxBodyCells := 0 } }
                          RuntimeProofConformance.measure
                          { node := node 1, version := 0 } refuteKey [1] with
                        | .error (.proof .bodyLimit) => true
                        | _ => false)
  | _, _, _ => false

/-- info: 'Hex.IntervalMathlib.RuntimeTerminalConformance.rootReplay?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms rootReplay?

/-- info: 'Hex.IntervalMathlib.RuntimeTerminalConformance.splitReplay?' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitReplay?

/-- info: 'Hex.IntervalMathlib.RuntimeTerminalConformance.refuteReplay?' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms refuteReplay?

end Hex.IntervalMathlib.RuntimeTerminalConformance
