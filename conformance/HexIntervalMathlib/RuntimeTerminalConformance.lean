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

private def runController
    (state : Runtime.Controller.State Range Nat Nat Proof.Key) :
    Option (Runtime.Controller.State Range Nat Nat Proof.Key) :=
  match Runtime.Controller.runWithin controllerLimits envelope RuntimeProofConformance.measure policy
      [0, 1, 3, 2] state with
  | .ok (.stopped _ state []) => some state
  | _ => none

private def runtimeFor (branch : State.Branch Range Nat) :
    Option (Runtime.State Range Nat) :=
  match RuntimeProofConformance.assembly? with
  | some assembly =>
      (Runtime.State.startWithin RuntimeProofConformance.runtimeLimits assembly branch).toOption
  | none => none

private def startRootController :
    Option (Runtime.Controller.State Range Nat Nat Proof.Key) := do
  let branch := (← liftOption.{0, 1} RuntimeProofConformance.branch?).down
  let runtime ← runtimeFor branch
  let tree := (← liftOption.{0, 1} ((Search.Result.startWithin
    RuntimeProofConformance.resultLimits RuntimeProofConformance.measure
    RuntimeProofConformance.scope branch).toOption)).down
  let state ← (Runtime.Controller.State.startWithin controllerLimits envelope
    RuntimeProofConformance.measure runtime tree).toOption
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
      (match RuntimeTerminal.Active.startWithin registry RuntimeProofConformance.input
          controller with
        | .ok active =>
            match active.targetWithin RuntimeProofConformance.resultLimits
                RuntimeProofConformance.measure { node := node 1, version := 0 } with
            | .error .mismatch => true
            | _ => false
        | _ => false)
  | _, _ => false

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

#print axioms rootReplay?
#print axioms splitReplay?
#print axioms refuteReplay?

end Hex.IntervalMathlib.RuntimeTerminalConformance
