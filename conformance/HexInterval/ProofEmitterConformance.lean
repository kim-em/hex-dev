/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.ProofEmitter
import HexInterval.PolicyFunctionConformance

/-!
This isolated canary quotes a plain trace for the arbitrary-function
contractor from `PolicyFunctionConformance`.  The theorem below is accepted by
ordinary kernel reduction; it does not inspect the opaque compiled session
or rely on a native decision oracle.
-/

namespace Hex.Interval.ProofEmitterConformance

open Experiment Propagator PayloadArena SemanticReplay ChronologicalReplay
open PolicyFunctionConformance

def base : List (NodeFact Rank) :=
  [{ node := node 0, fact := 0 }]

def action : Action :=
  { serial := 1
    programVersion := 1
    application := { index := 1 }
    rule := { index := 1 }
    key := contractKey
    node := node 3
    kind := .improve
    effort := 0
    generation := 1
    inputs := [{ node := node 0, version := 0 }]
    writes := [node 3] }

def entry : Entry :=
  { origin := action
    role := .fact
    schema := 5
    body := [1, 73] }

/-- The value a tactic quotes after running the opaque search.  It contains
only identifiers, facts, and the immutable package certificate body. -/
def quotedStep : ProofEmitter.RuleStep Rank :=
  { event :=
      { programVersion := 1
        node := node 3
        previous := { node := node 3, version := 0 }
        fact := 1
        version := 1
        cause := .rule action 1 { index := 2 } }
    payload := { index := 2 }
    entry
    assumptions := base
    previous := 0 }

/-- The literal is field-for-field semantic data from the real compiled search
run.  This executable comparison is only a regression for the emitter; the
kernel theorem below continues to depend on the literal, not on this Boolean
or on `contracted?`. -/
def quotedMatchesSearch : Bool :=
  match contracted? with
  | none => false
  | some session =>
      match session.state.engine.history[0]?,
          session.arena.entry? quotedStep.payload .fact with
      | some actual, some actualEntry =>
          actual.programVersion == quotedStep.event.programVersion &&
            actual.node == quotedStep.event.node &&
            actual.previous == quotedStep.event.previous &&
            actual.fact == quotedStep.event.fact &&
            actual.version == quotedStep.event.version &&
            actualEntry.origin == quotedStep.entry.origin &&
            actualEntry.role == quotedStep.entry.role &&
            actualEntry.schema == quotedStep.entry.schema &&
            actualEntry.body == quotedStep.entry.body &&
            match actual.cause, quotedStep.event.cause with
            | .rule actualAction actualProposed actualPayload,
                .rule quotedAction quotedProposed quotedPayload =>
                actualAction == quotedAction &&
                  actualProposed == quotedProposed &&
                  actualPayload == quotedPayload
            | _, _ => false
      | _, _ => false

#guard quotedMatchesSearch

def previousSound :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := quotedStep.event.node, fact := quotedStep.previous }) :=
  { proof := by
      intro _ _ _
      exact Or.inl rfl }

def baseEvidence :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 0, fact := 0 }) :=
  ProofEmitter.assumed (by simp [base])

def inputEvidence :
    ProofEmitter.EntailsList functionSemantics extendedProgram base
      quotedStep.assumptions :=
  .cons baseEvidence .nil

def repeatedEvidence :
    ProofEmitter.EntailsList functionSemantics extendedProgram base
      [{ node := node 0, fact := 0 }, { node := node 0, fact := 0 }] :=
  .cons baseEvidence (.cons baseEvidence .nil)

example :
    InputsSound functionSemantics extendedProgram base
      [{ node := node 0, fact := 0 }, { node := node 0, fact := 0 }] :=
  repeatedEvidence.sound.proof

def assumptionsSound :
    Evidence
      (InputsSound functionSemantics extendedProgram base
        quotedStep.assumptions) :=
  inputEvidence.sound

def rankFacts : FactDomainSchema functionSemantics :=
  { top := fun _ => 0
    topSound := by
      intro _ _ _ _ _ _
      exact Or.inl rfl
    proveMeet := fun _ _ previous proposed installed =>
      if previousProof : previous = 0 then
        if proposedProof : proposed = 1 then
          if installedProof : installed = 1 then
            some
              { proof := by
                  subst previous
                  subst proposed
                  subst installed
                  intro _ _
                  constructor
                  · intro installedHolds
                    exact ⟨Or.inl rfl, installedHolds⟩
                  · intro holds
                    exact holds.2 }
          else
            none
        else
          none
      else
        none }

def generatedTop :
    Evidence
      (functionSemantics.Entails extendedProgram base
        { node := node 3, fact := 0 }) :=
  ProofEmitter.topFact rankFacts extendedProgram base (node 3) sinInstruction
    (by rfl)

def replayed :
    Option
      (Evidence
        (functionSemantics.Entails extendedProgram base
          { node := quotedStep.event.node, fact := quotedStep.event.fact })) :=
  ProofEmitter.replayRule factSchema rankFacts checkerInput extendedProgram
    functionPrefix base quotedStep generatedTop assumptionsSound

/-- A malicious emitter cannot make an unauthorized write acceptable by
changing both copies of the frozen action.  This isolates the generic write
check from the separate origin-equality check. -/
def unwritableAction : Action :=
  { action with writes := [] }

def unwritableStep : ProofEmitter.RuleStep Rank :=
  { quotedStep with
    event :=
      { quotedStep.event with
        cause := .rule unwritableAction 1 { index := 2 } }
    entry := { entry with origin := unwritableAction } }

def unwritableReplay :=
  ProofEmitter.replayRule factSchema rankFacts checkerInput extendedProgram
    functionPrefix base unwritableStep
      (by simpa [unwritableStep, quotedStep] using previousSound)
      (by simpa [unwritableStep, quotedStep] using assumptionsSound)

#guard unwritableReplay.isNone

/-- This is the desired downstream interface: an ordinary theorem generated
from a literal trace by transparent proof replay.  `rfl` proves that replay
succeeded, so no external evaluator participates in the proof. -/
theorem quotedTraceProvesContract :
    functionSemantics.Entails extendedProgram base
      { node := node 3, fact := 1 } := by
  simpa [quotedStep] using
    (ProofEmitter.proofOfReplay replayed (by rfl))

end Hex.Interval.ProofEmitterConformance
