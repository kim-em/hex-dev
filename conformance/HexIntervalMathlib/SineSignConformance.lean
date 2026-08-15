/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.TraceReplay
import HexIntervalMathlib.Experiment.SineSign

/-!
This vertical runs the real sine example through the actual proof-producing
session.  The policy first chooses the shape matcher, admits its two auxiliary
expressions, then chooses the independent sine and negation propagators and
the generic equality contractor.  The retained interleaved trace is replayed
against the Mathlib theorem schemas.
-/

namespace Hex.IntervalMathlib.SineSignConformance

open Hex.Interval
open Hex.Interval.Experiment
open Propagator PolicySession SemanticReplay ChronologicalReplay TraceReplay
  ProofRegistry
open SineSign

def offer? (session : PolicySession.Session Range)
    (accepts : Propagator.Policy.OfferView -> Bool) :
    Option
      (Propagator.Policy.OfferView × Propagator.Policy.Selection ×
        PolicySession.Session Range) :=
  match session.view with
  | .ready view viewed =>
      match view.offers.toList.find? accepts with
      | none => none
      | some offer =>
          some
            (offer,
              { scope := view.scope
                serial := view.serial
                programVersion := view.programVersion
                id := offer.id
                expected := offer.key },
              viewed)
  | .resource _ _ | .contradiction _ | .invalidSession _ => none

def invokes (key : RuleKey) (anchor : NodeId)
    (offer : Propagator.Policy.OfferView) : Bool :=
  match offer.key with
  | .invoke invocation => invocation.rule == key && invocation.anchor == anchor
  | _ => false

def instantiatesOddness (offer : Propagator.Policy.OfferView) : Bool :=
  match offer.key with
  | .instantiate source _ => source.rule == oddnessRuleKey
  | _ => false

def firstEquality (offer : Propagator.Policy.OfferView) : Bool :=
  match offer.key with
  | .equality contractor => contractor.equality == ({ index := 0 } : EqualityId)
  | _ => false

def chooseRule? (session : PolicySession.Session Range)
    (key : RuleKey) (anchor : NodeId) :
    Option (PolicySession.Session Range) := do
  let (offer, selection, viewed) <- offer? session (invokes key anchor)
  let .invoke invocation := offer.key | none
  match viewed.choose (.select selection) with
  | .rule _ observation next =>
      if observation.invocation == invocation &&
          observation.outcome == .success then
        some next
      else
        none
  | _ => none

def matched? : Option (PolicySession.Session Range) := do
  let .ok session := start | none
  chooseRule? session oddnessRuleKey (node 2)

def instantiated? : Option (PolicySession.Session Range) := do
  let session <- matched?
  let (_, selection, viewed) <- offer? session instantiatesOddness
  match viewed.choose (.select selection) with
  | .instance _ (.instanceAdmitted [sineNode, negatedSineNode]) next =>
      if sineNode == node 3 && negatedSineNode == node 4 then some next else none
  | _ => none

def sineContracted? : Option (PolicySession.Session Range) := do
  let session <- instantiated?
  chooseRule? session sineRuleKey (node 3)

def negationContracted? : Option (PolicySession.Session Range) := do
  let session <- sineContracted?
  chooseRule? session negationRuleKey (node 4)

def transported? : Option (PolicySession.Session Range) := do
  let session <- negationContracted?
  let (_, selection, viewed) <- offer? session firstEquality
  match viewed.choose (.select selection) with
  | .equality _ observation next =>
      if observation.outcome == .improved then some next else none
  | _ => none

-- The live engine really performs all four distinct stages.  In particular,
-- the target fact is installed by generic equality transport, not directly by
-- either function propagator.
#guard
  transported?.any fun session =>
    session.live && !session.droppedWork &&
      session.state.engine.program == extendedProgram &&
      session.state.engine.facts[2]? == some .nonpositive &&
      session.state.engine.facts[3]? == some .nonnegative &&
      session.state.engine.facts[4]? == some .nonpositive &&
      session.state.engine.instanceHistory.size == 1 &&
      session.state.engine.equalities.size == 1 &&
      session.state.engine.history.size == 3 &&
      session.state.engine.chronology ==
        #[.instance 0, .fact 0, .fact 1, .fact 2] &&
      match session.state.engine.instanceHistory[0]?,
          session.state.engine.equalities[0]?, session.state.engine.history[0]?,
          session.state.engine.history[1]?, session.state.engine.history[2]?,
          session.arena.entry? (payload 0) .instance,
          session.arena.entry? (payload 1) .equality,
          session.arena.entry? (payload 2) .fact,
          session.arena.entry? (payload 3) .fact with
      | some instanceEvent, some edge, some sineEvent, some negationEvent,
          some transportEvent, some instanceEntry, some equalityEntry,
          some sineEntry, some negationEntry =>
          instanceEvent.newNodes == [node 3, node 4] &&
            instanceEvent.payload == payload 0 &&
            instanceEntry.replayKey ==
              { rule := oddnessRuleKey, role := .instance, schema := 1 } &&
            equalityEntry.replayKey ==
              { rule := oddnessRuleKey, role := .equality, schema := 1 } &&
            edge.left == node 2 && edge.right == node 4 &&
              edge.payload == payload 1 &&
            sineEntry.replayKey ==
              { rule := sineRuleKey, role := .fact, schema := 1 } &&
            sineEntry.body == [Range.nonnegative.code] &&
            negationEntry.replayKey ==
              { rule := negationRuleKey, role := .fact, schema := 1 } &&
            negationEntry.body == [Range.nonpositive.code] &&
            sineEvent.node == node 3 && sineEvent.fact == .nonnegative &&
            negationEvent.node == node 4 && negationEvent.fact == .nonpositive &&
            transportEvent.node == node 2 &&
              transportEvent.fact == .nonpositive &&
              match sineEvent.cause, negationEvent.cause,
                  transportEvent.cause with
              | .rule sineAction sineProposed sineProof,
                  .rule negationAction negationProposed negationProof,
                  .transport equality source =>
                    sineAction.key == sineRuleKey &&
                      sineAction.node == node 3 &&
                      sineAction.inputs == [{ node := node 0, version := 0 }] &&
                      sineProposed == .nonnegative && sineProof == payload 2 &&
                      negationAction.key == negationRuleKey &&
                      negationAction.node == node 4 &&
                      negationAction.inputs ==
                        [{ node := node 3, version := 1 }] &&
                      negationProposed == .nonpositive &&
                      negationProof == payload 3 &&
                      equality == ({ index := 0 } : EqualityId) &&
                      source.node == node 4 && source.version == 1
              | _, _, _ => false
      | _, _, _, _, _, _, _, _, _ => false

structure Fixture where
  session : PolicySession.Session Range
  registry : ProofRegistry.Registry semantics Lean.Name

def fixture? : Option Fixture := do
  let session <- transported?
  match ProofRegistry.build session.registry proofPackages with
  | .ok registry => some { session, registry }
  | .error _ => none

def baseStable : StableStep semantics baseProgram baseProgram :=
  { programPrefix := ProgramPrefix.refl baseProgram
    modelsBefore := fun _ model => model
    holdsOld := by
      intro oldValue newValue fact within _ _ agreement
      change Contains fact.fact (oldValue fact.node) ↔
        Contains fact.fact (newValue fact.node)
      rw [agreement fact.node within] }

def buildInstance (before : Program) (_event : InstanceEvent) :
    Option (InstanceStep semantics before) :=
  if beforeEq : before = baseProgram then
    some
      { after := extendedProgram
        stable := by simpa [beforeEq] using stable
        sameOperations := by
          subst before
          simp [baseProgram, extendedProgram] }
  else
    none

def replayed? :
    Option
      (Evidence
        (semantics.Entails checkerInput.baseProgram
          (initialBase checkerInput) checkerInput.target)) :=
  match fixture? with
  | none => none
  | some fixture =>
      let trace :=
        TraceReplay.Trace.ofEngine fixture.session.state.engine
          fixture.session.arena
      TraceReplay.replayInput checkerInput fixture.registry.semantic rangeSchema laws
        buildInstance trace baseStable
        (by simp [checkerInput, baseProgram, node])
        { node := node 2, version := 1 }

-- The complete authoritative trace, including the transport event, passes all
-- structural and package-schema checks and returns proof evidence for the
-- caller's original graph at runtime.
#guard replayed?.isSome

/-- End-user theorem canary.  Separately from the runtime trace guard, this
projects the ordinary emitted combinator chain for the same checked fields and
payload theorem shapes.  It uses neither `native_decide` nor rational
normalization. -/
theorem real_sine_example {x : ℝ} (nonnegative : 0 ≤ x) (atMostOne : x ≤ 1) :
    Real.sin (-x) ≤ 0 :=
  sin_neg_nonpositive nonnegative atMostOne

end Hex.IntervalMathlib.SineSignConformance
