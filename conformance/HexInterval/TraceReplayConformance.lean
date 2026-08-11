/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.TraceReplay
import HexInterval.ChronologicalReplayConformance

/-!
The complete trace driver accepts the live arbitrary-function session and
rejects omissions, reorderings, duplicate detail records, premature equality
use, and equality ownership mutations.  The tested propagator remains
package-owned; the driver contains no function cases.  These executable guards
test the opaque runtime checker.  Ordinary kernel proof production is tested
separately through the transparent emitter and the real-function vertical.
-/

namespace Hex.Interval.TraceReplayConformance

open Experiment Propagator SemanticReplay ChronologicalReplay TraceReplay
open PolicyFunctionConformance ChronologicalReplayConformance

/-- Fact locality for the unchanged caller program.  This law belongs to the
semantics adapter because generic `Semantics.holds` may inspect more than the
fact's node value. -/
def functionBaseStable :
    StableStep functionSemantics program program :=
  { programPrefix := ProgramPrefix.refl program
    modelsBefore := fun _ model => model
    holdsOld := by
      intro oldValue newValue fact within _ _ valueProof
      change
        RankAllows fact.fact (oldValue fact.node) ↔
          RankAllows fact.fact (newValue fact.node)
      rw [valueProof fact.node within] }

/-- Reconstruct the one concrete package-generated program snapshot. -/
def buildFunctionStep (before : Program) (_event : InstanceEvent) :
    Option (InstanceStep functionSemantics before) :=
  if beforeProof : before = program then
    some
      { after := extendedProgram
        stable := by
          simpa [beforeProof] using functionStep
        sameOperations := by
          subst before
          simp [extendedProgram, program] }
  else
    none

def replayed? (mutate : TraceReplay.Trace Rank -> TraceReplay.Trace Rank := id) :
    Option
      (Evidence
        (functionSemantics.Entails baseTargetInput.baseProgram
          (initialBase baseTargetInput) baseTargetInput.target)) :=
  match semanticFixture? with
  | none => none
  | some fixture =>
      let trace := mutate <|
        TraceReplay.Trace.ofEngine fixture.session.state.engine
          fixture.session.arena
      let targetWithin :
          baseTargetInput.target.node.index <
            baseTargetInput.baseProgram.nodes.size := by
        simp [baseTargetInput, checkerInput, program, node]
      TraceReplay.replayInput baseTargetInput fixture.registry rankFacts
        functionLaws buildFunctionStep trace (by
          simpa [baseTargetInput, checkerInput] using functionBaseStable)
        targetWithin { node := node 0, version := 0 }

-- The complete live instance/fact interleaving returns proof evidence for the
-- caller's original target.
#guard replayed?.isSome

-- The compact log may neither omit nor duplicate a role-specific record.
#guard
  !(replayed? fun trace => { trace with chronology := #[.instance 0] }).isSome &&
    !(replayed? fun trace =>
      { trace with chronology := #[.instance 0, .fact 0, .fact 0] }).isSome

-- A fact cannot run before the program version and equality prefix introduced
-- by its owning instance are available.
#guard
  !(replayed? fun trace =>
      { trace with chronology := #[.fact 0, .instance 0] }).isSome

/-- Replace the contractor fact with a valid generic transport across the
package-owned oddness equality.  Both endpoint facts are version zero when
the instance has just committed. -/
def equalityTransportTrace (trace : TraceReplay.Trace Rank) :
    TraceReplay.Trace Rank :=
  { trace with
    facts :=
      #[{ programVersion := 1
          node := node 2
          previous := { node := node 2, version := 0 }
          fact := 0
          version := 1
          cause :=
            .transport { index := 0 } { node := node 4, version := 0 } }]
    chronology := #[.instance 0, .fact 0] }

-- Once its exact owner event has run, the same equality identifier resolves
-- to the retained edge and can drive generic fact transport.
#guard (replayed? equalityTransportTrace).isSome

-- Every detailed array must be consumed in append order, exactly once.
#guard
  !(replayed? fun trace =>
      { trace with chronology := #[.instance 0, .fact 1] }).isSome

-- A fresh equality is bound to the exact action and generation which admitted
-- it, even when no subsequent transport happens to use the edge.
#guard
  !(replayed? fun trace =>
      match trace.equalities[0]? with
      | none => trace
      | some edge =>
          { trace with
            equalities := trace.equalities.set! 0
              { edge with
                origin := { edge.origin with serial := edge.origin.serial + 1 } } }).isSome

-- The owner event must name the exact contiguous fresh-equality suffix; the
-- final equality array cannot make an omitted identifier appear retroactively.
#guard
  !(replayed? fun trace =>
      match trace.instances[0]? with
      | none => trace
      | some event =>
          { trace with
            instances := trace.instances.set! 0
              { event with newEqualities := [] } }).isSome

/-- Directly exercise the generic equality-prefix validator, independently of
the package schema used by `replayed?`. -/
def equalityPrefixChecks : Bool :=
  match semanticFixture? with
  | none => false
  | some fixture =>
      let edges := fixture.session.state.engine.equalities
      match fixture.session.state.engine.instanceHistory[0]?, edges[0]? with
      | some event, some edge =>
          nextEqualityCount? extendedProgram edges 0 event == some 1 &&
            (nextEqualityCount? extendedProgram edges 0
              { event with newEqualities := [] }).isNone &&
            (nextEqualityCount? extendedProgram edges 0
              { event with equalities := [] }).isNone &&
            (nextEqualityCount? extendedProgram edges 0
              { event with
                newEqualities := [{ index := 0 }, { index := 0 }] }).isNone &&
            (nextEqualityCount? extendedProgram edges 0
              { event with
                newEqualities := [{ index := 1 }]
                equalities := [{ index := 1 }] }).isNone &&
            (nextEqualityCount? extendedProgram edges 1
              { event with
                newEqualities := []
                equalities := [{ index := 1 }] }).isNone &&
            (nextEqualityCount? extendedProgram
              (edges.set! 0
                { edge with
                  origin := { edge.origin with serial := edge.origin.serial + 1 } })
              0 event).isNone &&
            (nextEqualityCount? extendedProgram
              (edges.set! 0 { edge with generation := edge.generation + 1 })
              0 event).isNone &&
            (nextEqualityCount? extendedProgram
              (edges.set! 0 { edge with right := edge.left }) 0 event).isNone &&
            (nextEqualityCount? mixedProgram
              #[{ edge with left := node 0, right := node 1 }] 0 event).isNone &&
            nextEqualityCount? extendedProgram edges 1
              { event with newEqualities := [] } == some 1
      | _, _ => false

#guard equalityPrefixChecks

/-- Forge a self-consistent owner action whose input is proved only by the
later fact event, updating both arena origins and the edge origin.  Semantic
schema dispatch still matches, so rejection specifically requires the
chronological owner-input check. -/
def futureOwner (trace : TraceReplay.Trace Rank) : TraceReplay.Trace Rank :=
  match trace.instances[0]?, trace.equalities[0]? with
  | some event, some edge =>
      match trace.arena.entries[event.payload.index]?,
          trace.arena.entries[edge.payload.index]? with
      | some instanceEntry, some equalityEntry =>
          let action :=
            { event.origin with
              inputs := [{ node := node 3, version := 1 }] }
          { trace with
            instances := trace.instances.set! 0 { event with origin := action }
            equalities := trace.equalities.set! 0 { edge with origin := action }
            arena :=
              { trace.arena with
                entries :=
                  (trace.arena.entries.set! event.payload.index
                    { instanceEntry with origin := action }).set!
                      edge.payload.index
                      { equalityEntry with origin := action } } }
      | _, _ => trace
  | _, _ => trace

#guard !(replayed? futureOwner).isSome

-- A transport-labelled fact cannot cite an equality before its owner event.
#guard
  !(replayed? fun trace =>
      { equalityTransportTrace trace with
        chronology := #[.fact 0, .instance 0] }).isSome

-- Closure is tied to the retained final program and version, not merely to a
-- prefix whose individual recipes happened to replay.
#guard
  !(replayed? fun trace =>
      { trace with program := program }).isSome &&
    !(replayed? fun trace =>
      { trace with programVersion := trace.programVersion + 1 }).isSome

end Hex.Interval.TraceReplayConformance
