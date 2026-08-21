/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.ChronologicalReplay

@[expose] public section

/-!
# Complete chronological trace replay

This module folds the engine's compact cross-history log.  The log, rather
than either role-specific array, decides when a fact, expression instance, or
equality becomes available.  Every detailed record must occur exactly once
and in append order.

The checker remains independent of a function language.  A semantics adapter
supplies `StableStep` evidence for each concrete program produced by an
instance event; package-owned replay proves the corresponding conservative
extension.  Fact and equality recipes continue to dispatch through the
package registry.
-/

namespace Hex.Interval.Experiment.TraceReplay

open Propagator PayloadArena SemanticReplay ChronologicalReplay

/-- The immutable replay projection of a completed engine session. -/
structure Trace (Fact : Type) where
  programVersion : Nat
  program : Program
  facts : Array (Hex.Interval.State.Update Fact (FactCause Fact))
  instances : Array InstanceEvent
  chronology : Array Hex.Interval.Trace.Ref
  equalities : Array EqualityEdge
  arena : Arena

namespace Trace

/-- Copy only replay-relevant append-only state from an engine.  The payload
arena belongs to the enclosing session and is supplied separately. -/
def ofEngine (engine : Engine Fact) (arena : Arena) : Trace Fact :=
  { programVersion := engine.programVersion
    program := engine.program
    facts := engine.history
    instances := engine.instanceHistory
    chronology := engine.chronology
    equalities := engine.equalities
    arena }

end Trace

/-- A semantics adapter's proof-bearing reconstruction of one concrete
program extension.  `Cursor.replayInstance` independently checks the event's
version and exact fresh-node suffix before accepting this step. -/
structure InstanceStep (semantics : Semantics Fact) (before : Program) where
  after : Program
  stable : StableStep semantics before after
  sameOperations : before.operations = after.operations

/-- Semantics-side callback for reconstructing the next program snapshot.
It may inspect an instance event, but cannot install facts or equalities.

This callback is an experimental seam, not a license for a central switch over
function keys.  The production comparison must either reconstruct the exact
final-program prefix generically and use one semantics-wide stability law, or
dispatch reconstruction through the owning package. -/
abbrev InstanceBuilder (semantics : Semantics Fact) :=
  (before : Program) -> InstanceEvent ->
    Option (InstanceStep semantics before)

/-- Validate the exact equality prefix introduced by one instance.

The event's explicit fresh list must be the gap-free array-order suffix
starting at `available`, every fresh identifier must occur among the outputs,
and no output may refer beyond the resulting prefix.  Fresh retained edges
must be owned by this exact instance action and generation.  Repeated and
reused output identifiers remain valid because outputs preserve proposal
order. -/
def nextEqualityCount? (program : Program) (equalities : Array EqualityEdge)
    (available : Nat) (event : InstanceEvent) : Option Nat := do
  let expectedFresh : List EqualityId :=
    (List.range event.newEqualities.length).map fun offset =>
      { index := available + offset }
  if event.newEqualities != expectedFresh then none else pure ()
  if !event.newEqualities.all event.equalities.contains then none else pure ()
  let next := available + event.newEqualities.length
  if equalities.size < next then none else pure ()
  for identifier in event.equalities do
    if next <= identifier.index then none else pure ()
    let _edge <- equalities[identifier.index]?
  for identifier in event.newEqualities do
    let edge <- equalities[identifier.index]?
    if edge.origin != event.origin || edge.generation != event.generation then
      none
    else
      pure ()
    let left <- program.node? edge.left
    let right <- program.node? edge.right
    if edge.left == edge.right || left.domain != right.domain then none else pure ()
  pure next

/-- Existential chronological state.  The proof cursor and accumulated
stability evidence are indexed by the exact program and version reached so
far. -/
structure State (semantics : Semantics Fact) (input : CheckerInput Fact)
    (base : List (NodeFact Fact)) where
  version : Nat
  program : Program
  cursor : Cursor semantics input base version program
  stable : StableStep semantics input.baseProgram program
  nextFact : Nat
  nextInstance : Nat
  equalityCount : Nat

/-- The caller's version-zero fact array as an exact node-indexed assumption
list. -/
def initialBase (input : CheckerInput Fact) : List (NodeFact Fact) :=
  List.ofFn fun index : Fin input.initialFacts.size =>
    { node := { index := index.val }, fact := input.initialFacts[index] }

/-- Every canonical initial assumption belongs to the caller's base program
when the frontend supplied exactly one fact per node. -/
theorem initialBaseWithin (input : CheckerInput Fact)
    (sizeEq : input.initialFacts.size = input.baseProgram.nodes.size) :
    FactsWithin input.baseProgram (initialBase input) := by
  intro fact member
  rw [initialBase, List.mem_ofFn] at member
  obtain ⟨index, rfl⟩ := member
  simpa [sizeEq] using index.isLt

/-- Construct the initial proof cursor directly from the caller-owned fact
array.  Its semantic proof is simply the corresponding assumption hypothesis;
no arithmetic or domain-specific theorem is involved. -/
def startInput {Fact : Type} (semantics : Semantics Fact)
    (input : CheckerInput Fact)
    (sizeEq : input.initialFacts.size = input.baseProgram.nodes.size) :
    Cursor semantics input (initialBase input) 0 input.baseProgram :=
  Cursor.start <|
    Prefix.start (initialBaseWithin input sizeEq) fun seen _ within =>
      let factWithin : seen.node.index < input.initialFacts.size := by
        simpa [sizeEq] using within
      let index : Fin input.initialFacts.size := ⟨seen.node.index, factWithin⟩
      some
        { fact := input.initialFacts[index]
          within
          sound :=
            { proof := by
                intro valuation model assumptions
                apply assumptions
                  { node := seen.node, fact := input.initialFacts[index] }
                rw [initialBase, List.mem_ofFn]
                exact ⟨index, rfl⟩ } }

/-- Replay one authoritative cross-history entry. -/
def replayEvent {Fact : Type} {semantics : Semantics Fact}
    {input : CheckerInput Fact} {base : List (NodeFact Fact)}
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics) (laws : Laws semantics)
    (buildInstance : InstanceBuilder semantics) (trace : Trace Fact)
    (checked : State semantics input base) (entry : Hex.Interval.Trace.Ref) :
    Option (State semantics input base) := do
  match entry with
  | .fact index =>
      if index != checked.nextFact then none else pure ()
      let event <- trace.facts[index]?
      let next <-
        match event.cause with
        | .rule _ _ _ =>
            Cursor.replayRule checked.cursor registry domain trace.arena event
        | .transport equality _ => do
            if checked.equalityCount <= equality.index then none else pure ()
            let edge <- trace.equalities[equality.index]?
            Cursor.replayTransport checked.cursor registry domain laws trace.arena
              event edge
      pure
        { checked with
          cursor := next
          nextFact := checked.nextFact + 1 }
  | .instance index =>
      if index != checked.nextInstance then none else pure ()
      let event <- trace.instances[index]?
      -- An instance and every equality it owns may depend only on facts which
      -- were already available when the originating action was issued.  It is
      -- too late to validate these inputs when a later transport uses an edge.
      let _ownerInputs <-
        resolveInputs checked.cursor.facts.resolve event.origin.inputs
      let step <- buildInstance checked.program event
      if !step.after.check then none else pure ()
      let equalityCount <-
        nextEqualityCount? step.after trace.equalities checked.equalityCount event
      let next <-
        Cursor.replayInstance checked.cursor registry domain trace.arena event
          step.after step.stable.programPrefix step.sameOperations step.stable
      pure
        { version := event.programVersion
          program := step.after
          cursor := next
          stable := StableStep.trans checked.stable step.stable
          nextFact := checked.nextFact
          nextInstance := checked.nextInstance + 1
          equalityCount }

/-- Fold the complete compact history in its retained order. -/
def replayEvents {Fact : Type} {semantics : Semantics Fact}
    {input : CheckerInput Fact} {base : List (NodeFact Fact)}
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics) (laws : Laws semantics)
    (buildInstance : InstanceBuilder semantics) (trace : Trace Fact) :
    List Hex.Interval.Trace.Ref -> State semantics input base ->
      Option (State semantics input base)
  | [], checked => some checked
  | entry :: entries, checked => do
      let next <-
        replayEvent registry domain laws buildInstance trace checked entry
      replayEvents registry domain laws buildInstance trace entries next

/-- Replay every retained record and close the caller's exact target.

The final checks prevent a compact log from omitting a detailed fact or
instance record, introducing an equality without its owner event, or stopping
at a program/version other than the retained final snapshot. -/
def replay {Fact : Type} {semantics : Semantics Fact}
    {input : CheckerInput Fact} {base : List (NodeFact Fact)}
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics) (laws : Laws semantics)
    (buildInstance : InstanceBuilder semantics) (trace : Trace Fact)
    (started : Cursor semantics input base 0 input.baseProgram)
    (baseStable : StableStep semantics input.baseProgram input.baseProgram)
    (baseWithin : FactsWithin input.baseProgram base)
    (targetWithin : input.target.node.index < input.baseProgram.nodes.size)
    (result : SeenVersion) :
    Option
      (Evidence
        (semantics.Entails input.baseProgram base input.target)) := do
  if !input.baseProgram.check ||
      input.initialFacts.size != input.baseProgram.nodes.size then
    none
  else
    pure ()
  let initial : State semantics input base :=
    { version := 0
      program := input.baseProgram
      cursor := started
      stable := baseStable
      nextFact := 0
      nextInstance := 0
      equalityCount := 0 }
  let checked <-
    replayEvents registry domain laws buildInstance trace
      trace.chronology.toList initial
  if checked.nextFact != trace.facts.size ||
      checked.nextInstance != trace.instances.size ||
      checked.equalityCount != trace.equalities.size ||
      checked.version != trace.programVersion then
    none
  else
    if programEq : checked.program = trace.program then
      let finalCursor :
          Cursor semantics input base checked.version trace.program := by
        simpa [programEq] using checked.cursor
      let finalStable :
          StableStep semantics input.baseProgram trace.program := by
        simpa [programEq] using checked.stable
      Cursor.close finalCursor domain finalStable baseWithin targetWithin result
    else
      none

/-- High-level checker whose assumptions are exactly `CheckerInput.initialFacts`
in node order.  This is the entry point a tactic frontend can use after it has
proved that the requested target node belongs to the original expression
program and supplied the semantics-local stability law. -/
def replayInput {Fact : Type} {semantics : Semantics Fact}
    (input : CheckerInput Fact)
    (registry : SemanticReplay.Registry semantics)
    (domain : FactDomainSchema semantics) (laws : Laws semantics)
    (buildInstance : InstanceBuilder semantics) (trace : Trace Fact)
    (baseStable : StableStep semantics input.baseProgram input.baseProgram)
    (targetWithin : input.target.node.index < input.baseProgram.nodes.size)
    (result : SeenVersion) :
    Option
      (Evidence
        (semantics.Entails input.baseProgram (initialBase input) input.target)) :=
  if sizeEq : input.initialFacts.size = input.baseProgram.nodes.size then
    replay registry domain laws buildInstance trace
      (startInput semantics input sizeEq) baseStable
      (initialBaseWithin input sizeEq) targetWithin result
  else
    none

end Hex.Interval.Experiment.TraceReplay
