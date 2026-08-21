/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.ProofRegistry

@[expose] public section

/-!
# Function-independent tactic frontend data

The compiled engine retains fact and instantiation records in separate arrays
and one compact chronology describing their interleaving.  This module quotes
that state into the three proof-producing event shapes understood by
`ProofEmitter`.  It is parameterized only by the fact type: no operation or
mathematical function is enumerated here.

Quotation checks exact role-local ordering and complete consumption.  The
subsequent proof fold remains responsible for causal availability of facts,
equalities, and program versions; quoted values are plain data, not evidence.
-/

namespace Hex.Interval.Experiment.Frontend

open Propagator PayloadArena SemanticReplay ProofEmitter

/-- Proof-producing events in their authoritative cross-history order. -/
inductive Event (Fact : Type) where
  | instantiation (quote : InstanceQuote)
  | rule (step : RuleStep Fact)
  | transport (step : TransportStep Fact)

/-- A final expression program and its completely quoted proof chronology. -/
structure Trace (Fact : Type) where
  program : Program
  events : List (Event Fact)

/-- Resolve the fact values named by one frozen action from retained history.
This is quotation only; the proof fold must find evidence for the same versions
in its already-established prefix. -/
def resolveFacts? (engine : Engine Fact) (inputs : List SeenVersion) :
    Option (List (NodeFact Fact)) :=
  inputs.mapM fun input => do
    let fact ← engine.toBranch.factAt? input
    pure { node := input.node, fact }

/-- Quote one rule-produced fact record and its immutable payload entry. -/
def ruleStep? (engine : Engine Fact) (arena : Arena)
    (event : Hex.Interval.State.Update Fact (FactCause Fact)) : Option (RuleStep Fact) := do
  let .rule action _ payload := event.cause | none
  let entry ← arena.entry? payload .fact
  let assumptions ← resolveFacts? engine action.inputs
  let previous ← engine.toBranch.factAt? event.previous
  pure { event, payload, entry, assumptions, previous }

/-- Quote one equality-transport fact record, retained edge, and payload. -/
def transportStep? (engine : Engine Fact) (arena : Arena)
    (event : Hex.Interval.State.Update Fact (FactCause Fact)) : Option (TransportStep Fact) := do
  let .transport equality source := event.cause | none
  let edge ← engine.equalities[equality.index]?
  let entry ← arena.entry? edge.payload .equality
  let assumptions ← resolveFacts? engine edge.origin.inputs
  let previous ← engine.toBranch.factAt? event.previous
  let sourceFact ← engine.toBranch.factAt? source
  pure
    { event
      equality
      edge
      payload := edge.payload
      entry
      assumptions
      previous
      sourceFact }

/-- Quote a complete compact chronology.

Indices in each role must be gap-free and increasing, and the final counters
must exhaust both detailed histories.  Cross-role causal checks deliberately
belong to the dependent proof fold, which has the evidence and program state
needed to validate them. -/
def quote? (engine : Engine Fact) (arena : Arena) :
    List Hex.Interval.Trace.Ref → Nat → Nat → Option (List (Event Fact))
  | [], nextFact, nextInstance =>
      if nextFact == engine.history.size &&
          nextInstance == engine.instanceHistory.size then
        some []
      else
        none
  | .instance index :: rest, nextFact, nextInstance => do
      if index != nextInstance then none else pure ()
      let event ← engine.instanceHistory[index]?
      let entry ← arena.entry? event.payload .instance
      let tail ← quote? engine arena rest nextFact (nextInstance + 1)
      pure
        (.instantiation
          { event
            payload := event.payload
            entry } :: tail)
  | .fact index :: rest, nextFact, nextInstance => do
      if index != nextFact then none else pure ()
      let event ← engine.history[index]?
      let head ←
        match event.cause with
        | .rule _ _ _ => (ruleStep? engine arena event).map .rule
        | .transport _ _ => (transportStep? engine arena event).map .transport
      let tail ← quote? engine arena rest (nextFact + 1) nextInstance
      pure (head :: tail)

/-- Quote the engine's retained chronology and final program. -/
def trace? (engine : Engine Fact) (arena : Arena) : Option (Trace Fact) := do
  let events ← quote? engine arena engine.chronology.toList 0 0
  pure { program := engine.program, events }

end Hex.Interval.Experiment.Frontend
