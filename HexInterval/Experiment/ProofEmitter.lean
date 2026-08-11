/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.ChronologicalReplay

@[expose] public section

/-!
# Kernel-facing proof emission

The interval search may be opaque and may run through compiled code.  Its
return value is therefore not itself evidence: the kernel cannot reduce an
opaque search, and a proof recovered from the evaluator would put that
evaluator in the trusted base.

The tactic boundary instead quotes the search output as plain data.  This
module provides transparent replay for the three proof-producing event shapes
a tactic must quote: expression instantiation, a rule fact, and equality
transport.  Each transition selects a package-owned theorem schema supplied
by the caller, checks its replay address and the event's structural links, and
composes the resulting theorem with generic semantic lemmas.

The schemas remain abstract: neither these quote types nor their replay
functions enumerate operations or supported mathematical functions.  A
tactic may emit these applications directly in dependency order or quote a
complete trace for a transparent fold over the same transitions.
-/

namespace Hex.Interval.Experiment.ProofEmitter

open Propagator PayloadArena SemanticReplay ChronologicalReplay

/-- Plain data quoted by the tactic for one rule-caused fact event.

`payload` names the entry copied from the search arena.  Keeping the entry in
the quote, rather than retaining the opaque arena lookup, is what makes the
proof-side reduction independent of the compiled search implementation. -/
structure RuleStep (Fact : Type) where
  event : FactEvent Fact
  payload : PayloadId
  entry : Entry
  assumptions : List (NodeFact Fact)
  previous : Fact

/-- Plain data quoted for one expression-instantiation event. -/
structure InstanceQuote where
  event : InstanceEvent
  payload : PayloadId
  entry : Entry

/-- Plain data quoted for one equality-caused fact improvement. -/
structure TransportStep (Fact : Type) where
  event : FactEvent Fact
  equality : EqualityId
  edge : EqualityEdge
  payload : PayloadId
  entry : Entry
  assumptions : List (NodeFact Fact)
  previous : Fact
  sourceFact : Fact

/-- Transparently replay one quoted expression instantiation and compose its
package-owned conservative-extension theorem with the extension accumulated
for the preceding program prefix. -/
def replayInstance {Fact : Type} {semantics : Semantics Fact}
    (schema : PackedInstanceSchema semantics) (input : CheckerInput Fact)
    (version : Nat) (before after : Program)
    (basePrefix : ProgramPrefix input.baseProgram before)
    (stepPrefix : ProgramPrefix before after)
    (sameOperations : before.operations = after.operations)
    (step : InstanceQuote)
    (previous : Evidence (semantics.Extends input.baseProgram before)) :
    Option (Evidence (semantics.Extends input.baseProgram after)) := do
  if step.event.payload != step.payload ||
      step.event.origin.programVersion != version ||
      step.event.programVersion != version + 1 ||
      step.event.newNodes !=
        Propagator.newNodeIds before.nodes.size after.nodes.size ||
      schema.key != step.entry.replayKey then
    none
  else if originProof : step.event.origin = step.entry.origin then
    let context : InstanceContext input step.entry.origin :=
      { before
        after
        basePrefix
        stepPrefix
        sameOperations
        event := step.event
        origin := originProof }
    let certificate <- schema.decode step.entry.body
    let extension <- schema.replay input step.entry.origin context certificate
    pure (extendTrans basePrefix previous extension)
  else
    none

/-- Transparently replay one quoted rule step.

The caller supplies soundness of facts resolved from the already-replayed
prefix.  The selected schema must match the entry's full `(rule, role,
schema)` address.  Even a malicious emitter cannot manufacture the result:
the only successful branch contains the package schema's proof and the
fact-domain intersection proof, both checked by Lean's kernel. -/
def replayRule {Fact : Type} {semantics : Semantics Fact}
    (schema : PackedFactSchema semantics)
    (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (program : Program)
    (basePrefix : ProgramPrefix input.baseProgram program)
    (base : List (NodeFact Fact)) (step : RuleStep Fact)
    (previousSound :
      Evidence
        (semantics.Entails program base
          { node := step.event.node, fact := step.previous }))
    (assumptionsSound :
      Evidence
        (InputsSound semantics program base step.assumptions)) :
    Option
      (Evidence
        (semantics.Entails program base
          { node := step.event.node, fact := step.event.fact })) :=
  match causeProof : step.event.cause with
  | .transport _ _ => none
  | .rule action proposed payload => do
      if payload != step.payload ||
          action.programVersion != step.event.programVersion ||
          step.event.version != step.event.previous.version + 1 ||
          step.event.previous.node != step.event.node ||
          !action.writes.contains step.event.node ||
          !inputNodesMatch action step.assumptions ||
          schema.key != step.entry.replayKey then
        none
      else if originProof : action = step.entry.origin then
        let context : RuleFactContext input action :=
          { program
            basePrefix
            assumptions := step.assumptions
            proposed := { node := step.event.node, fact := proposed } }
        let certificate ← schema.decode step.entry.body
        let rule ← schema.replay input action context certificate
        let meet ←
          domain.proveMeet program step.event.node step.previous proposed
            step.event.fact
        let exactRule :
            Evidence
              (semantics.Entails program step.assumptions
                { node := step.event.node, fact := proposed }) := by
          simpa using rule
        pure
          (installRule exactRule meet previousSound assumptionsSound)
      else
        none

/-- Transparently replay one equality transport.  The preceding proof terms
must supply the target's previous fact, the exact source fact, and every
conditional equality assumption; an emitted application therefore cannot use
a fact before its proof has appeared in the dependency chain. -/
def replayTransport {Fact : Type} {semantics : Semantics Fact}
    (schema : PackedEqualitySchema semantics)
    (domain : FactDomainSchema semantics) (laws : Laws semantics)
    (input : CheckerInput Fact) (version : Nat) (program : Program)
    (basePrefix : ProgramPrefix input.baseProgram program)
    (base : List (NodeFact Fact)) (step : TransportStep Fact)
    (previousSound :
      Evidence
        (semantics.Entails program base
          { node := step.event.node, fact := step.previous }))
    (sourceSound :
      Evidence
        (semantics.Entails program base
          { node :=
              match step.event.cause with
              | .transport _ source => source.node
              | .rule _ _ _ => step.event.node
            fact := step.sourceFact }))
    (assumptionsSound :
      Evidence (InputsSound semantics program base step.assumptions)) :
    Option
      (Evidence
        (semantics.Entails program base
          { node := step.event.node, fact := step.event.fact })) :=
  match causeProof : step.event.cause with
  | .rule _ _ _ => none
  | .transport equality source => do
      if step.event.programVersion != version ||
          step.event.version != step.event.previous.version + 1 ||
          step.event.previous.node != step.event.node ||
          equality != step.equality ||
          step.edge.payload != step.payload ||
          !inputNodesMatch step.edge.origin step.assumptions ||
          schema.key != step.entry.replayKey then
        none
      else if originProof : step.edge.origin = step.entry.origin then
        let context : EqualityContext input step.entry.origin :=
          { program
            basePrefix
            assumptions := step.assumptions
            equality := step.equality
            edge := step.edge
            origin := originProof }
        let certificate <- schema.decode step.entry.body
        let equalityProof <-
          schema.replay input step.entry.origin context certificate
        let compatible <- sameDomain? program step.edge.left step.edge.right
        if orientation :
            (step.event.node = step.edge.left ∧ source.node = step.edge.right) ∨
              (step.event.node = step.edge.right ∧ source.node = step.edge.left) then
          let meet <-
            domain.proveMeet program step.event.node step.previous
              step.sourceFact step.event.fact
          let exactSource :
              Evidence
                (semantics.Entails program base
                  { node := source.node, fact := step.sourceFact }) := by
            simpa [causeProof] using sourceSound
          pure
            (installTransport laws step.edge compatible orientation equalityProof
              meet previousSound exactSource assumptionsSound)
        else
          none
      else
        none

/-- Project a proposition from any successfully replayed proof object. -/
theorem evidenceOfReplay {P : Prop} (result : Option (Evidence P))
    (success : result.isSome) : P :=
  (result.get success).proof

/-- A successful transparent replay is an ordinary kernel theorem.  This
eliminator is intentionally tiny: the substantial trust argument lives in
`replayRule`; `Option` only represents rejection of malformed quoted data. -/
theorem proofOfReplay {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    {conclusion : NodeFact Fact}
    (result : Option (Evidence (semantics.Entails program base conclusion)))
    (success : result.isSome) :
    semantics.Entails program base conclusion :=
  evidenceOfReplay result success

end Hex.Interval.Experiment.ProofEmitter
