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
module is a small canary for one such quoted rule step.  `replayRule` is
transparent, selects a package-owned theorem schema supplied by the caller,
checks the schema's complete replay address and the step's structural links,
and composes the resulting theorem with the fact-domain meet theorem.  A
tactic can emit a term containing the literal `RuleStep` and discharge the
successful `Option` reduction by kernel computation.

The schema remains abstract: neither this trace format nor the replay
function enumerates operations or supported mathematical functions.  A full
emitter will fold the same idea over instance, equality, and fact events in
chronological order.
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

/-- A successful transparent replay is an ordinary kernel theorem.  This
eliminator is intentionally tiny: the substantial trust argument lives in
`replayRule`; `Option` only represents rejection of malformed quoted data. -/
theorem proofOfReplay {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {base : List (NodeFact Fact)}
    {conclusion : NodeFact Fact}
    (result : Option (Evidence (semantics.Entails program base conclusion)))
    (success : result.isSome) :
    semantics.Entails program base conclusion :=
  (result.get success).proof

end Hex.Interval.Experiment.ProofEmitter
