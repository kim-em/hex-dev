/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Search

@[expose] public section

/-!
# Autonomous typed runtime controller

This Mathlib-free controller runs the exact applications owned by one sealed
`Runtime.State`. Runtime-owned offer snapshots bind executable tables, the
current branch and equality arena, callback chronology, and reconstructed
actions before Search exposes policy views. A selected policy echo is
authenticated by Search and executed exactly once by `Runtime.State.advanceWithin`;
the same sealed `Runtime.Applied` then advances both the authenticated session
and retained result tree.

The interface deliberately has no target, refutation, split, or unknown
terminal constructor. Exhausting the currently supported offers therefore
requires a policy stop and returns a resumable sealed state; it is not a proof
closure or saturation claim. Only that policy stop returns a successor
`State`. Every resource, callback, Search, result-tree, or alignment error is
all-or-nothing for the whole `runWithin` call: no state constructed earlier in
that call is returned, and the caller retains the immutable initial state. A
pure callback can therefore be replayed on retry; effects outside the returned
Lean value are not transactional. Callback and policy execution, caller
equality, and logical measurement remain non-preemptible.
-/

namespace Hex.Interval.Runtime.Controller

abbrev OfferId := ApplicationId
abbrev SemanticKey := RuleKey

/-- The retained-tree envelope also supplies the exact runtime limits. Search
session and retained-tree search accounting must use the same search limits. -/
structure Limits where
  maxChoices : Nat
  result : Search.Result.Limits
  deriving DecidableEq, Repr

inductive Resource where
  | choices
  deriving DecidableEq, Repr

inductive Error where
  | runtime (error : Runtime.Error)
  | search (error : Search.Error)
  | result (error : Search.Result.Error)
  | resource (resource : Resource)
  | mismatch
  deriving DecidableEq, Repr

/-- Fixed structural policy measure for runtime-owned application/rule keys. -/
def policyMeasure : Policy.Measure OfferId SemanticKey :=
  { id := fun id => { bytes := id.index + 1, pairs := 1, work := 1 }
    key := fun key =>
      { bytes := key.name.length + key.schema + 1, pairs := 1, work := 1 } }

/-- Ordinary-import-sealed live alignment of the typed runtime, authenticated
policy session, retained runtime tree, and cumulative choice accounting. -/
structure State (Fact Cause Plan Schema : Type) where
  private mk ::
  runtime : Runtime.State Fact Cause
  session : Search.Session Fact Cause OfferId SemanticKey
  tree : Search.Result.Tree Fact Cause Plan Schema
  choices : Nat

private def coherent (limits : Limits) (envelope : Search.Envelope) : Bool :=
  envelope.state == limits.result.runtime.executable.state &&
    envelope.search == limits.result.search

/-- Keep universe-polymorphic opaque `Except` results in a small `do` block;
the `ULift` prevents Lean from assigning the bound value to the error
universe while elaborating these public opaque definitions. -/
private def liftExcept.{u, v} {ε : Type u} {α : Type v} (result : Except ε α) :
    Except ε (ULift α) :=
  match result with
  | .error error => .error error
  | .ok value => .ok (ULift.up value)

/-- Start one controller lineage at the exact pending retained-tree source.
The supplied measure validates the retained tree before it enters the state.
The runtime-owned snapshot creates the initial Search session; neither a raw
branch nor executable application table is accepted independently. -/
opaque State.startWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (envelope : Search.Envelope)
    (measure : Search.Result.Measure Fact Cause Plan Schema)
    (runtime : Runtime.State Fact Cause)
    (tree : Search.Result.Tree Fact Cause Plan Schema) :
    Except Error (State Fact Cause Plan Schema) := do
  if !coherent limits envelope then throw .mismatch
  if !tree.check limits.result measure then throw (.result .malformed)
  let some (id, source) := Search.Result.current? tree | throw .mismatch
  let retainedSerial := tree.transitions.foldl (init := 0) fun count entry =>
    if entry.1 == id then count + 1 else count
  let snapshot := (← liftExcept (runtime.offerSnapshotWithin limits.result.runtime
    envelope.policy.maxOffers |>.mapError Error.runtime)).down
  if snapshot.branch != source.branch || snapshot.serial != retainedSerial then throw .mismatch
  let session := (← liftExcept (Search.Session.startRuntimeWithin envelope policyMeasure
    source.scope snapshot |>.mapError Error.search)).down
  pure { runtime, session, tree, choices := 0 }

/-- The typed controller has only an honest resumable policy stop, represented
by its live-offer count. Unsupported proof/search terminals are not
representable at this boundary, and errors return no in-call successor state. -/
inductive Run (Fact Cause Plan Schema PolicyState : Type)
  | stopped (liveOffers : Nat)
      (state : State Fact Cause Plan Schema) (policy : PolicyState)

/-- Run deterministic runtime-owned offer regeneration and replaceable policy
selection until the policy stops or a checked refusal occurs. `maxChoices`
counts accepted select/dismiss decisions, not the final policy stop: after
exactly the cap, the policy may still stop, while one more decision is refused.
Every dismissed live offer marks the session incomplete, regardless of offer
class. Dismissal removes it only from the current snapshot: a later accepted
selection regenerates runtime-owned offers and may make it visible again while
the incompleteness latch remains set.

For selected transition `i`, `chooseWithin`, `prepareWithin`, and the old/new
checks in `Session.advanceRuntimeWithin` perform four complete Search
authentications. If `K_i` offers are live before selection and `K_(i+1)`
afterward, the first three authentications include `Policy.checkOffersWithin`'s
`O(K_i^2)` duplicate scan and the successor authentication includes
`O(K_(i+1)^2)`. Result advancement performs two complete `Tree.check` calls
plus one standalone `computeCost`, so
it makes three complete retained-cost passes. Let `G_i` be successor offer
generation/application scanning, `H_i` the rest of one Search authentication,
`T(N_i,R_i,B_i)` one complete retained-tree check, and `M(N_i,R_i)` one tree
cost pass at node count `N_i`, retained runtime-transition count `R_i`, and
branch cost `B_i`. The first tree check sees `R_i`; the standalone cost pass
and second check see the appended `R_i + 1` successor. The selected-transition
orchestration is bounded by the honest sum
`sum_i (G_i + 3 * (H_i + K_i^2) + H_(i+1) + K_(i+1)^2 +
T(N_i,R_i,B_i) + M(N_i,R_i+1) + T(N_i,R_i+1,B_(i+1)))`.
A dismissal from `K_i` offers separately authenticates the `K_i` entry session
and the `K_i - 1` successor. In particular,
`R_i` grows with accepted selections, so this is not `O(C)` times a fixed tree
cost. Exact callbacks, event folds, caller equality, policy, and measurement
costs are excluded.

The initial retained tree is revalidated under this call's measure before the
policy runs. Only `.stopped` returns the accumulated successor. Any error discards the
entire in-call lineage; the caller still owns the immutable `initial` value and
may replay pure callbacks. Sticky assembly caches and exact event chronology
remain inside the returned runtime state. -/
opaque runWithin [DecidableEq Fact] [DecidableEq Cause]
    [DecidableEq Plan] [DecidableEq Schema]
    (limits : Limits) (envelope : Search.Envelope)
    (measure : Search.Result.Measure Fact Cause Plan Schema)
    (policy : Policy.Interface Fact PolicyState OfferId SemanticKey)
    (policyState : PolicyState) (initial : State Fact Cause Plan Schema) :
    Except Error (Run Fact Cause Plan Schema PolicyState) := do
  if !coherent limits envelope then throw .mismatch
  if !initial.tree.check limits.result measure then throw (.result .malformed)
  let rec loop (fuel : Nat) (state : State Fact Cause Plan Schema)
      (policyState : PolicyState) :
      Except Error (Run Fact Cause Plan Schema PolicyState) := do
    match fuel with
    | 0 => throw (.resource .choices)
    | fuel + 1 =>
      let choice := (← liftExcept (Search.chooseWithin envelope policyMeasure policy policyState
        state.session |>.mapError Error.search)).down
      match choice with
      | .stopped (.policyStop liveOffers) next => pure (.stopped liveOffers state next)
      | .stopped _ _ => throw .mismatch
      | .dismiss decision next =>
          if state.choices >= limits.maxChoices then throw (.resource .choices)
          let offers := state.session.offers.filter fun offer => offer.view.id != decision.id
          if offers.size + 1 != state.session.offers.size then throw .mismatch
          let session := (← liftExcept (Search.Session.refreshWithin envelope policyMeasure
            state.session offers state.session.remaining true |>.mapError Error.search)).down
          loop fuel
            { runtime := state.runtime, session := session, tree := state.tree,
              choices := state.choices + 1 } next
      | .select decision next =>
          if state.choices >= limits.maxChoices then throw (.resource .choices)
          let request := (← liftExcept (Search.prepareWithin envelope policyMeasure
            state.session decision |>.mapError Error.search)).down
          let advanced : Runtime.Advanced Fact Cause ←
            state.runtime.advanceWithin limits.result.runtime envelope.policy.maxOffers
              request.action
              |>.mapError Error.runtime
          let tree := (← liftExcept (Search.Result.advanceRuntimeWithin limits.result measure
            state.tree advanced.transition |>.mapError Error.result)).down
          let session := (← liftExcept (Search.Session.advanceRuntimeWithin envelope
            policyMeasure state.session decision advanced |>.mapError Error.search)).down
          loop fuel
            { runtime := advanced.state, session := session, tree := tree,
              choices := state.choices + 1 } next
  loop (limits.maxChoices + 1) initial policyState

end Hex.Interval.Runtime.Controller
