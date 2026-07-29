/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PayloadArena

/-!
Focused checks for transactional proof-payload freezing and relocation.
-/

namespace Hex.Interval.PayloadArenaConformance

open Experiment Propagator PayloadArena

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def rule : RuleKey := { name := "payload-arena.test" }

def action (serial : Nat) : Action :=
  { serial
    programVersion := 3
    application := { index := 2 }
    rule := { index := 1 }
    key := rule
    node := node 0
    kind := .forward
    effort := 0
    inputs := [] }

def matcherInputs : List StructuralInput :=
  [{ key := .node (node 4), generation := 2 },
    { key := .equality { index := 3 }, generation := 5 },
    { key := .application { index := 6 }, generation := 7 }]

def matcherAction : Action :=
  { action 12 with
    structuralInputs := matcherInputs
    matcherEpoch := some 9 }

def generous : PayloadArena.Limits :=
  { maxEntries := 16
    maxBodyCells := 32
    maxDrafts := 16
    maxDraftCells := 32
    maxAtom := 100
    maxSchema := 10
    maxUses := 16 }

def factDraft (label : Nat) (body : List Nat := [10]) (schema : Nat := 1) : Draft :=
  { label := payload label, role := .fact, schema, body }

def instanceDraft (label : Nat) (body : List Nat := [20]) (schema : Nat := 2) : Draft :=
  { label := payload label, role := .instance, schema, body }

def equalityDraft (label : Nat) (body : List Nat := [30]) (schema : Nat := 3) : Draft :=
  { label := payload label, role := .equality, schema, body }

def factOutcome (label : Nat) : Outcome Nat :=
  .success [{ node := node 0, fact := 7, payload := payload label }] [] {}

def pairOutcome : Outcome Nat :=
  .success
    [{ node := node 0, fact := 7, payload := payload 0 },
      { node := node 1, fact := 8, payload := payload 1 }]
    [] {}

def retainedSeed : Entry :=
  { origin := action 9
    role := .fact
    schema := 4
    body := [3] }

def seeded : Arena :=
  { entries := #[retainedSeed], bodyCells := 1 }

def seedPreserved (arena : Arena) : Bool :=
  arena.entries.size == 1 && arena.bodyCells == 1 &&
    match arena.entry? (payload 0) .fact with
    | some entry =>
        entry.origin.key == rule && entry.origin.serial == 9 &&
          entry.schema == 4 && entry.body == [3]
    | none => false

#guard seeded.wellFormed
#guard !({ seeded with bodyCells := 0 }).wellFormed

-- Identical local labels in separate replies relocate to distinct global IDs.
#guard
  match freeze generous .empty (action 0) (factOutcome 0) [factDraft 0] with
  | .ready firstArena (.success [first] [] _) =>
      match freeze generous firstArena (action 1) (factOutcome 0) [factDraft 0] with
      | .ready secondArena (.success [second] [] _) =>
          first.payload.index == 0 && second.payload.index == 1 &&
            secondArena.entries.size == 2 && secondArena.bodyCells == 2 &&
            secondArena.wellFormed &&
            (secondArena.entry? second.payload .fact).any fun entry =>
              entry.origin.key == rule && entry.origin.serial == 1 &&
                entry.schema == 1 && entry.body == [10]
      | _ => false
  | _ => false

-- Several uses of one local recipe share its single frozen arena entry.
#guard
  match freeze generous .empty (action 0)
      (.success
        [{ node := node 0, fact := 4, payload := payload 7 },
          { node := node 1, fact := 5, payload := payload 7 }]
        [] {})
      [factDraft 7] with
  | .ready arena (.success [first, second] [] _) =>
      arena.entries.size == 1 && first.payload.index == 0 &&
        second.payload == first.payload
  | _ => false

-- Candidate, instance, and nested equality references are all relocated.
def mixedRequest : InstantiationRequest :=
  { key := 77
    nodes := []
    equalities :=
      [{ left := .existing (node 0)
         right := .existing (node 1)
         payload := payload 9 }]
    scopes :=
      [{ rule
         anchor := .existing (node 1)
         watches := [.existing (node 0)]
         writes := [.existing (node 1)] }]
    payload := payload 4 }

#guard
  match freeze generous .empty (action 0)
      (.success
        [{ node := node 0, fact := 8, payload := payload 7 }]
        [.instantiate mixedRequest] {})
      [equalityDraft 9, factDraft 7, instanceDraft 4] with
  | .ready arena
      (.success [candidate] [.instantiate request] _) =>
      match request.equalities, request.scopes with
      | [equality], [scope] =>
          arena.entries.size == 3 && arena.bodyCells == 3 && arena.wellFormed &&
            candidate.payload.index == 1 && request.payload.index == 2 &&
            equality.payload.index == 0 &&
            scope.rule == rule && scope.anchor == .existing (node 1) &&
            scope.watches == [.existing (node 0)] &&
            scope.writes == [.existing (node 1)] &&
            (arena.entry? equality.payload .equality).any (fun entry =>
              entry.schema == 3 && entry.body == [30]) &&
            (arena.entry? candidate.payload .fact).any (fun entry =>
              entry.schema == 1 && entry.body == [10]) &&
            (arena.entry? request.payload .instance).any (fun entry =>
              entry.schema == 2 && entry.body == [20])
      | _, _ => false
  | _ => false

-- Replay retains exactly the public matcher evidence which caused the reply.
-- Cursor progress remains engine-private because it is absent from `Action`.
#guard
  match freeze generous .empty matcherAction (factOutcome 0) [factDraft 0] with
  | .ready arena (.success [candidate] [] _) =>
      (arena.entry? candidate.payload .fact).any fun entry =>
        entry.origin.structuralInputs == matcherInputs &&
          entry.origin.matcherEpoch == some 9 &&
          entry.origin.serial == 12
  | _ => false

-- Role-checked replay lookup cannot reinterpret a well-formed entry.
#guard
  match freeze generous .empty (action 0) (factOutcome 0) [factDraft 0] with
  | .ready arena (.success [candidate] [] _) =>
      (arena.entry? candidate.payload .fact).isSome &&
        (arena.entry? candidate.payload .equality).isNone &&
        (arena.rawEntry? candidate.payload).isSome
  | _ => false

#guard
  match freeze generous seeded (action 0) (factOutcome 2) [] with
  | .invalid (.danglingReference label) arena =>
      label.index == 2 && seedPreserved arena
  | _ => false

#guard
  match freeze generous seeded (action 0) (factOutcome 0)
      [equalityDraft 0] with
  | .invalid (.wrongRole label .fact .equality) arena =>
      label.index == 0 && seedPreserved arena
  | _ => false

#guard
  match freeze generous seeded (action 0) (factOutcome 0)
      [factDraft 0, factDraft 0 [11]] with
  | .invalid (.duplicateDraft label) arena =>
      label.index == 0 && seedPreserved arena
  | _ => false

#guard
  match freeze generous seeded (action 0) (factOutcome 0)
      [factDraft 0, equalityDraft 1] with
  | .invalid (.extraDraft label) arena =>
      label.index == 1 && seedPreserved arena
  | _ => false

-- Exact draft coverage is checked before remaining whole-run entry capacity:
-- malformed local evidence cannot masquerade as fatal cumulative exhaustion.
#guard
  match freeze { generous with maxEntries := 1 } seeded (action 0)
      (factOutcome 0) [factDraft 0, equalityDraft 1] with
  | .invalid (.extraDraft label) arena =>
      label.index == 1 && seedPreserved arena
  | _ => false

-- The same ordering holds when an unused draft carries a body which would
-- exceed the partly filled arena's remaining cell capacity.
#guard
  match freeze { generous with maxBodyCells := 1 } seeded (action 0)
      (factOutcome 0) [factDraft 0, equalityDraft 1 [4, 5]] with
  | .invalid (.extraDraft label) arena =>
      label.index == 1 && seedPreserved arena
  | _ => false

-- Local preflight derives one cell count from the exact bounded draft list.
-- The same opaque transaction drives both cumulative capacity and the
-- committed aggregate, so there is no independent cell count to mismatch.
#guard
  match
      freeze
        { generous with
          maxEntries := 3
          maxBodyCells := 4
          maxDrafts := 2
          maxDraftCells := 3
          maxUses := 2 }
        seeded (action 0) pairOutcome
        [factDraft 0 [4], factDraft 1 [5, 6]] with
  | .ready arena (.success [first, second] [] _) =>
      first.payload.index == 1 && second.payload.index == 2 &&
        arena.entries.size == 3 && arena.bodyCells == 4 && arena.wellFormed
  | _ => false

-- Reducing only the remaining cumulative cell capacity rejects that same
-- locally bounded transaction and preserves the original cached aggregate.
#guard
  match
      freeze
        { generous with
          maxEntries := 3
          maxBodyCells := 3
          maxDrafts := 2
          maxDraftCells := 3
          maxUses := 2 }
        seeded (action 0) pairOutcome
        [factDraft 0 [4], factDraft 1 [5, 6]] with
  | .resourceLimit .bodyCells arena => seedPreserved arena
  | _ => false

-- Each resource limit is exactly one below the required prospective value.
#guard
  match freeze { generous with maxEntries := 0 } seeded (action 0)
      (.noChange {} : Outcome Nat) [] with
  | .resourceLimit .entries arena => seedPreserved arena
  | _ => false

#guard
  match freeze { generous with maxBodyCells := 0 } seeded (action 0)
      (.noChange {} : Outcome Nat) [] with
  | .resourceLimit .bodyCells arena => seedPreserved arena
  | _ => false

#guard
  match freeze { generous with maxEntries := 1 } seeded (action 0)
      (factOutcome 0) [factDraft 0] with
  | .resourceLimit .entries arena => seedPreserved arena
  | _ => false

#guard
  match freeze { generous with maxBodyCells := 2 } seeded (action 0)
      (factOutcome 0) [factDraft 0 [4, 5]] with
  | .resourceLimit .bodyCells arena => seedPreserved arena
  | _ => false

-- A single oversized recipe is a reply-local failure even though the
-- cumulative arena has room.
#guard
  match freeze { generous with maxDraftCells := 1 } seeded (action 0)
      (factOutcome 0) [factDraft 0 [4, 5]] with
  | .resourceLimit .draftCells arena => seedPreserved arena
  | _ => false

-- The first cell beyond the local cap is still atom-checked before local
-- refusal; whole-run capacity is never consulted for that invalid reply.
#guard
  match freeze
      { generous with maxBodyCells := 1, maxDraftCells := 0, maxAtom := 4 }
      seeded (action 0)
      (factOutcome 0) [factDraft 0 [5]] with
  | .resourceLimit .atom arena => seedPreserved arena
  | _ => false

#guard
  match freeze { generous with maxSchema := 4 } seeded (action 0)
      (factOutcome 0) [factDraft 0 [4] 5] with
  | .resourceLimit .schema arena => seedPreserved arena
  | _ => false

#guard
  match freeze { generous with maxUses := 1 } seeded (action 0)
      (.success
        [{ node := node 0, fact := 4, payload := payload 0 },
          { node := node 1, fact := 5, payload := payload 0 }]
        [] {})
      [factDraft 0] with
  | .resourceLimit .uses arena => seedPreserved arena
  | _ => false

-- Every suggestion constructor consumes the total-proposal budget, including
-- retry and split suggestions which carry no proof payload.
#guard
  match freeze { generous with maxUses := 1 } seeded (action 0)
      (.success [] [.retry 1, .retry 2] {} : Outcome Nat) [] with
  | .resourceLimit .uses arena => seedPreserved arena
  | _ => false

#guard
  match freeze { generous with maxUses := 1 } seeded (action 0)
      (.success []
        [.split { node := node 0, point := 0, reason := .midpoint },
          .split { node := node 0, point := 1, reason := .midpoint }]
        {} : Outcome Nat)
      [] with
  | .resourceLimit .uses arena => seedPreserved arena
  | _ => false

-- Draft count has its own reply-local cap before exact-coverage scans, even
-- when both proposal traversal and the cumulative arena have ample room.
#guard
  match freeze { generous with maxDrafts := 1 } seeded (action 0)
      (factOutcome 0) [factDraft 0, factDraft 1] with
  | .resourceLimit .drafts arena => seedPreserved arena
  | _ => false

-- Nested equalities are charged as payload uses in addition to their
-- containing instantiation suggestion.
#guard
  match freeze { generous with maxUses := 1 } seeded (action 0)
      (.success [] [.instantiate mixedRequest] {} : Outcome Nat)
      [instanceDraft 4, equalityDraft 9] with
  | .resourceLimit .uses arena => seedPreserved arena
  | _ => false

-- Negative outcomes contain no payload uses and therefore accept no drafts.
#guard
  match freeze generous seeded (action 0) (.noChange {} : Outcome Nat) [] with
  | .ready arena (.noChange _) => seedPreserved arena
  | _ => false

#guard
  match freeze generous seeded (action 0) (.resourceLimit 6 : Outcome Nat) [] with
  | .ready arena (.resourceLimit 6) => seedPreserved arena
  | _ => false

#guard
  match freeze generous seeded (action 0) (.inapplicable : Outcome Nat) [factDraft 0] with
  | .invalid (.extraDraft label) arena =>
      label.index == 0 && seedPreserved arena
  | _ => false

#guard
  match freeze generous seeded (action 0) (.failed 8 : Outcome Nat) [factDraft 0] with
  | .invalid (.extraDraft label) arena =>
      label.index == 0 && seedPreserved arena
  | _ => false

end Hex.Interval.PayloadArenaConformance
