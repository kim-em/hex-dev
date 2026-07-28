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

def generous : PayloadArena.Limits :=
  { maxEntries := 16, maxBodyCells := 32, maxAtom := 100, maxUses := 16 }

def factDraft (label : Nat) (body : List Nat := [10]) : Draft :=
  { label := payload label, role := .fact, body }

def instanceDraft (label : Nat) (body : List Nat := [20]) : Draft :=
  { label := payload label, role := .instance, body }

def equalityDraft (label : Nat) (body : List Nat := [30]) : Draft :=
  { label := payload label, role := .equality, body }

def factOutcome (label : Nat) : Outcome Nat :=
  .success [{ node := node 0, fact := 7, payload := payload label }] [] {}

def retainedSeed : Entry :=
  { owner := rule
    origin := action 9
    role := .fact
    body := [3] }

def seeded : Arena :=
  { entries := #[retainedSeed], bodyCells := 1 }

def seedPreserved (arena : Arena) : Bool :=
  arena.entries.size == 1 && arena.bodyCells == 1 &&
    match arena.entry? (payload 0) with
    | some entry =>
        entry.owner == rule && entry.origin.serial == 9 &&
          entry.role == .fact && entry.body == [3]
    | none => false

-- Identical local labels in separate replies relocate to distinct global IDs.
#guard
  match freeze generous .empty (action 0) (factOutcome 0) [factDraft 0] with
  | .ready firstArena (.success [first] [] _) =>
      match freeze generous firstArena (action 1) (factOutcome 0) [factDraft 0] with
      | .ready secondArena (.success [second] [] _) =>
          first.payload.index == 0 && second.payload.index == 1 &&
            secondArena.entries.size == 2 &&
            (secondArena.entry? second.payload).any fun entry =>
              entry.owner == rule && entry.origin.serial == 1 &&
                entry.role == .fact && entry.body == [10]
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
    triggers := [node 0]
    claimedGeneration := 1
    nodes := []
    equalities :=
      [{ left := .existing (node 0)
         right := .existing (node 1)
         payload := payload 9 }]
    payload := payload 4 }

#guard
  match freeze generous .empty (action 0)
      (.success
        [{ node := node 0, fact := 8, payload := payload 7 }]
        [.instantiate mixedRequest] {})
      [equalityDraft 9, factDraft 7, instanceDraft 4] with
  | .ready arena
      (.success [candidate] [.instantiate request] _) =>
      match request.equalities with
      | [equality] =>
          arena.entries.size == 3 && arena.bodyCells == 3 &&
            candidate.payload.index == 1 && request.payload.index == 2 &&
            equality.payload.index == 0
      | _ => false
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

-- Each resource limit is exactly one below the required prospective value.
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

#guard
  match freeze { generous with maxAtom := 4 } seeded (action 0)
      (factOutcome 0) [factDraft 0 [5]] with
  | .resourceLimit .atom arena => seedPreserved arena
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
