/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Propagator

@[expose] public section

/-!
# Immutable proof-payload arena experiment

A propagator reply uses `PayloadId` values only as reply-local recipe labels.
Before the reply may enter retained solver state, `freeze` checks a bounded
list of immutable recipe drafts, appends them to an arena, and relocates every
payload reference to its fresh arena index.

The arena deliberately stores only replay data and engine-owned provenance.
It cannot contain a propagator cache, a callback, or any other mutable
performance state.  Every failure returns the original arena, so callers may
discard a prospective freeze transaction without rollback.
-/

namespace Hex.Interval.Experiment.PayloadArena

open Propagator

/-- The semantic consumer of one frozen recipe. -/
inductive Role where
  | fact
  | instance
  | equality
  deriving DecidableEq, Repr

/-- One package-produced recipe.  `label` is local to this reply. -/
structure Draft where
  label : PayloadId
  role : Role
  body : List Nat
  deriving Repr

/-- One immutable replay entry.  The rule owner is copied from the originating
action rather than trusted as a second package-supplied identity. -/
structure Entry where
  owner : RuleKey
  origin : Action
  role : Role
  body : List Nat
  deriving Repr

/-- Append-only replay storage.  `bodyCells` is maintained by `freeze`, making
the aggregate body bound independent of later arena size. -/
structure Arena where
  entries : Array Entry
  bodyCells : Nat
  deriving Repr

namespace Arena

/-- The initial empty replay arena. -/
def empty : Arena :=
  { entries := #[], bodyCells := 0 }

/-- Exact optional lookup of a frozen recipe. -/
def entry? (arena : Arena) (payload : PayloadId) : Option Entry :=
  arena.entries[payload.index]?

end Arena

/-- Trusted bounds for the prospective whole arena. -/
structure Limits where
  maxEntries : Nat
  maxBodyCells : Nat
  maxAtom : Nat
  maxUses : Nat
  deriving DecidableEq, Repr

/-- A malformed package recipe set. -/
inductive Invalid where
  | duplicateDraft (label : PayloadId)
  | danglingReference (label : PayloadId)
  | wrongRole (label : PayloadId) (expected actual : Role)
  | extraDraft (label : PayloadId)
  deriving DecidableEq, Repr

/-- A trusted arena limit exhausted before allocation. -/
inductive Resource where
  | entries
  | bodyCells
  | atom
  | uses
  deriving DecidableEq, Repr

/-- Pure result of freezing one outcome.  Failure carries the unchanged arena
to make the transaction boundary executable and testable. -/
inductive Result (Fact : Type) where
  | ready (arena : Arena) (outcome : Outcome Fact)
  | invalid (error : Invalid) (arena : Arena)
  | resourceLimit (resource : Resource) (arena : Arena)

structure Use where
  label : PayloadId
  role : Role

def equalityUses (equality : ProposedEquality) : List Use :=
  [{ label := equality.payload, role := .equality }]

def requestUses (request : InstantiationRequest) : List Use :=
  { label := request.payload, role := .instance } ::
    request.equalities.flatMap equalityUses

def suggestionUses : Suggestion -> List Use
  | .retry _ | .split _ => []
  | .instantiate request => requestUses request

def outcomeUses : Outcome Fact -> List Use
  | .success candidates suggestions _ =>
      candidates.map (fun candidate => { label := candidate.payload, role := .fact }) ++
        suggestions.flatMap suggestionUses
  | .noChange _ | .inapplicable | .resourceLimit _ | .failed _ => []

/-- Bound payload-bearing output structure before `outcomeUses` allocates its
flat list. Repeated references are work even when they share one draft. -/
def consumeCandidates : Nat -> List (Candidate Fact) -> Except Resource Nat
  | remaining, [] => pure remaining
  | 0, _ :: _ => throw .uses
  | remaining + 1, _ :: candidates =>
      consumeCandidates remaining candidates

def consumeEqualities : Nat -> List ProposedEquality -> Except Resource Nat
  | remaining, [] => pure remaining
  | 0, _ :: _ => throw .uses
  | remaining + 1, _ :: equalities =>
      consumeEqualities remaining equalities

def consumeSuggestions : Nat -> List Suggestion -> Except Resource Nat
  | remaining, [] => pure remaining
  | remaining, .retry _ :: suggestions
  | remaining, .split _ :: suggestions =>
      consumeSuggestions remaining suggestions
  | 0, .instantiate _ :: _ => throw .uses
  | remaining + 1, .instantiate request :: suggestions => do
      let remaining ← consumeEqualities remaining request.equalities
      consumeSuggestions remaining suggestions

def preflightUses (limit : Nat) : Outcome Fact -> Except Resource Unit
  | .success candidates suggestions _ => do
      let remaining ← consumeCandidates limit candidates
      let _ ← consumeSuggestions remaining suggestions
      pure ()
  | .noChange _ | .inapplicable | .resourceLimit _ | .failed _ => pure ()

def duplicateDraft? : List Draft -> Option PayloadId
  | [] => none
  | draft :: drafts =>
      if drafts.any (fun other => other.label == draft.label) then some draft.label
      else duplicateDraft? drafts

def findDraft? (label : PayloadId) (drafts : List Draft) : Option Draft :=
  drafts.find? fun draft => draft.label == label

def checkUses (drafts : List Draft) : List Use -> Option Invalid
  | [] => none
  | use :: uses =>
      match findDraft? use.label drafts with
      | none => some (.danglingReference use.label)
      | some draft =>
          if draft.role != use.role then
            some (.wrongRole use.label use.role draft.role)
          else
            checkUses drafts uses

def checkCoverage (uses : List Use) : List Draft -> Option Invalid
  | [] => none
  | draft :: drafts =>
      if uses.any (fun use => use.label == draft.label) then checkCoverage uses drafts
      else some (.extraDraft draft.label)

def validate (uses : List Use) (drafts : List Draft) : Option Invalid :=
  match duplicateDraft? drafts with
  | some label => some (.duplicateDraft label)
  | none =>
      match checkUses drafts uses with
      | some error => some error
      | none => checkCoverage uses drafts

/-- Consume a body-cell budget while checking every encoded recipe atom. -/
def consumeBody (maxAtom : Nat) : Nat -> List Nat -> Except Resource Nat
  | remaining, [] => pure remaining
  | 0, _ :: _ => throw .bodyCells
  | remaining + 1, atom :: atoms =>
      if maxAtom < atom then throw .atom
      else consumeBody maxAtom remaining atoms

def consumeDrafts (maxAtom : Nat) :
    Nat -> List Draft -> Except Resource Nat
  | remaining, [] => pure remaining
  | remaining, draft :: drafts => do
      let remaining ← consumeBody maxAtom remaining draft.body
      consumeDrafts maxAtom remaining drafts

/-- Check aggregate entry and cell limits before constructing any new entry. -/
def preflight (limits : Limits) (arena : Arena) (drafts : List Draft) :
    Except Resource Nat := do
  if limits.maxEntries < arena.entries.size then
    throw .entries
  let entryRoom := limits.maxEntries - arena.entries.size
  if !listWithin entryRoom drafts then
    throw .entries
  if limits.maxBodyCells < arena.bodyCells then
    throw .bodyCells
  let cellRoom := limits.maxBodyCells - arena.bodyCells
  let remaining ← consumeDrafts limits.maxAtom cellRoom drafts
  pure (cellRoom - remaining)

structure Relocation where
  source : PayloadId
  global : PayloadId

def relocationsFrom : Nat -> List Draft -> List Relocation
  | _, [] => []
  | next, draft :: drafts =>
      { source := draft.label, global := { index := next } } ::
        relocationsFrom (next + 1) drafts

def relocateId (relocations : List Relocation) (source : PayloadId) :
    Except Invalid PayloadId :=
  match relocations.find? (fun relocation => relocation.source == source) with
  | some relocation => pure relocation.global
  | none => throw (.danglingReference source)

def relocateCandidate (relocations : List Relocation)
    (candidate : Candidate Fact) : Except Invalid (Candidate Fact) := do
  let payload ← relocateId relocations candidate.payload
  pure { candidate with payload }

def relocateEquality (relocations : List Relocation)
    (equality : ProposedEquality) : Except Invalid ProposedEquality := do
  let payload ← relocateId relocations equality.payload
  pure { equality with payload }

def relocateRequest (relocations : List Relocation)
    (request : InstantiationRequest) : Except Invalid InstantiationRequest := do
  let payload ← relocateId relocations request.payload
  let equalities ← request.equalities.mapM (relocateEquality relocations)
  pure { request with payload, equalities }

def relocateSuggestion (relocations : List Relocation) :
    Suggestion -> Except Invalid Suggestion
  | .retry effort => pure (.retry effort)
  | .split request => pure (.split request)
  | .instantiate request => return .instantiate (← relocateRequest relocations request)

def relocateOutcome (relocations : List Relocation) :
    Outcome Fact -> Except Invalid (Outcome Fact)
  | .success candidates suggestions cost => do
      let candidates ← candidates.mapM (relocateCandidate relocations)
      let suggestions ← suggestions.mapM (relocateSuggestion relocations)
      pure (.success candidates suggestions cost)
  | .noChange cost => pure (.noChange cost)
  | .inapplicable => pure .inapplicable
  | .resourceLimit budget => pure (.resourceLimit budget)
  | .failed code => pure (.failed code)

def appendEntries (arena : Arena) (origin : Action)
    (drafts : List Draft) (addedCells : Nat) : Arena :=
  { entries := drafts.foldl
      (fun entries draft => entries.push
        { owner := origin.key
          origin
          role := draft.role
          body := draft.body })
      arena.entries
    bodyCells := arena.bodyCells + addedCells }

/-- Validate and freeze every reply-local payload reference in an outcome.

This function does not mutate the supplied arena.  A caller should retain the
returned arena only if the surrounding reply transaction also commits. -/
def freeze (limits : Limits) (arena : Arena) (origin : Action)
    (outcome : Outcome Fact) (drafts : List Draft) : Result Fact :=
  match preflightUses limits.maxUses outcome with
  | .error resource => .resourceLimit resource arena
  | .ok _ =>
      let uses := outcomeUses outcome
      match preflight limits arena drafts with
      | .error resource => .resourceLimit resource arena
      | .ok addedCells =>
          match validate uses drafts with
          | some error => .invalid error arena
          | none =>
              let relocations := relocationsFrom arena.entries.size drafts
              match relocateOutcome relocations outcome with
              | .error error => .invalid error arena
              | .ok outcome =>
                  .ready (appendEntries arena origin drafts addedCells) outcome

end Hex.Interval.Experiment.PayloadArena
