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

/-- One package-produced recipe.  `label` is local to this reply, while
`schema` selects the package-owned decoder for the opaque body. -/
structure Draft where
  label : PayloadId
  role : Role
  schema : Nat
  body : List Nat
  deriving Repr

/-- One immutable replay entry.  Its rule owner is always `origin.key`; it is
not stored as a second field which could disagree with the action.

`origin` is safe to copy verbatim because an `Action` contains only
engine-issued identifiers and frozen observations, never a package-produced
reply-local `PayloadId`.  In particular matcher structural inputs and their
epoch are retained here, while the engine-private matcher cursor is not part of
`Action` and cannot enter replay data.  A future payload-bearing action field
must instead be added to the relocation traversal below. -/
structure Entry where
  origin : Action
  role : Role
  schema : Nat
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

/-- Exact optional lookup without checking the recipe's semantic role.  Replay
code should ordinarily use `entry?`; this raw operation is useful to inspect
malformed untrusted certificates. -/
def rawEntry? (arena : Arena) (payload : PayloadId) : Option Entry :=
  arena.entries[payload.index]?

/-- Exact optional lookup which rejects a payload used in the wrong semantic
position. -/
def entry? (arena : Arena) (payload : PayloadId) (expected : Role) : Option Entry := do
  let entry ← arena.rawEntry? payload
  if entry.role == expected then some entry else none

/-- Check the cached aggregate used by the body-cell resource bound.  Callers
must enforce this condition while the standalone experiment exposes `Arena`; a
later session abstraction will own the invariant by construction. -/
def wellFormed (arena : Arena) : Bool :=
  arena.bodyCells ==
    arena.entries.foldl (fun total entry => total + entry.body.length) 0

end Arena

/-- Trusted bounds for the prospective whole arena. -/
structure Limits where
  maxEntries : Nat
  maxBodyCells : Nat
  maxAtom : Nat
  maxSchema : Nat
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
  | schema
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

/-- Traverse every payload-bearing position in one candidate.  The explicit
constructor is intentional: adding another payload field makes this code fail
to compile instead of silently leaving that field unchecked. -/
def traverseCandidate [Monad m] (visit : Role -> PayloadId -> m PayloadId)
    (candidate : Candidate Fact) : m (Candidate Fact) := do
  let payload ← visit .fact candidate.payload
  pure { node := candidate.node, fact := candidate.fact, payload }

def traverseEquality [Monad m] (visit : Role -> PayloadId -> m PayloadId)
    (equality : ProposedEquality) : m ProposedEquality := do
  let payload ← visit .equality equality.payload
  pure { left := equality.left, right := equality.right, payload }

def traverseRequest [Monad m] (visit : Role -> PayloadId -> m PayloadId)
    (request : InstantiationRequest) : m InstantiationRequest := do
  let payload ← visit .instance request.payload
  let equalities ← request.equalities.mapM (traverseEquality visit)
  pure
    { key := request.key
      nodes := request.nodes
      equalities
      scopes := request.scopes
      payload }

def traverseSuggestion [Monad m] (visit : Role -> PayloadId -> m PayloadId) :
    Suggestion -> m Suggestion
  | .retry effort => pure (.retry effort)
  | .instantiate request => return .instantiate (← traverseRequest visit request)
  | .split request =>
      pure (.split
        { node := request.node, point := request.point, reason := request.reason })

/-- The single structural traversal for collecting and relocating payloads.
Explicit reconstruction makes additions to existing payload-bearing records a
compile-time obligation here. -/
def traverseOutcome [Monad m] (visit : Role -> PayloadId -> m PayloadId) :
    Outcome Fact -> m (Outcome Fact)
  | .success candidates suggestions cost => do
      let candidates ← candidates.mapM (traverseCandidate visit)
      let suggestions ← suggestions.mapM (traverseSuggestion visit)
      pure (.success candidates suggestions cost)
  | .noChange cost => pure (.noChange cost)
  | .inapplicable => pure .inapplicable
  | .resourceLimit budget => pure (.resourceLimit budget)
  | .failed code => pure (.failed code)

def recordUse (role : Role) (label : PayloadId) :
    StateM (List Use) PayloadId :=
  fun uses => (label, { label, role } :: uses)

def outcomeUses (outcome : Outcome Fact) : List Use :=
  let (_, reversed) := traverseOutcome recordUse outcome []
  reversed.reverse

/-- Bound the complete top-level proposal structure before `outcomeUses`
allocates its flat payload-use list.  Repeated references are work even when
they share one draft, and suggestions count even when they carry no payload. -/
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
  | 0, _ :: _ => throw .uses
  | remaining + 1, suggestion :: suggestions => do
      let remaining ←
        match suggestion with
        | .retry _ | .split _ => pure remaining
        | .instantiate request => consumeEqualities remaining request.equalities
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

/-- Check aggregate entry, draft-work, schema, and cell limits before
constructing any new entry.  In particular the draft list is bounded by both
remaining arena room and `maxUses` before the quadratic exact-coverage checks
run. -/
def preflight (limits : Limits) (arena : Arena) (drafts : List Draft) :
    Except Resource Nat := do
  if limits.maxEntries < arena.entries.size then
    throw .entries
  let entryRoom := limits.maxEntries - arena.entries.size
  if !listWithin limits.maxUses drafts then
    throw .uses
  if !listWithin entryRoom drafts then
    throw .entries
  if drafts.any (fun draft => limits.maxSchema < draft.schema) then
    throw .schema
  if limits.maxBodyCells < arena.bodyCells then
    throw .bodyCells
  let cellRoom := limits.maxBodyCells - arena.bodyCells
  let remaining ← consumeDrafts limits.maxAtom cellRoom drafts
  pure (cellRoom - remaining)

structure Relocation where
  source : PayloadId
  global : PayloadId

def relocateId (relocations : List Relocation) (source : PayloadId) :
    Except Invalid PayloadId :=
  match relocations.find? (fun relocation => relocation.source == source) with
  | some relocation => pure relocation.global
  | none => throw (.danglingReference source)

def relocateOutcome (relocations : List Relocation) :
    Outcome Fact -> Except Invalid (Outcome Fact) :=
  traverseOutcome fun _ source => relocateId relocations source

/-- Append entries and assign their relocation identifiers in the same
traversal, so the identifier recorded for a draft is definitionally the index
at which that draft's entry is pushed. -/
def appendDrafts (origin : Action) :
    Array Entry -> List Draft -> Array Entry × List Relocation
  | entries, [] => (entries, [])
  | entries, draft :: drafts =>
      let global : PayloadId := { index := entries.size }
      let entry : Entry :=
        { origin
          role := draft.role
          schema := draft.schema
          body := draft.body }
      let (entries, relocations) := appendDrafts origin (entries.push entry) drafts
      (entries, { source := draft.label, global } :: relocations)

def freezeDrafts (arena : Arena) (origin : Action)
    (drafts : List Draft) (addedCells : Nat) : Arena × List Relocation :=
  let (entries, relocations) := appendDrafts origin arena.entries drafts
  ({ entries, bodyCells := arena.bodyCells + addedCells }, relocations)

/-- Validate and freeze every reply-local payload reference in an outcome.

This function does not mutate the supplied arena.  A caller should retain the
returned arena only if the surrounding reply transaction also commits.
Starting from `arena.wellFormed`, every ready result remains well formed.
Callers must supply that precondition until a later session abstraction owns
the arena by construction. -/
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
              let (prospective, relocations) :=
                freezeDrafts arena origin drafts addedCells
              match relocateOutcome relocations outcome with
              | .error error => .invalid error arena
              | .ok outcome =>
                  .ready prospective outcome

end Hex.Interval.Experiment.PayloadArena
