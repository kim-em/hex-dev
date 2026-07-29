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
`schema` selects a package-owned body variant within the originating
`RuleKey.schema` compatibility epoch. -/
structure Draft where
  label : PayloadId
  role : Role
  schema : Nat
  body : List Nat
  deriving Repr

/-- One immutable replay entry.  Its rule owner is always `origin.key`; it is
not stored as a second field which could disagree with the action. -/
structure Entry where
  origin : Action
  role : Role
  schema : Nat
  body : List Nat
  deriving DecidableEq, Repr

/-- The immutable dispatch address for semantic replay.  `rule.schema` is the
handler/theorem compatibility epoch; this structure's numeric `schema` is a
recipe variant local to that exact rule and role.  Dispatch is exact on all
three fields, with no newest-version or schema-only fallback. -/
structure ReplayKey where
  rule : RuleKey
  role : Role
  schema : Nat
  deriving DecidableEq, Repr

namespace Draft

/-- Resolve a reply-local draft's full replay address under its handler. -/
def replayKey (rule : RuleKey) (draft : Draft) : ReplayKey :=
  { rule, role := draft.role, schema := draft.schema }

end Draft

namespace Entry

/-- The full replay address retained by a frozen arena entry. -/
def replayKey (entry : Entry) : ReplayKey :=
  { rule := entry.origin.key, role := entry.role, schema := entry.schema }

end Entry

/-- Append-only replay storage.  `bodyCells` is maintained by `freeze`, making
the aggregate body bound independent of later arena size. -/
structure Arena where
  entries : Array Entry
  bodyCells : Nat
  deriving DecidableEq, Repr

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

/-- Trusted per-reply and whole-run bounds for prospective freezing. -/
structure Limits where
  /-- Cumulative frozen entries retained by the whole run. -/
  maxEntries : Nat
  /-- Cumulative encoded body cells retained by the whole run. -/
  maxBodyCells : Nat
  /-- Drafts supplied by one package reply. -/
  maxDrafts : Nat
  /-- Encoded body cells supplied by one package reply. -/
  maxDraftCells : Nat
  maxAtom : Nat
  maxSchema : Nat
  /-- Payload-bearing proposal positions traversed in one reply. -/
  maxUses : Nat
  deriving DecidableEq, Repr

/-- A malformed package recipe set. -/
inductive Invalid where
  | duplicateDraft (label : PayloadId)
  | danglingReference (label : PayloadId)
  | wrongRole (label : PayloadId) (expected actual : Role)
  | extraDraft (label : PayloadId)
  | wrongOwner (expected actual : RuleKey)
  | undeclaredFormat (key : ReplayKey)
  | invalidBody (key : ReplayKey)
  deriving DecidableEq, Repr

/-- A trusted arena limit exhausted before allocation. -/
inductive Resource where
  /-- The remaining whole-run entry capacity is exhausted. -/
  | entries
  /-- The remaining whole-run body-cell capacity is exhausted. -/
  | bodyCells
  /-- One reply supplied too many drafts. -/
  | drafts
  /-- One reply supplied too many encoded body cells. -/
  | draftCells
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

/-- One exact draft list after reply-local bounds have been checked. Its
private constructor prevents callers from pairing an invented cell count with
different drafts before cumulative preflight or freezing. -/
structure BoundedDrafts where
  private mk ::
  drafts : List Draft
  cells : Nat

def validateDrafts (validateDraft : Draft -> Option Invalid) :
    List Draft -> Option Invalid
  | [] => none
  | draft :: drafts =>
      match validateDraft draft with
      | some error => some error
      | none => validateDrafts validateDraft drafts

/-- Traverse a reply body through the first cell beyond its local budget.
Every visited atom is checked before its cell is charged, so an oversized
boundary atom reports `.atom`. Cells after a `.draftCells` stop are
deliberately not inspected. -/
def consumeBody (maxAtom : Nat) : Nat -> List Nat -> Except Resource Nat
  | remaining, [] => pure remaining
  | remaining, atom :: atoms =>
      if maxAtom < atom then throw .atom
      else
        match remaining with
        | 0 => throw .draftCells
        | remaining + 1 => consumeBody maxAtom remaining atoms

def consumeDrafts (maxAtom : Nat) :
    Nat -> List Draft -> Except Resource Nat
  | remaining, [] => pure remaining
  | remaining, draft :: drafts => do
      let remaining ← consumeBody maxAtom remaining draft.body
      consumeDrafts maxAtom remaining drafts

/-- Check only reply-local draft, schema, atom, and cell bounds. The returned
opaque transaction retains the exact list whose cell count was derived.
Exact draft coverage must still be validated before whole-run capacity is
consulted. -/
opaque preflightLocal (limits : Limits) (drafts : List Draft) :
    Except Resource BoundedDrafts := do
  if !listWithin limits.maxDrafts drafts then
    throw .drafts
  if drafts.any (fun draft => limits.maxSchema < draft.schema) then
    throw .schema
  let remaining ← consumeDrafts limits.maxAtom limits.maxDraftCells drafts
  pure { drafts, cells := limits.maxDraftCells - remaining }

/-- Compare an already locally bounded and exactly validated transaction with
remaining whole-run capacity. Consequently `.entries` and `.bodyCells` mean
genuine cumulative exhaustion by otherwise valid evidence. -/
def preflightWhole (limits : Limits) (arena : Arena)
    (bounded : BoundedDrafts) : Except Resource Unit := do
  if limits.maxEntries < arena.entries.size then
    throw .entries
  let entryRoom := limits.maxEntries - arena.entries.size
  if !listWithin entryRoom bounded.drafts then
    throw .entries
  if limits.maxBodyCells < arena.bodyCells then
    throw .bodyCells
  let cellRoom := limits.maxBodyCells - arena.bodyCells
  if cellRoom < bounded.cells then
    throw .bodyCells
  pure ()

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
    (bounded : BoundedDrafts) : Arena × List Relocation :=
  let (entries, relocations) :=
    appendDrafts origin arena.entries bounded.drafts
  ({ entries, bodyCells := arena.bodyCells + bounded.cells }, relocations)

/-- Low-level validation and freezing with an explicitly supplied rule owner
and draft validator. The package layer pairs those values in one immutable
snapshot before a proof-producing session calls this operation.

Reply-local body and draft bounds and exact coverage are checked before
`validateDraft` runs, so a package validator only receives locally bounded,
structurally relevant inputs. Only structurally and format-valid evidence is
then compared with remaining whole-run capacity. The validator establishes
representation shape only. Semantic replay must decode the same immutable
entry and recheck the rule-specific mathematics.

This function does not mutate the supplied arena. A caller should retain the
returned arena only if the surrounding reply transaction also commits.
Starting from `arena.wellFormed`, every ready result remains well formed.
Direct callers must supply that precondition; the checked session owns a
well-formed arena by construction. -/
def freezeChecked (limits : Limits) (arena : Arena) (origin : Action)
    (owner : RuleKey) (validateDraft : Draft -> Option Invalid)
    (outcome : Outcome Fact) (drafts : List Draft) : Result Fact :=
  if owner != origin.key then
    .invalid (.wrongOwner origin.key owner) arena
  else
    match preflightUses limits.maxUses outcome with
    | .error resource => .resourceLimit resource arena
    | .ok _ =>
        let uses := outcomeUses outcome
        match preflightLocal limits drafts with
        | .error resource => .resourceLimit resource arena
        | .ok bounded =>
            match validate uses bounded.drafts with
            | some error => .invalid error arena
            | none =>
                match validateDrafts validateDraft bounded.drafts with
                | some error => .invalid error arena
                | none =>
                    match preflightWhole limits arena bounded with
                    | .error resource => .resourceLimit resource arena
                    | .ok _ =>
                        let (prospective, relocations) :=
                          freezeDrafts arena origin bounded
                        match relocateOutcome relocations outcome with
                        | .error error => .invalid error arena
                        | .ok outcome =>
                            .ready prospective outcome

/-- Standalone structural freezing with no package format validation.
Proof-producing sessions instead use the package layer's snapshot-paired
wrapper. -/
def freeze (limits : Limits) (arena : Arena) (origin : Action)
    (outcome : Outcome Fact) (drafts : List Draft) : Result Fact :=
  freezeChecked limits arena origin origin.key (fun _ => none) outcome drafts

end Hex.Interval.Experiment.PayloadArena
