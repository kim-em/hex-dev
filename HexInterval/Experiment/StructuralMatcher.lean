/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Propagator

@[expose] public section

/-!
# Bounded structural matcher cursor

This reference experiment gives the engine, rather than a function package, an
append-stable cursor over the structural objects in one propagation network.
It deliberately uses three linear identifier streams and freezes a snapshot
ceiling for each cursor epoch.  Indexed and compiled matchers can later be
compared against this exact stream without changing its completion or replay
contract.

The package may filter the returned structural inputs and propose arbitrary
expressions, equalities, or scoped propagators.  It cannot claim that
enumeration is complete: exhaustion is derived solely from the engine-owned
cursor.  Network growth during an epoch does not change its frozen suffix;
after exhaustion, renewal exposes exactly the appended delta.
-/

namespace Hex.Interval.Experiment.Propagator.StructuralMatcher

/-- Stable key of one matcher input.  Nodes, equality edges, and concrete
propagator applications have independent append-only identifier spaces. -/
inductive Key where
  | node (node : NodeId)
  | equality (equality : EqualityId)
  | application (application : ApplicationId)
  deriving DecidableEq, Repr

/-- Engine-derived matcher input.  Creation generation participates in causal
generation accounting when the scheduler integration consumes this reference
model. -/
structure Input where
  key : Key
  generation : Nat
  deriving DecidableEq, Repr

/-- Prefix lengths of the three append-only structural arenas. -/
structure Size where
  nodes : Nat := 0
  equalities : Nat := 0
  applications : Nat := 0
  deriving DecidableEq, Repr

def Size.le (left right : Size) : Bool :=
  left.nodes <= right.nodes &&
    left.equalities <= right.equalities &&
      left.applications <= right.applications

def Size.delta (base limit : Size) : Nat :=
  (limit.nodes - base.nodes) +
    (limit.equalities - base.equalities) +
      (limit.applications - base.applications)

/-- Immutable size view used by the reference enumerator.  It contains no
facts, generation arrays, or package metadata, so freezing it is constant
work. -/
structure View where
  programVersion : Nat
  size : Size
  deriving DecidableEq, Repr

/-- Freeze only append-stable arena sizes. -/
def Engine.matcherView (state : Engine Fact) : View :=
  { programVersion := state.programVersion
    size :=
      { nodes := state.generations.size
        equalities := state.equalities.size
        applications := state.applications.size } }

/-- Read one engine-owned creation generation without scanning another arena
entry. -/
def Engine.structuralGeneration? (state : Engine Fact) : Key -> Option Nat
  | .node node => state.generations[node.index]?
  | .equality equality => state.equalities[equality.index]?.map (fun edge => edge.generation)
  | .application application =>
      state.applications[application.index]?.map (fun entry => entry.generation)

/-- Engine-owned continuation for one concrete matcher application.  `base`
is the prefix exhausted by earlier epochs, `limit` is this epoch's frozen
ceiling, and `offset` is a position in the concatenated
node/equality/application delta stream. -/
structure Cursor where
  programVersion : Nat
  base : Size
  limit : Size
  offset : Nat := 0
  epoch : Nat := 0
  visits : Nat := 0
  deriving DecidableEq, Repr

def Cursor.start (view : View) : Cursor :=
  { programVersion := view.programVersion
    base := {}
    limit := view.size }

def Cursor.exhausted (cursor : Cursor) : Bool :=
  cursor.offset == cursor.base.delta cursor.limit

def Cursor.validFor (cursor : Cursor) (view : View) : Bool :=
  cursor.programVersion <= view.programVersion &&
    cursor.base.le cursor.limit &&
      cursor.limit.le view.size &&
        cursor.offset <= cursor.base.delta cursor.limit

/-- Independent matcher traversal limits.  `batchSize` is a yield quantum;
`maxVisits` is cumulative across cursor epochs. -/
structure Limits where
  maxVisits : Nat
  batchSize : Nat
  deriving DecidableEq, Repr

inductive Error where
  | staleSnapshot
  | invalidCursor
  | cursorNotExhausted
  deriving DecidableEq, Repr

/-- Result of one reference matcher step.  Only the engine constructs
`exhausted`; packages receive no completion field to echo. -/
inductive Step where
  | yielded (inputs : Array Input) (cursor : Cursor)
  | exhausted (cursor : Cursor)
  | resourceLimit (cursor : Cursor)
  | invalidCursor
  deriving DecidableEq, Repr

/-- Resolve one offset in the frozen canonical delta stream. -/
def inputAt? (generation? : Key -> Option Nat)
    (cursor : Cursor) (offset : Nat) : Option Input := do
  let nodeCount := cursor.limit.nodes - cursor.base.nodes
  if offset < nodeCount then
    let index := cursor.base.nodes + offset
    let key := Key.node { index }
    let generation <- generation? key
    return { key, generation }
  let offset := offset - nodeCount
  let equalityCount := cursor.limit.equalities - cursor.base.equalities
  if offset < equalityCount then
    let index := cursor.base.equalities + offset
    let key := Key.equality { index }
    let generation <- generation? key
    return { key, generation }
  let offset := offset - equalityCount
  let applicationCount := cursor.limit.applications - cursor.base.applications
  if offset < applicationCount then
    let index := cursor.base.applications + offset
    let key := Key.application { index }
    let generation <- generation? key
    return { key, generation }
  none

/-- Build exactly `count` inputs.  Recursion is on the trusted batch quantum,
so a small step never first traverses a large network. -/
def inputsFromLoop? (generation? : Key -> Option Nat) (cursor : Cursor) :
    Nat -> Nat -> Array Input -> Option (Array Input)
  | _, 0, inputs => some inputs
  | offset, count + 1, inputs => do
      let input <- inputAt? generation? cursor offset
      inputsFromLoop? generation? cursor (offset + 1) count (inputs.push input)

def inputsFrom? (generation? : Key -> Option Nat) (cursor : Cursor)
    (offset count : Nat) : Option (Array Input) :=
  inputsFromLoop? generation? cursor offset count #[]

/-- Take one deterministic batch from a frozen epoch.  Visit exhaustion is
checked before traversal and leaves the cursor unchanged. -/
def take (generation? : Key -> Option Nat)
    (limits : Limits) (view : View) (cursor : Cursor) : Step :=
  if limits.batchSize == 0 then
    .invalidCursor
  else if !cursor.validFor view then
    .invalidCursor
  else
    let total := cursor.base.delta cursor.limit
    if total == cursor.offset then
      .exhausted cursor
    else
      let count := Nat.min limits.batchSize (total - cursor.offset)
      if limits.maxVisits < cursor.visits + count then
        .resourceLimit cursor
      else
        match inputsFrom? generation? cursor cursor.offset count with
        | none => .invalidCursor
        | some inputs =>
            .yielded inputs
              { cursor with
                offset := cursor.offset + count
                visits := cursor.visits + count }

/-- Engine-integrated wrapper around the transparent reference enumerator. -/
def Engine.takeMatches (state : Engine Fact) (limits : Limits) (cursor : Cursor) : Step :=
  take (structuralGeneration? state) limits (matcherView state) cursor

/-- Begin a new epoch over exactly the network suffix appended since the old
frozen ceiling.  Renewal before exhaustion, snapshot rollback, or arena shrink
is rejected. -/
def renew (view : View) (cursor : Cursor) : Except Error Cursor := do
  if view.programVersion < cursor.programVersion then
    throw .staleSnapshot
  if !cursor.validFor view then
    throw .invalidCursor
  if !cursor.exhausted then
    throw .cursorNotExhausted
  if view.size == cursor.limit then
    pure cursor
  else
    pure
      { programVersion := view.programVersion
        base := cursor.limit
        limit := view.size
        offset := 0
        epoch := cursor.epoch + 1
        visits := cursor.visits }

end Hex.Interval.Experiment.Propagator.StructuralMatcher
