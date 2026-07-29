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

abbrev Key := StructuralKey
abbrev Input := StructuralInput
abbrev Size := MatcherSize
abbrev View := MatcherView
abbrev Cursor := MatcherCursor
abbrev Limits := MatcherLimits
abbrev Error := MatcherError
abbrev Step := MatcherStep

namespace Cursor

def start : View -> Cursor :=
  StructuralCursor.Cursor.start

def exhausted : Cursor -> Bool :=
  StructuralCursor.Cursor.exhausted

def validFor : Cursor -> View -> Bool :=
  StructuralCursor.Cursor.validFor

end Cursor

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

/-- Resolve one offset in the frozen canonical delta stream. -/
def inputAt? (generation? : Key -> Option Nat)
    (cursor : Cursor) (offset : Nat) : Option Input := do
  let nodeCount := cursor.limit.nodes - cursor.base.nodes
  if offset < nodeCount then
    let index := cursor.base.nodes + offset
    let key := StructuralKey.node { index }
    let generation <- generation? key
    return { key, generation }
  let offset := offset - nodeCount
  let equalityCount := cursor.limit.equalities - cursor.base.equalities
  if offset < equalityCount then
    let index := cursor.base.equalities + offset
    let key := StructuralKey.equality { index }
    let generation <- generation? key
    return { key, generation }
  let offset := offset - equalityCount
  let applicationCount := cursor.limit.applications - cursor.base.applications
  if offset < applicationCount then
    let index := cursor.base.applications + offset
    let key := StructuralKey.application { index }
    let generation <- generation? key
    return { key, generation }
  none

/-- Take one deterministic batch from a frozen epoch.  Visit exhaustion is
checked before traversal and leaves the cursor unchanged. -/
def take (generation? : Key -> Option Nat)
    (limits : Limits) (view : View) (cursor : Cursor) : Step :=
  StructuralCursor.take (inputAt? generation?) limits view cursor

/-- Engine-integrated wrapper around the transparent reference enumerator. -/
def Engine.takeMatches (state : Engine Fact) (limits : Limits) (cursor : Cursor) : Step :=
  take (structuralGeneration? state) limits (matcherView state) cursor

/-- Begin a new epoch over exactly the network suffix appended since the old
frozen ceiling.  Renewal before exhaustion, snapshot rollback, or arena shrink
is rejected. -/
def renew (view : View) (cursor : Cursor) : Except Error Cursor := do
  StructuralCursor.renew view cursor

end Hex.Interval.Experiment.Propagator.StructuralMatcher
