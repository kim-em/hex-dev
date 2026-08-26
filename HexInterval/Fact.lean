/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Program

@[expose] public section

/-!
# Function-agnostic fact contracts

Facts remain an opaque caller-selected type. The controller owns exact node
versions and supplies packages only immutable, explicitly projected fact
views. Narrowing validates the fact representation and monotone intersection;
it does not authenticate a candidate's mathematical meaning.
-/

namespace Hex.Interval

/-- Exact monotone fact version observed at one program node. -/
structure SeenVersion where
  node : NodeId
  version : Nat
  deriving DecidableEq, Repr

/-- Immutable whole-state fact snapshot. This is controller data, not proof
evidence. Package callbacks receive the narrower `FactView` projection. -/
structure Snapshot (Fact : Type) where
  facts : Array Fact
  versions : Array Nat
  contradictory : Bool

namespace Snapshot

/-- Validate exact fact/version alignment with one checked program. The
contradiction marker remains runtime state and has no evidentiary force. -/
def check (snapshot : Snapshot Fact) (program : Program) : Bool :=
  program.check && snapshot.facts.size == program.nodes.size &&
    snapshot.versions.size == program.nodes.size

/-- Exact optional fact lookup. -/
def fact? (snapshot : Snapshot Fact) (node : NodeId) : Option Fact :=
  snapshot.facts[node.index]?

/-- Exact optional version lookup. -/
def version? (snapshot : Snapshot Fact) (node : NodeId) : Option Nat :=
  snapshot.versions[node.index]?

end Snapshot

/-- One declared rule input. Packages receive these projected views rather
than unrestricted fact state, so every semantic dependency has a watcher. -/
structure FactView (Fact : Type) where
  node : NodeId
  fact : Fact
  version : Nat

/-- Result of intersecting an untrusted candidate with the current strongest
fact. Refusal and malformed input are distinct from contradiction. -/
inductive NarrowResult (Fact : Type) where
  | noChange
  | improved (fact : Fact)
  | contradiction (fact : Fact)
  | malformed (code : Nat)
  | resourceLimit (budget : Nat)

/-- The fact behavior required by the generic controller. `narrow` preserves
the domain's representation and intersection discipline; replay, not this
callback, establishes mathematical soundness. -/
structure FactDomain (Fact : Type) where
  top : DomainId -> Fact
  narrow : DomainId -> Fact -> Fact -> NarrowResult Fact

end Hex.Interval
