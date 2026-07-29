/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PackageRegistry

@[expose] public section

/-!
# Package-owned semantic replay protocol

This module is a proof-side extensibility canary above the immutable payload
format layer.  It deliberately contains no arithmetic expression language and
no enumeration of supported functions.  A semantic package owns the private
certificate type, decoder, and theorem builder for each fact schema.  The
generic registry dispatches only on the exact `(RuleKey, role, schema)` stored
in an immutable payload entry.

This is not yet a complete trace checker.  It fixes the interfaces needed by
that checker without pretending that format validation establishes semantic
soundness.  In particular, rule replay proves the proposed fact, while a
separate fact-domain schema proves that intersecting the previous and proposed
facts produced the installed fact.
-/

namespace Hex.Interval.Experiment.SemanticReplay

open Propagator PayloadArena

/-- A fact tied to the exact expression node it describes. -/
structure NodeFact (Fact : Type) where
  node : NodeId
  fact : Fact

/-- Inputs owned by the caller, rather than reconstructed from an untrusted
trace.  Making this value an explicit parameter of every replay context binds
the base program, version-zero facts, and requested result exactly. -/
structure CheckerInput (Fact : Type) where
  baseProgram : Program
  initialFacts : Array Fact
  target : NodeFact Fact

/-- Function-agnostic mathematical interpretation used by replay.

`Value`, `models`, and `holds` may be instantiated by a Mathlib companion with
typed real semantics.  The protocol does not inspect operation keys or facts.
`models` interprets the complete checked program; `holds` interprets one fact
under one valuation. -/
structure Semantics (Fact : Type) where
  Value : Type
  models : Program -> (NodeId -> Value) -> Prop
  holds : Program -> (NodeId -> Value) -> NodeFact Fact -> Prop

namespace Semantics

/-- Semantic consequence from an exact finite fact context.  Rule schemas
produce this proposition for their proposed fact. -/
def Entails (semantics : Semantics Fact) (program : Program)
    (assumptions : List (NodeFact Fact)) (conclusion : NodeFact Fact) : Prop :=
  ∀ valuation, semantics.models program valuation ->
    (∀ assumption, assumption ∈ assumptions ->
      semantics.holds program valuation assumption) ->
    semantics.holds program valuation conclusion

end Semantics

/-- A proof packaged in `Type`, so a computational checker may return it in
`Option` without moving the proposition itself out of `Prop`. -/
structure Evidence (claim : Prop) : Type where
  proof : claim

/-- Proposition that the caller's program is an exact prefix of the program
being replayed.  A future untrusted trace validator must construct this
witness; schemas may consume it but cannot choose a different base program. -/
structure ProgramPrefix (base extended : Program) : Prop where
  operationSize : base.operations.size ≤ extended.operations.size
  nodeSize : base.nodes.size ≤ extended.nodes.size
  operationAt :
    ∀ index, index < base.operations.size ->
      extended.operations[index]? = base.operations[index]?
  nodeAt :
    ∀ index, index < base.nodes.size ->
      extended.nodes[index]? = base.nodes[index]?

namespace ProgramPrefix

theorem refl (program : Program) : ProgramPrefix program program :=
  { operationSize := Nat.le_refl _
    nodeSize := Nat.le_refl _
    operationAt := fun _ _ => rfl
    nodeAt := fun _ _ => rfl }

end ProgramPrefix

/-- Exact rule context supplied after structural trace validation.  The action
is a type parameter so `dispatchFact` can bind it definitionally to the
payload entry's immutable origin. -/
structure RuleFactContext (input : CheckerInput Fact) (action : Action) where
  program : Program
  basePrefix : ProgramPrefix input.baseProgram program
  assumptions : List (NodeFact Fact)
  proposed : NodeFact Fact

/-- The fact-domain proof boundary is intentionally independent of all
function-rule schemas.  `proveMeet` must establish semantic intersection for
the exact installed fact; merely proving the proposal is insufficient.

Returning a proof in `Option` permits a computational companion checker to
reject malformed facts.  It does not trust the scheduler's `narrow` result. -/
structure FactDomainSchema (semantics : Semantics Fact) where
  top : DomainId -> Fact
  topSound :
    ∀ (program : Program) (valuation : NodeId -> semantics.Value)
      (node : NodeId) (instruction : Node),
      program.node? node = some instruction ->
      semantics.models program valuation ->
      semantics.holds program valuation
        { node, fact := top instruction.domain }
  proveMeet :
    (program : Program) -> (node : NodeId) ->
      (previous proposed installed : Fact) ->
      Option (Evidence
        (∀ valuation, semantics.models program valuation ->
          (semantics.holds program valuation { node, fact := installed } ↔
            semantics.holds program valuation { node, fact := previous } ∧
            semantics.holds program valuation { node, fact := proposed })))

/-- An immutable, existentially packed theorem schema owned by one rule.

`Certificate` disappears behind this structure when schemas from unrelated
packages are placed in the same array.  The decoder and theorem builder are
cache-independent.  In particular, this type has no field capable of
observing a mutable search package or propagator callback. -/
structure PackedFactSchema (semantics : Semantics Fact) where
  rule : RuleKey
  schema : Nat
  Certificate : Type
  decode : List Nat -> Option Certificate
  replay :
    (input : CheckerInput Fact) -> (action : Action) ->
      (context : RuleFactContext input action) -> Certificate ->
      Option (Evidence
        (semantics.Entails context.program context.assumptions context.proposed))

namespace PackedFactSchema

/-- The complete semantic dispatch address. -/
def key (packed : PackedFactSchema semantics) : ReplayKey :=
  { rule := packed.rule, role := .fact, schema := packed.schema }

end PackedFactSchema

/-- Cache-free semantic declarations contributed by one function package.
Package order is the same as in the checked executable registry supplied to
`Registry.build`; this lets assembly reject a theorem schema attributed to a
different package even when both packages reuse the same numeric schema. -/
structure Package (semantics : Semantics Fact) where
  factSchemas : Array (PackedFactSchema semantics)

/-- Exact executable replay declarations covered or deliberately deferred by
the current semantic protocol.  Fact formats have bidirectional coverage:
every key here has exactly one checker.  Instance and equality formats remain
visible rather than being silently treated as checked. -/
structure Coverage where
  factFormats : Array ReplayKey
  deferredFormats : Array ReplayKey
  deriving Repr

/-- Semantic assembly failures retain the exact replay address and package
position; no schema-only or foreign-owner fallback is available. -/
inductive BuildError where
  | packageCount (executable semantic : Nat)
  | duplicateSchema (key : ReplayKey)
  | unownedSchema (package : Nat) (key : ReplayKey)
  | missingSchema (package : Nat) (key : ReplayKey)
  deriving DecidableEq, Repr

/-- Flattened cache-free theorem dispatcher. -/
structure Registry (semantics : Semantics Fact) where
  private mk ::
  factSchemas : Array (PackedFactSchema semantics)
  coverage : Coverage

namespace Registry

private def make (factSchemas : Array (PackedFactSchema semantics))
    (coverage : Coverage) : Registry semantics :=
  { factSchemas, coverage }

private def containsKey (schemas : Array (PackedFactSchema semantics))
    (key : ReplayKey) : Bool :=
  schemas.any fun schema => schema.key == key

private def addSchemas (schemas : Array (PackedFactSchema semantics)) :
    List (PackedFactSchema semantics) ->
      Except BuildError (Array (PackedFactSchema semantics))
  | [] => pure schemas
  | schema :: rest =>
      if containsKey schemas schema.key then
        throw (BuildError.duplicateSchema schema.key)
      else
        addSchemas (schemas.push schema) rest

private def packageCoverage (package : Propagator.Package Fact) : Coverage :=
  package.handlers.foldl
    (fun coverage handler =>
      handler.replayFormats.foldl
        (fun coverage format =>
          let key := format.replayKey handler.registration.key
          if format.role == .fact then
            { coverage with factFormats := coverage.factFormats.push key }
          else
            { coverage with
                deferredFormats := coverage.deferredFormats.push key })
        coverage)
    { factFormats := #[], deferredFormats := #[] }

private def checkOwners (package : Nat) (formats : Array ReplayKey) :
    List (PackedFactSchema semantics) -> Except BuildError PUnit
  | [] => pure ⟨⟩
  | schema :: schemas =>
      if formats.any (fun key => key == schema.key) then
        checkOwners package formats schemas
      else
        throw (.unownedSchema package schema.key)

private def checkCoverage (package : Nat)
    (schemas : Array (PackedFactSchema semantics)) :
    List ReplayKey -> Except BuildError PUnit
  | [] => pure ⟨⟩
  | key :: keys =>
      if containsKey schemas key then
        checkCoverage package schemas keys
      else
        throw (.missingSchema package key)

private def addPackages (index : Nat)
    (schemas : Array (PackedFactSchema semantics)) (coverage : Coverage) :
    List (Propagator.Package Fact) -> List (Package semantics) ->
      Except BuildError (Array (PackedFactSchema semantics) × Coverage)
  | [], [] => pure (schemas, coverage)
  | executable :: executables, package :: packages => do
      let owned := packageCoverage executable
      checkOwners index owned.factFormats package.factSchemas.toList
      checkCoverage index package.factSchemas owned.factFormats.toList
      let schemas ← addSchemas schemas package.factSchemas.toList
      let coverage :=
        { factFormats := coverage.factFormats ++ owned.factFormats
          deferredFormats :=
            coverage.deferredFormats ++ owned.deferredFormats }
      addPackages (index + 1) schemas coverage executables packages
  | executables, packages =>
      throw (.packageCount executables.length packages.length)

/-- Assemble schemas against one checked executable registry without retaining
its mutable package caches.  Package positions establish ownership, exact
`ReplayKey`s establish dispatch, and every executable fact format must have
exactly one checker.  Unsupported instance and equality formats are returned
in `Registry.coverage.deferredFormats`. -/
opaque build (executable : Propagator.Registry Fact)
    (packages : Array (Package semantics)) :
    Except BuildError (Registry semantics) := do
  if executable.packages.size != packages.size then
    throw (.packageCount executable.packages.size packages.size)
  let (factSchemas, coverage) ←
    addPackages 0 #[] { factFormats := #[], deferredFormats := #[] }
      executable.packages.toList packages.toList
  pure (make factSchemas coverage)

def findFact? (registry : Registry semantics) (key : ReplayKey) :
    Option (PackedFactSchema semantics) :=
  registry.factSchemas.toList.find? fun schema => schema.key == key

/-- Decode and replay one immutable fact entry under the exact selected
schema.  Equality and instantiation roles cannot accidentally reach a fact
schema because lookup compares the full replay key.

The context's action is definitionally the entry origin, preventing a caller
from pairing a proof body with a different invocation. -/
def dispatchFact {Fact : Type} {semantics : Semantics Fact}
    (registry : Registry semantics) (input : CheckerInput Fact)
    (entry : Entry) (context : RuleFactContext input entry.origin) :
    Option (Evidence
      (semantics.Entails context.program context.assumptions context.proposed)) :=
  match registry.findFact? entry.replayKey with
  | none => none
  | some packed =>
      match packed.decode entry.body with
      | none => none
      | some certificate =>
          packed.replay input entry.origin context certificate

end Registry

/-! ## Prefix-only access to untrusted trace data -/

/-- Untrusted retained replay data.  The caller-owned base program, initial
facts, and target are intentionally absent; they remain in `CheckerInput`. -/
structure Trace (Fact : Type) where
  program : Program
  events : Array (FactEvent Fact)
  arena : Arena

namespace Trace

/-- Read an event only when its index is strictly before the replay cursor.
Even if the untrusted array contains a future entry, it is inaccessible. -/
def eventAt? (trace : Trace Fact) (cursor index : Nat) : Option (FactEvent Fact) :=
  if index < cursor then trace.events[index]? else none

def findVersionPrefix? (events : Array (FactEvent Fact)) (seen : SeenVersion) :
    Nat -> Nat -> Option Fact
  | 0, _ => none
  | cursor + 1, index =>
      match events[index]? with
      | none => none
      | some event =>
          if event.node == seen.node && event.version == seen.version then
            some event.fact
          else
            findVersionPrefix? events seen cursor (index + 1)

/-- Resolve a positive fact version from a bounded event prefix.  This helper
never falls back to the engine's mutable current fact slot. -/
def eventFactAt? (trace : Trace Fact) (cursor : Nat)
    (seen : SeenVersion) : Option Fact :=
  if seen.version == 0 then none
  else findVersionPrefix? trace.events seen cursor 0

/-- Resolve a fact exactly as replay will: base version zero comes from the
caller's immutable initial facts, generated version zero is semantic top, and
positive versions can inspect only the already-checked event prefix. -/
def factAt? {Fact : Type} {semantics : Semantics Fact}
    (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (trace : Trace Fact)
    (cursor : Nat) (seen : SeenVersion) : Option Fact :=
  if seen.version == 0 then
    if seen.node.index < input.baseProgram.nodes.size then
      input.initialFacts[seen.node.index]?
    else do
      let instruction ← trace.program.node? seen.node
      pure (domain.top instruction.domain)
  else
    trace.eventFactAt? cursor seen

end Trace

/-! ## Deliberate boundary of this canary

A complete checker still has to validate, in one forward pass:

* exact base-prefix preservation and initial-fact length;
* chronological versions, `previous` links, and action-input resolution using
  only the already-checked event prefix;
* package-owned instance and equality schemas for the explicitly deferred
  non-fact `ReplayFormat` declarations, including proof of every appended
  instruction and admitted equality;
* composition of the rule entailment and fact-domain meet evidence into an
  installed-fact theorem; and
* final closure of `CheckerInput.target`.

Those obligations are intentionally not represented by a Boolean labelled
“checked” here.  The next Mathlib vertical should instantiate this protocol
with the existing fixed centered example, while leaving its `Center.Prim` and
`EqRecipe` local rather than promoting either to a central function language.
-/

end Hex.Interval.Experiment.SemanticReplay
