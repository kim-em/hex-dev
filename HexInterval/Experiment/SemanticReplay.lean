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

Format validation does not establish semantic soundness.  Fact schemas prove
proposed facts, instance schemas prove conservative program extension, and
equality schemas prove transport for the exact admitted edge.  A separate
fact-domain schema proves that intersecting the previous and proposed facts
produced the installed fact.
-/

namespace Hex.Interval.Experiment.SemanticReplay

open Propagator PayloadArena

/-- A fact tied to the exact expression node it describes. -/
structure NodeFact (Fact : Type) where
  node : NodeId
  fact : Fact
  deriving DecidableEq

namespace NodeFact

theorem extensionality (left right : NodeFact Fact)
    (node : left.node = right.node) (fact : left.fact = right.fact) :
    left = right := by
  cases left
  cases right
  simp_all

end NodeFact

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
  /-- Fact interpretation is stable when an equality schema proves that two
  expression nodes have the same semantic value. -/
  transport :
    ∀ (program : Program) (valuation : NodeId -> Value)
      (left right : NodeId) (fact : Fact),
      valuation left = valuation right ->
      holds program valuation { node := left, fact } ->
      holds program valuation { node := right, fact }

namespace Semantics

/-- Semantic consequence from an exact finite fact context.  Rule schemas
produce this proposition for their proposed fact. -/
def Entails (semantics : Semantics Fact) (program : Program)
    (assumptions : List (NodeFact Fact)) (conclusion : NodeFact Fact) : Prop :=
  ∀ valuation, semantics.models program valuation ->
    (∀ assumption, assumption ∈ assumptions ->
      semantics.holds program valuation assumption) ->
    semantics.holds program valuation conclusion

/-- A package-owned expression extension is semantically conservative when
every valuation of the old program has a valuation of the new program which
agrees on every old expression node.  An instance schema proves this stronger
property rather than merely acknowledging that an instance payload exists. -/
def Extends (semantics : Semantics Fact) (before after : Program) : Prop :=
  ∀ valuation, semantics.models before valuation ->
    ∃ extended, semantics.models after extended ∧
      ∀ node, node.index < before.nodes.size -> extended node = valuation node

/-- Semantic equality of two nodes in one checked program. -/
def Equivalent (semantics : Semantics Fact) (program : Program)
    (left right : NodeId) : Prop :=
  ∀ valuation, semantics.models program valuation ->
    valuation left = valuation right

end Semantics

/-- A proof packaged in `Type`, so a computational checker may return it in
`Option` without moving the proposition itself out of `Prop`. -/
structure Evidence (claim : Prop) : Type where
  proof : claim

/-- Proposition that the caller's program is an exact prefix of the program
being replayed.  The suffix witnesses make this constructible by a transparent
checker over untrusted arrays; schemas may consume it but cannot choose a
different base program. -/
structure ProgramPrefix (base extended : Program) : Prop where
  operationSuffix :
    ∃ suffix, extended.operations.toList = base.operations.toList ++ suffix
  nodeSuffix :
    ∃ suffix, extended.nodes.toList = base.nodes.toList ++ suffix

namespace ProgramPrefix

theorem refl (program : Program) : ProgramPrefix program program :=
  { operationSuffix := ⟨[], by simp⟩
    nodeSuffix := ⟨[], by simp⟩ }

def suffix? [DecidableEq α] :
    (expected values : List α) ->
      Option { suffix : List α // values = expected ++ suffix }
  | [], values => some ⟨values, rfl⟩
  | _ :: _, [] => none
  | head :: rest, actual :: values =>
      if equal : actual = head then
        match suffix? rest values with
        | none => none
        | some suffix =>
            some
              ⟨suffix, by
                subst actual
                simpa only [List.cons_append] using
                  congrArg (List.cons head) suffix.property⟩
      else
        none

/-- Transparently construct exact prefix evidence from two untrusted program
snapshots. -/
def check? (base extended : Program) :
    Option (Evidence (ProgramPrefix base extended)) :=
  match suffix? base.operations.toList extended.operations.toList with
  | none => none
  | some operations =>
      match suffix? base.nodes.toList extended.nodes.toList with
      | none => none
      | some nodes =>
          some
            { proof :=
                { operationSuffix := ⟨operations, operations.property⟩
                  nodeSuffix := ⟨nodes, nodes.property⟩ } }

end ProgramPrefix

/-- Exact rule context supplied after structural trace validation.  The action
is a type parameter so `dispatchFact` can bind it definitionally to the
payload entry's immutable origin. -/
structure RuleFactContext (input : CheckerInput Fact) (action : Action) where
  program : Program
  basePrefix : ProgramPrefix input.baseProgram program
  assumptions : List (NodeFact Fact)
  proposed : NodeFact Fact

/-- Exact structural context for one admitted instantiation.  The executable
engine supplies the event and the two chronological program snapshots; the
payload entry fixes `action` to the immutable package invocation which
proposed it. -/
structure InstanceContext (input : CheckerInput Fact) (action : Action) where
  before : Program
  after : Program
  basePrefix : ProgramPrefix input.baseProgram before
  event : InstanceEvent

/-- Exact semantic context for transporting one fact over an admitted
equality.  Equality packages prove the transport theorem for the fact domain;
the generic replay loop never interprets either endpoint's function. -/
structure EqualityContext (input : CheckerInput Fact) (action : Action) where
  program : Program
  basePrefix : ProgramPrefix input.baseProgram program
  edge : EqualityEdge

/-- The fact-domain proof boundary is intentionally independent of all
function-rule schemas.  `proveMeet` must establish semantic intersection for
the exact installed fact; merely proving the proposal is insufficient.

Returning a proof in `Option` permits a computational companion checker to
reject malformed facts.  It does not trust the scheduler's `narrow` result. -/
structure FactDomainSchema (semantics : Semantics Fact) where
  top : DomainId -> Fact
  /-- A fact about a modeled old expression node has the same meaning after a
  conservative program extension when the extended model agrees at that node.
  Function packages may add arbitrary new nodes over the program's declared
  operation table; this is the sole generic locality law needed to transport
  caller assumptions and the requested result across those additions. -/
  holdsPrefix :
    ∀ (before after : Program)
      (valuation extended : NodeId -> semantics.Value)
      (fact : NodeFact Fact),
      ProgramPrefix before after ->
      semantics.models before valuation ->
      semantics.models after extended ->
      fact.node.index < before.nodes.size ->
      extended fact.node = valuation fact.node ->
      (semantics.holds before valuation fact ↔
        semantics.holds after extended fact)
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
  /-- Close a requested result from a fact which may be strictly stronger.
  Final replay must not require representation equality with the goal. -/
  proveImplies :
    (program : Program) -> (node : NodeId) ->
      (stronger requested : Fact) ->
      Option (Evidence
        (∀ valuation, semantics.models program valuation ->
          semantics.holds program valuation { node, fact := stronger } ->
          semantics.holds program valuation { node, fact := requested }))

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

/-- An existentially packed, package-owned proof for one expression
instantiation recipe. -/
structure PackedInstanceSchema (semantics : Semantics Fact) where
  rule : RuleKey
  schema : Nat
  Certificate : Type
  decode : List Nat -> Option Certificate
  replay :
    (input : CheckerInput Fact) -> (action : Action) ->
      (context : InstanceContext input action) -> Certificate ->
      Option (Evidence (semantics.Extends context.before context.after))

namespace PackedInstanceSchema

def key (packed : PackedInstanceSchema semantics) : ReplayKey :=
  { rule := packed.rule, role := .instance, schema := packed.schema }

end PackedInstanceSchema

/-- An existentially packed, package-owned proof for one admitted equality
recipe.  Its theorem is the exact transport step used by chronological fact
replay, so equality payload coverage is semantic rather than cosmetic. -/
structure PackedEqualitySchema (semantics : Semantics Fact) where
  rule : RuleKey
  schema : Nat
  Certificate : Type
  decode : List Nat -> Option Certificate
  replay :
    (input : CheckerInput Fact) -> (action : Action) ->
      (context : EqualityContext input action) -> Certificate ->
      Option (Evidence
        (semantics.Equivalent context.program context.edge.left context.edge.right))

namespace PackedEqualitySchema

def key (packed : PackedEqualitySchema semantics) : ReplayKey :=
  { rule := packed.rule, role := .equality, schema := packed.schema }

end PackedEqualitySchema

/-- Cache-free semantic declarations contributed by one function package.
Package order is the same as in the checked executable registry supplied to
`Registry.build`; this lets assembly reject a theorem schema attributed to a
different package even when both packages reuse the same numeric schema. -/
structure Package (semantics : Semantics Fact) where
  factSchemas : Array (PackedFactSchema semantics)
  instanceSchemas : Array (PackedInstanceSchema semantics) := #[]
  equalitySchemas : Array (PackedEqualitySchema semantics) := #[]

/-- Exact executable replay declarations covered by semantic schemas.  Every
key in each role has exactly one package-owned checker. -/
structure Coverage where
  factFormats : Array ReplayKey
  instanceFormats : Array ReplayKey
  equalityFormats : Array ReplayKey
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
  instanceSchemas : Array (PackedInstanceSchema semantics)
  equalitySchemas : Array (PackedEqualitySchema semantics)
  coverage : Coverage

/-- Transparent theorem dispatcher used by kernel replay.  Unlike the sealed
search-paired `Registry`, its constructor need not be a trust boundary:
forging one cannot manufacture any `Evidence`, because every packed schema's
dependent result still has to prove its exact context.  `buildPackages` is the
checked constructor used by the tactic and conformance fixtures. -/
structure KernelRegistry (semantics : Semantics Fact) where
  factSchemas : Array (PackedFactSchema semantics)
  instanceSchemas : Array (PackedInstanceSchema semantics)
  equalitySchemas : Array (PackedEqualitySchema semantics)
  coverage : Coverage

namespace Registry

private def make (factSchemas : Array (PackedFactSchema semantics))
    (instanceSchemas : Array (PackedInstanceSchema semantics))
    (equalitySchemas : Array (PackedEqualitySchema semantics))
    (coverage : Coverage) : Registry semantics :=
  { factSchemas, instanceSchemas, equalitySchemas, coverage }

def containsFactKey (schemas : Array (PackedFactSchema semantics))
    (key : ReplayKey) : Bool :=
  schemas.any fun schema => schema.key == key

def containsInstanceKey
    (schemas : Array (PackedInstanceSchema semantics))
    (key : ReplayKey) : Bool :=
  schemas.any fun schema => schema.key == key

def containsEqualityKey
    (schemas : Array (PackedEqualitySchema semantics))
    (key : ReplayKey) : Bool :=
  schemas.any fun schema => schema.key == key

def addFactSchemas (schemas : Array (PackedFactSchema semantics)) :
    List (PackedFactSchema semantics) ->
      Except BuildError (Array (PackedFactSchema semantics))
  | [] => pure schemas
  | schema :: rest =>
      if containsFactKey schemas schema.key then
        throw (BuildError.duplicateSchema schema.key)
      else
        addFactSchemas (schemas.push schema) rest

def addInstanceSchemas
    (schemas : Array (PackedInstanceSchema semantics)) :
    List (PackedInstanceSchema semantics) ->
      Except BuildError (Array (PackedInstanceSchema semantics))
  | [] => pure schemas
  | schema :: rest =>
      if containsInstanceKey schemas schema.key then
        throw (BuildError.duplicateSchema schema.key)
      else
        addInstanceSchemas (schemas.push schema) rest

def addEqualitySchemas
    (schemas : Array (PackedEqualitySchema semantics)) :
    List (PackedEqualitySchema semantics) ->
      Except BuildError (Array (PackedEqualitySchema semantics))
  | [] => pure schemas
  | schema :: rest =>
      if containsEqualityKey schemas schema.key then
        throw (BuildError.duplicateSchema schema.key)
      else
        addEqualitySchemas (schemas.push schema) rest

def packageCoverage (package : Propagator.Package Fact) : Coverage :=
  package.handlers.foldl
    (fun coverage handler =>
      handler.replayFormats.foldl
        (fun coverage format =>
          let key := format.replayKey handler.registration.key
          match format.role with
          | .fact =>
              { coverage with factFormats := coverage.factFormats.push key }
          | .instance =>
              { coverage with
                  instanceFormats := coverage.instanceFormats.push key }
          | .equality =>
              { coverage with
                  equalityFormats := coverage.equalityFormats.push key })
        coverage)
    { factFormats := #[], instanceFormats := #[], equalityFormats := #[] }

def checkFactOwners (package : Nat) (formats : Array ReplayKey) :
    List (PackedFactSchema semantics) -> Except BuildError PUnit
  | [] => pure ⟨⟩
  | schema :: schemas =>
      if formats.any (fun key => key == schema.key) then
        checkFactOwners package formats schemas
      else
        throw (.unownedSchema package schema.key)

def checkInstanceOwners (package : Nat) (formats : Array ReplayKey) :
    List (PackedInstanceSchema semantics) -> Except BuildError PUnit
  | [] => pure ⟨⟩
  | schema :: schemas =>
      if formats.any (fun key => key == schema.key) then
        checkInstanceOwners package formats schemas
      else
        throw (.unownedSchema package schema.key)

def checkEqualityOwners (package : Nat) (formats : Array ReplayKey) :
    List (PackedEqualitySchema semantics) -> Except BuildError PUnit
  | [] => pure ⟨⟩
  | schema :: schemas =>
      if formats.any (fun key => key == schema.key) then
        checkEqualityOwners package formats schemas
      else
        throw (.unownedSchema package schema.key)

def checkFactCoverage (package : Nat)
    (schemas : Array (PackedFactSchema semantics)) :
    List ReplayKey -> Except BuildError PUnit
  | [] => pure ⟨⟩
  | key :: keys =>
      if containsFactKey schemas key then
        checkFactCoverage package schemas keys
      else
        throw (.missingSchema package key)

def checkInstanceCoverage (package : Nat)
    (schemas : Array (PackedInstanceSchema semantics)) :
    List ReplayKey -> Except BuildError PUnit
  | [] => pure ⟨⟩
  | key :: keys =>
      if containsInstanceKey schemas key then
        checkInstanceCoverage package schemas keys
      else
        throw (.missingSchema package key)

def checkEqualityCoverage (package : Nat)
    (schemas : Array (PackedEqualitySchema semantics)) :
    List ReplayKey -> Except BuildError PUnit
  | [] => pure ⟨⟩
  | key :: keys =>
      if containsEqualityKey schemas key then
        checkEqualityCoverage package schemas keys
      else
        throw (.missingSchema package key)

def addPackages (index : Nat)
    (facts : Array (PackedFactSchema semantics))
    (instances : Array (PackedInstanceSchema semantics))
    (equalities : Array (PackedEqualitySchema semantics))
    (coverage : Coverage) :
    List (Propagator.Package Fact) -> List (Package semantics) ->
      Except BuildError
        (Array (PackedFactSchema semantics) ×
          Array (PackedInstanceSchema semantics) ×
          Array (PackedEqualitySchema semantics) × Coverage)
  | [], [] => pure (facts, instances, equalities, coverage)
  | executable :: executables, package :: packages => do
      let owned := packageCoverage executable
      checkFactOwners index owned.factFormats package.factSchemas.toList
      checkInstanceOwners index owned.instanceFormats package.instanceSchemas.toList
      checkEqualityOwners index owned.equalityFormats package.equalitySchemas.toList
      checkFactCoverage index package.factSchemas owned.factFormats.toList
      checkInstanceCoverage index package.instanceSchemas owned.instanceFormats.toList
      checkEqualityCoverage index package.equalitySchemas owned.equalityFormats.toList
      let facts ← addFactSchemas facts package.factSchemas.toList
      let instances ← addInstanceSchemas instances package.instanceSchemas.toList
      let equalities ← addEqualitySchemas equalities package.equalitySchemas.toList
      let coverage :=
        { factFormats := coverage.factFormats ++ owned.factFormats
          instanceFormats := coverage.instanceFormats ++ owned.instanceFormats
          equalityFormats := coverage.equalityFormats ++ owned.equalityFormats }
      addPackages (index + 1) facts instances equalities coverage
        executables packages
  | executables, packages =>
      throw (.packageCount executables.length packages.length)

/-- Transparent semantic assembly directly against the immutable executable
package declarations.  This is the kernel-replay entry point: opaque compiled
search registries are deliberately not a soundness dependency. -/
def buildPackages (executable : Array (Propagator.Package Fact))
    (packages : Array (Package semantics)) :
    Except BuildError (KernelRegistry semantics) := do
  if executable.size != packages.size then
    throw (.packageCount executable.size packages.size)
  let (factSchemas, instanceSchemas, equalitySchemas, coverage) ←
    addPackages 0 #[] #[] #[]
      { factFormats := #[], instanceFormats := #[], equalityFormats := #[] }
      executable.toList packages.toList
  pure { factSchemas, instanceSchemas, equalitySchemas, coverage }

/-- Assemble schemas against one checked executable registry without retaining
its mutable package caches.  Package positions establish ownership, exact
`ReplayKey`s establish dispatch, and every executable format in every role
must have exactly one checker. -/
opaque build (executable : Propagator.Registry Fact)
    (packages : Array (Package semantics)) :
    Except BuildError (Registry semantics) := do
  if executable.packages.size != packages.size then
    throw (.packageCount executable.packages.size packages.size)
  let (factSchemas, instanceSchemas, equalitySchemas, coverage) ←
    addPackages 0 #[] #[] #[]
      { factFormats := #[], instanceFormats := #[], equalityFormats := #[] }
      executable.packages.toList packages.toList
  pure (make factSchemas instanceSchemas equalitySchemas coverage)

def findFact? (registry : Registry semantics) (key : ReplayKey) :
    Option (PackedFactSchema semantics) :=
  registry.factSchemas.toList.find? fun schema => schema.key == key

def findInstance? (registry : Registry semantics) (key : ReplayKey) :
    Option (PackedInstanceSchema semantics) :=
  registry.instanceSchemas.toList.find? fun schema => schema.key == key

def findEquality? (registry : Registry semantics) (key : ReplayKey) :
    Option (PackedEqualitySchema semantics) :=
  registry.equalitySchemas.toList.find? fun schema => schema.key == key

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

/-- Decode and replay one exact instance entry. -/
def dispatchInstance {Fact : Type} {semantics : Semantics Fact}
    (registry : Registry semantics) (input : CheckerInput Fact)
    (entry : Entry) (context : InstanceContext input entry.origin) :
    Option (Evidence (semantics.Extends context.before context.after)) :=
  match registry.findInstance? entry.replayKey with
  | none => none
  | some packed =>
      match packed.decode entry.body with
      | none => none
      | some certificate =>
          packed.replay input entry.origin context certificate

/-- Decode and replay one exact equality entry. -/
def dispatchEquality {Fact : Type} {semantics : Semantics Fact}
    (registry : Registry semantics) (input : CheckerInput Fact)
    (entry : Entry) (context : EqualityContext input entry.origin) :
    Option (Evidence
      (semantics.Equivalent context.program context.edge.left context.edge.right)) :=
  match registry.findEquality? entry.replayKey with
  | none => none
  | some packed =>
      match packed.decode entry.body with
      | none => none
      | some certificate =>
          packed.replay input entry.origin context certificate

end Registry

namespace KernelRegistry

def findFact? (registry : KernelRegistry semantics) (key : ReplayKey) :
    Option (PackedFactSchema semantics) :=
  registry.factSchemas.toList.find? fun schema => schema.key == key

def findInstance? (registry : KernelRegistry semantics) (key : ReplayKey) :
    Option (PackedInstanceSchema semantics) :=
  registry.instanceSchemas.toList.find? fun schema => schema.key == key

def findEquality? (registry : KernelRegistry semantics) (key : ReplayKey) :
    Option (PackedEqualitySchema semantics) :=
  registry.equalitySchemas.toList.find? fun schema => schema.key == key

def dispatchFact {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (input : CheckerInput Fact)
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

def dispatchInstance {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (input : CheckerInput Fact)
    (entry : Entry) (context : InstanceContext input entry.origin) :
    Option (Evidence (semantics.Extends context.before context.after)) :=
  match registry.findInstance? entry.replayKey with
  | none => none
  | some packed =>
      match packed.decode entry.body with
      | none => none
      | some certificate =>
          packed.replay input entry.origin context certificate

def dispatchEquality {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (input : CheckerInput Fact)
    (entry : Entry) (context : EqualityContext input entry.origin) :
    Option (Evidence
      (semantics.Equivalent context.program context.edge.left context.edge.right)) :=
  match registry.findEquality? entry.replayKey with
  | none => none
  | some packed =>
      match packed.decode entry.body with
      | none => none
      | some certificate =>
          packed.replay input entry.origin context certificate

end KernelRegistry

/-! ## Prefix-only access to untrusted trace data -/

/-- Untrusted retained replay data.  The caller-owned base program, initial
facts, and target are intentionally absent; they remain in `CheckerInput`. -/
structure Trace (Fact : Type) where
  program : Program
  /-- Program snapshots in chronological order, including the caller's base
  program at index zero and `program` as the final entry. -/
  programs : Array Program := #[]
  instances : Array InstanceEvent := #[]
  equalities : Array EqualityEdge := #[]
  events : Array (FactEvent Fact)
  arena : Arena

/-! ## Transparent chronological trace checker -/

/-- Caller-owned version-zero assumptions, in exact base-node order. -/
def initialContextFrom (index : Nat) : List Fact -> List (NodeFact Fact)
  | [] => []
  | fact :: facts =>
      { node := { index }, fact } :: initialContextFrom (index + 1) facts

def initialContext (input : CheckerInput Fact) : List (NodeFact Fact) :=
  initialContextFrom 0 input.initialFacts.toList

theorem initialContextFrom_node_lt (facts : List Fact) (index : Nat)
    (nodeFact : NodeFact Fact)
    (member : nodeFact ∈ initialContextFrom index facts) :
    nodeFact.node.index < index + facts.length := by
  induction facts generalizing index with
  | nil => simp [initialContextFrom] at member
  | cons fact facts induction =>
      simp only [initialContextFrom, List.mem_cons] at member
      rcases member with equal | member
      · subst nodeFact
        simp
      · have later := induction (index := index + 1) member
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using later

/-- A list member carrying its membership proof in `Type`. -/
structure Member (items : List α) where
  value : α
  proof : value ∈ items

def findNodeMember? (node : NodeId) :
    (items : List (NodeFact Fact)) -> Option (Member items)
  | [] => none
  | fact :: facts =>
      if fact.node == node then
        some { value := fact, proof := List.Mem.head _ }
      else
        match findNodeMember? node facts with
        | none => none
        | some member =>
            some { value := member.value, proof := List.Mem.tail _ member.proof }

/-- One chronologically established fact, together with its theorem from the
caller-owned initial context. -/
structure ProvenFact (semantics : Semantics Fact) (program : Program)
    (assumptions : List (NodeFact Fact)) where
  nodeFact : NodeFact Fact
  version : Nat
  evidence : Evidence (semantics.Entails program assumptions nodeFact)

namespace ProvenFact

def find? (seen : SeenVersion) :
    List (ProvenFact semantics program assumptions) ->
      Option (ProvenFact semantics program assumptions)
  | [] => none
  | proven :: facts =>
      if proven.nodeFact.node == seen.node && proven.version == seen.version then
        some proven
      else
        find? seen facts

theorem holdsOfMem {Fact : Type} {semantics : Semantics Fact}
    {program : Program} {assumptions : List (NodeFact Fact)}
    (proven : List (ProvenFact semantics program assumptions))
    (valuation : NodeId -> semantics.Value)
    (model : semantics.models program valuation)
    (initial : ∀ assumption, assumption ∈ assumptions ->
      semantics.holds program valuation assumption)
    (fact : NodeFact Fact)
    (member : fact ∈ proven.map
      (fun item : ProvenFact semantics program assumptions => item.nodeFact)) :
    semantics.holds program valuation fact := by
  induction proven with
  | nil => simp at member
  | cons head tail induction =>
      simp only [List.map_cons, List.mem_cons] at member
      rcases member with equal | member
      · subst fact
        exact head.evidence.proof valuation model initial
      · exact induction member

end ProvenFact

/-- An admitted equality whose exact package-owned theorem has replayed. -/
structure ProvenEquality (semantics : Semantics Fact) (program : Program) where
  edge : EqualityEdge
  evidence :
    Evidence (semantics.Equivalent program edge.left edge.right)

/-- One package-checked conservative extension step.  Keeping the semantic
evidence is essential: structural prefix checks alone do not show that a
valuation of the caller's expression graph extends to the added nodes. -/
structure ProvenExtension (semantics : Semantics Fact) where
  before : Program
  after : Program
  programPrefix : ProgramPrefix before after
  evidence : Evidence (semantics.Extends before after)

namespace ProgramPrefix

theorem nodeSize_le (programPrefix : ProgramPrefix before after) :
    before.nodes.size ≤ after.nodes.size := by
  rcases programPrefix.nodeSuffix with ⟨suffix, equal⟩
  have lengths := congrArg List.length equal
  simp only [Array.length_toList, List.length_append] at lengths
  rw [lengths]
  exact Nat.le_add_right _ _

end ProgramPrefix

namespace Semantics

theorem extendsRefl (semantics : Semantics Fact) (program : Program) :
    semantics.Extends program program := by
  intro valuation model
  exact ⟨valuation, model, fun _ _ => rfl⟩

theorem extendsTrans (semantics : Semantics Fact)
    (programPrefix : ProgramPrefix before middle)
    (first : Evidence (semantics.Extends before middle))
    (second : Evidence (semantics.Extends middle after)) :
    semantics.Extends before after := by
  intro valuation model
  obtain ⟨middleValuation, middleModel, agreesFirst⟩ :=
    first.proof valuation model
  obtain ⟨extended, extendedModel, agreesSecond⟩ :=
    second.proof middleValuation middleModel
  refine ⟨extended, extendedModel, ?_⟩
  intro node oldNode
  calc
    extended node = middleValuation node :=
      agreesSecond node (Nat.lt_of_lt_of_le oldNode programPrefix.nodeSize_le)
    _ = valuation node := agreesFirst node oldNode

end Semantics

def expectedNewNodes (before after : Program) : List NodeId :=
  (List.range (after.nodes.size - before.nodes.size)).map
    (fun offset => { index := before.nodes.size + offset })

def instanceEqualitiesValid (equalities : Array EqualityEdge)
    (event : InstanceEvent) : Bool :=
  event.equalities.all fun equalityId =>
    (equalities[equalityId.index]?).any fun edge => edge.origin == event.origin

def replayInstances {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (input : CheckerInput Fact)
    (trace : Trace Fact) (index : Nat) :
    List InstanceEvent -> Option (List (ProvenExtension semantics))
  | [] => some []
  | event :: events => do
      let before ← trace.programs[index]?
      let after ← trace.programs[index + 1]?
      if before.operations != after.operations ||
          event.programVersion != index + 1 ||
          event.origin.programVersion != index ||
          event.newNodes != expectedNewNodes before after ||
          !instanceEqualitiesValid trace.equalities event then
        none
      else
        let basePrefix ← ProgramPrefix.check? input.baseProgram before
        let stepPrefix ← ProgramPrefix.check? before after
        let entry ← trace.arena.entry? event.payload .instance
        if entry.origin != event.origin then none else
          let context : InstanceContext input entry.origin :=
            { before
              after
              basePrefix := basePrefix.proof
              event }
          let evidence ← registry.dispatchInstance input entry context
          let rest ← replayInstances registry input trace (index + 1) events
          pure
            ({ before
               after
               programPrefix := stepPrefix.proof
               evidence } :: rest)

/-- Compose a checked chronological list of package-owned extension steps.
The endpoint comparisons are transparent checks over untrusted trace data;
the semantic result is built only from the proofs returned by the packages. -/
def composeExtensions {Fact : Type} {semantics : Semantics Fact}
    (base final : Program) :
    List (ProvenExtension semantics) ->
      Option (Evidence (semantics.Extends base final))
  | [] =>
      if equal : base = final then
        some
          { proof := by
              subst final
              exact semantics.extendsRefl base }
      else
        none
  | step :: steps =>
      if starts : step.before = base then
        match composeExtensions step.after final steps with
        | none => none
        | some rest =>
            let programPrefix : ProgramPrefix base step.after := by
              rw [← starts]
              exact step.programPrefix
            let first : Evidence (semantics.Extends base step.after) :=
              { proof := by
                  rw [← starts]
                  exact step.evidence.proof }
            some
              { proof := semantics.extendsTrans programPrefix first rest }
      else
        none

def equalityOwned (instances : Array InstanceEvent)
    (id : EqualityId) (edge : EqualityEdge) : Bool :=
  instances.any fun event =>
    event.origin == edge.origin && event.equalities.contains id

def replayEqualities {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (input : CheckerInput Fact)
    (trace : Trace Fact) (basePrefix : ProgramPrefix input.baseProgram trace.program) :
    Nat -> List EqualityEdge ->
      Option (Array (ProvenEquality semantics trace.program))
  | _, [] => some #[]
  | index, edge :: edges => do
      let id : EqualityId := { index }
      if !equalityOwned trace.instances id edge then none else
        let entry ← trace.arena.entry? edge.payload .equality
        if entry.origin != edge.origin then none else
          let context : EqualityContext input entry.origin :=
            { program := trace.program
              basePrefix
              edge }
          let evidence ← registry.dispatchEquality input entry context
          let rest ← replayEqualities registry input trace basePrefix
            (index + 1) edges
          pure (#[{ edge, evidence }] ++ rest)

def replayStructure {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (input : CheckerInput Fact)
    (trace : Trace Fact) :
    Option
      (Evidence (semantics.Extends input.baseProgram trace.program) ×
        Evidence (ProgramPrefix input.baseProgram trace.program) ×
        Array (ProvenEquality semantics trace.program)) := do
  if trace.programs.size != trace.instances.size + 1 ||
      trace.programs[0]? != some input.baseProgram ||
      trace.programs[trace.instances.size]? != some trace.program then
    none
  else
    let finalPrefix ← ProgramPrefix.check? input.baseProgram trace.program
    let steps ← replayInstances registry input trace 0 trace.instances.toList
    let extension ← composeExtensions input.baseProgram trace.program steps
    let equalities ← replayEqualities registry input trace finalPrefix.proof
      0 trace.equalities.toList
    pure (extension, finalPrefix, equalities)

def resolveFact {Fact : Type} {semantics : Semantics Fact}
    (domain : FactDomainSchema semantics) (input : CheckerInput Fact)
    (trace : Trace Fact) (assumptions : List (NodeFact Fact))
    (proven : List (ProvenFact semantics trace.program assumptions))
    (seen : SeenVersion) :
    Option (ProvenFact semantics trace.program assumptions) :=
  if seen.version == 0 then
    if seen.node.index < input.baseProgram.nodes.size then
      match findNodeMember? seen.node assumptions with
      | none => none
      | some member =>
          some
            { nodeFact := member.value
              version := 0
              evidence :=
                { proof := by
                    intro valuation model initial
                    exact initial member.value member.proof } }
    else
      match nodeProof : trace.program.node? seen.node with
      | none => none
      | some instruction =>
          some
            { nodeFact := { node := seen.node, fact := domain.top instruction.domain }
              version := 0
              evidence :=
                { proof := by
                    intro valuation model _
                    exact domain.topSound trace.program valuation seen.node
                      instruction nodeProof model } }
  else
    ProvenFact.find? seen proven

def discharge {Fact : Type} {semantics : Semantics Fact}
    (program : Program) (assumptions : List (NodeFact Fact))
    (premises : List (ProvenFact semantics program assumptions))
    (conclusion : NodeFact Fact)
    (evidence :
      Evidence (semantics.Entails program
        (premises.map (fun item => item.nodeFact)) conclusion)) :
    Evidence (semantics.Entails program assumptions conclusion) :=
  { proof := by
      intro valuation model initial
      exact evidence.proof valuation model fun fact member =>
        ProvenFact.holdsOfMem premises valuation model initial fact member }

def installFact {Fact : Type} {semantics : Semantics Fact}
    (domain : FactDomainSchema semantics) (program : Program)
    (assumptions : List (NodeFact Fact))
    (previous : ProvenFact semantics program assumptions)
    (proposed : ProvenFact semantics program assumptions)
    (event : FactEvent Fact) :
    Option (ProvenFact semantics program assumptions) :=
  if previousNode : previous.nodeFact.node = event.node then
    if proposedNode : proposed.nodeFact.node = event.node then
      if event.previous.node != event.node ||
          event.version != event.previous.version + 1 then
        none
      else do
        let meet ← domain.proveMeet program event.node previous.nodeFact.fact
          proposed.nodeFact.fact event.fact
        pure
          { nodeFact := { node := event.node, fact := event.fact }
            version := event.version
            evidence :=
              { proof := by
                  intro valuation model initial
                  have previousHolds :
                      semantics.holds program valuation
                        { node := event.node, fact := previous.nodeFact.fact } := by
                    have factEq : previous.nodeFact =
                        { node := event.node, fact := previous.nodeFact.fact } := by
                      exact NodeFact.extensionality _ _ previousNode rfl
                    rw [← factEq]
                    exact previous.evidence.proof valuation model initial
                  have proposedHolds :
                      semantics.holds program valuation
                        { node := event.node, fact := proposed.nodeFact.fact } := by
                    have factEq : proposed.nodeFact =
                        { node := event.node, fact := proposed.nodeFact.fact } := by
                      exact NodeFact.extensionality _ _ proposedNode rfl
                    rw [← factEq]
                    exact proposed.evidence.proof valuation model initial
                  exact (meet.proof valuation model).mpr
                    ⟨previousHolds, proposedHolds⟩ } }
    else
      none
  else
    none

def factFromRule {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact)
    (trace : Trace Fact) (basePrefix : ProgramPrefix input.baseProgram trace.program)
    (assumptions : List (NodeFact Fact))
    (proven : List (ProvenFact semantics trace.program assumptions))
    (event : FactEvent Fact) (action : Action) (proposed : Fact)
    (payload : PayloadId) :
    Option (ProvenFact semantics trace.program assumptions) := do
  if event.programVersion != action.programVersion then none else
    let premises ← action.inputs.mapM
      (resolveFact (Fact := Fact) (semantics := semantics)
        domain input trace assumptions proven)
    let entry ← trace.arena.entry? payload .fact
    if entry.origin != action then none else
      let context : RuleFactContext input entry.origin :=
        { program := trace.program
          basePrefix
          assumptions := premises.map (fun item => item.nodeFact)
          proposed := { node := event.node, fact := proposed } }
      let evidence ← registry.dispatchFact input entry context
      pure
        { nodeFact := context.proposed
          version := event.version
          evidence := discharge trace.program assumptions premises
            context.proposed evidence }

def transportFact {Fact : Type} {semantics : Semantics Fact}
    (trace : Trace Fact)
    (assumptions : List (NodeFact Fact))
    (equalities : Array (ProvenEquality semantics trace.program))
    (source : ProvenFact semantics trace.program assumptions)
    (target : NodeId) (equalityId : EqualityId) :
    Option (ProvenFact semantics trace.program assumptions) := do
  let equality ← equalities[equalityId.index]?
  let proposed : NodeFact Fact := { node := target, fact := source.nodeFact.fact }
  if forward :
      equality.edge.left = source.nodeFact.node ∧ equality.edge.right = target then
    pure
      { nodeFact := proposed
        version := source.version
        evidence :=
          { proof := by
              intro valuation model initial
              let equal := equality.evidence.proof valuation model
              have values :
                  valuation source.nodeFact.node = valuation target := by
                simpa [forward.1, forward.2] using equal
              exact semantics.transport trace.program valuation
                source.nodeFact.node target source.nodeFact.fact values
                (source.evidence.proof valuation model initial) } }
  else if reverse :
      equality.edge.right = source.nodeFact.node ∧ equality.edge.left = target then
    pure
      { nodeFact := proposed
        version := source.version
        evidence :=
          { proof := by
              intro valuation model initial
              let equal := (equality.evidence.proof valuation model).symm
              have values :
                  valuation source.nodeFact.node = valuation target := by
                simpa [reverse.1, reverse.2] using equal
              exact semantics.transport trace.program valuation
                source.nodeFact.node target source.nodeFact.fact values
                (source.evidence.proof valuation model initial) } }
  else
    none

def replayEvents {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (trace : Trace Fact)
    (basePrefix : ProgramPrefix input.baseProgram trace.program)
    (assumptions : List (NodeFact Fact))
    (equalities : Array (ProvenEquality semantics trace.program)) :
    List (FactEvent Fact) ->
      List (ProvenFact semantics trace.program assumptions) ->
      Option (List (ProvenFact semantics trace.program assumptions))
  | [], proven => some proven
  | event :: events, proven => do
      let previous ← resolveFact domain input trace assumptions proven event.previous
      if (ProvenFact.find?
          { node := event.node, version := event.version } proven).isSome then
        none
      else
        let proposed ←
          match event.cause with
          | .rule action fact payload =>
              factFromRule registry domain input trace basePrefix assumptions
                proven event action fact payload
          | .transport equality sourceVersion => do
              let source ←
                resolveFact domain input trace assumptions proven sourceVersion
              transportFact trace assumptions equalities source event.node equality
        let installed ← installFact domain trace.program assumptions
          previous proposed event
        replayEvents registry domain input trace basePrefix assumptions equalities
          events (installed :: proven)

/-- Replay fact and equality events after the structural pass has established
the final program prefix and all package-owned equality theorems. -/
def replayFinal {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (trace : Trace Fact)
    (basePrefix : ProgramPrefix input.baseProgram trace.program)
    (equalities : Array (ProvenEquality semantics trace.program)) :
    Option (Evidence
      (semantics.Entails trace.program (initialContext input) input.target)) := do
  let assumptions := initialContext input
  let proven ← replayEvents registry domain input trace basePrefix assumptions
      equalities trace.events.toList []
  match proven.find? (fun fact => fact.nodeFact.node == input.target.node) with
  | none =>
      match findNodeMember? input.target.node assumptions with
      | some member =>
          if targetNode : member.value.node = input.target.node then
            let implication ← domain.proveImplies trace.program input.target.node
              member.value.fact input.target.fact
            some
              { proof := by
                  intro valuation model initial
                  have stronger :
                      semantics.holds trace.program valuation
                        { node := input.target.node, fact := member.value.fact } := by
                    have factEq : member.value =
                        { node := input.target.node, fact := member.value.fact } := by
                      exact NodeFact.extensionality _ _ targetNode rfl
                    rw [← factEq]
                    exact initial member.value member.proof
                  exact implication.proof valuation model stronger }
          else
            none
      | none => none
  | some target =>
      if targetNode : target.nodeFact.node = input.target.node then
        let implication ← domain.proveImplies trace.program input.target.node
          target.nodeFact.fact input.target.fact
        some
          { proof := by
              intro valuation model initial
              have stronger :
                  semantics.holds trace.program valuation
                    { node := input.target.node, fact := target.nodeFact.fact } := by
                have factEq : target.nodeFact =
                    { node := input.target.node, fact := target.nodeFact.fact } := by
                  exact NodeFact.extensionality _ _ targetNode rfl
                rw [← factEq]
                exact target.evidence.proof valuation model initial
              exact implication.proof valuation model stronger }
      else
        none

/-- Transparently replay an explicit, untrusted trace.  Search may run through
opaque compiled session operations, but soundness depends only on this
kernel-reducible pass and the proof terms returned by package-owned schemas.

Unlike an extended-program-only checker, the result is a theorem about the
caller's original expression graph.  The checker composes every package-owned
`Extends` proof, transports the caller's initial facts to the final graph,
replays the trace there, and transports the requested old-node fact back. -/
def check {Fact : Type} {semantics : Semantics Fact}
    (registry : KernelRegistry semantics) (domain : FactDomainSchema semantics)
    (input : CheckerInput Fact) (trace : Trace Fact) :
    Option (Evidence
      (semantics.Entails input.baseProgram (initialContext input) input.target)) := do
  if sizeEqual : input.initialFacts.size = input.baseProgram.nodes.size then
    if targetOld : input.target.node.index < input.baseProgram.nodes.size then
      let (extension, basePrefix, equalities) ← replayStructure registry input trace
      let final ← replayFinal registry domain input trace basePrefix.proof equalities
      some
        { proof := by
            intro valuation model initial
            obtain ⟨extended, extendedModel, agreement⟩ :=
              extension.proof valuation model
            have extendedInitial :
                ∀ assumption, assumption ∈ initialContext input ->
                  semantics.holds trace.program extended assumption := by
              intro assumption member
              have inFacts :
                  assumption.node.index < input.initialFacts.toList.length := by
                simpa using
                  initialContextFrom_node_lt input.initialFacts.toList 0
                    assumption member
              have inBase :
                  assumption.node.index < input.baseProgram.nodes.size := by
                simpa [sizeEqual] using inFacts
              exact
                (domain.holdsPrefix input.baseProgram trace.program
                  valuation extended assumption basePrefix.proof
                  model extendedModel inBase
                  (agreement assumption.node inBase)).mp
                  (initial assumption member)
            have result := final.proof extended extendedModel extendedInitial
            exact
              (domain.holdsPrefix input.baseProgram trace.program
                valuation extended input.target basePrefix.proof
                model extendedModel targetOld
                (agreement input.target.node targetOld)).mpr result }
    else
      none
  else
    none

/-! ## Remaining production work

A complete checker still has to validate, in one forward pass:

* resource envelopes for trace sizes and theorem-schema decoding work;
* exact reconstruction of instance substitutions, products, and equality
  ownership, plus per-event program-snapshot linkage, from proposed recipes
  instead of accepting those fields only after their package schema has
  checked them;
* contradiction certificates and branch/split composition; and
* a frontend quotation format which emits the transparent `Trace` value from
  an opaque, untrusted search run.

The next Mathlib vertical should instantiate this protocol with the centered
example while leaving its function language and equality recipes local rather
than promoting either to a central engine enumeration.
-/

end Hex.Interval.Experiment.SemanticReplay
