/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Program
public import Mathlib.Lean.Elab.Tactic.Basic

@[expose] public section

/-!
# Function-agnostic proof replay

This module is the supported proof authority for interval search. Search state,
callback replies, payload arenas, and diagnostic traces are decoded data only.
The replay cursor starts from the caller's exact program and fact array and can
advance only through theorem schemas whose complete address, body, action,
scope, versions, dependencies, and chronology all match. The sealed `Registry`
authenticates package ownership before producing its resolver; the public
`Resolver` replay surface is caller-owned and does not independently enforce
that provenance.
Binary splits additionally require a package-owned cover theorem. Each child
adds exactly one assumption; inherited facts are rebased as derived evidence.
A bounded fold checks an exact retained `Search.Result.Tree`, rejects unknown
leaves, closes target or checked-refutation leaves, and joins children only
under that cover.

Schema decoders and theorem builders are package callbacks, but their returned
`Evidence` contains an ordinary Lean proof of the exact indexed proposition.
The final Meta boundary instantiates and rejects unresolved metavariables and
placeholders, restores the caller's environment, messages, information, and
metavariable state, and clears both elaborator caches before running structural
`Meta.check` and checking the inferred type against the exact expected
proposition by definitional equality. Validation state is restored and its
caches are cleared on success and failure. The kernel performs the final check
only when the caller installs the returned expression in a declaration.
Concrete operations, packages, goal reification, tactic syntax, registries of
declaration names, and default search policy are intentionally absent.

`Limits` bounds retained package/schema counts, certificate bodies, ordered
dependencies, and chronology.  It does not make `Program.check`, registration
validation, equality on caller facts, schema decoding, or package theorem
callbacks preemptible.  A search-to-proof quotation must first cross the
supported `Search` resource boundary; direct trusted callers of this module
remain responsible for supplying a structurally bounded program and package
assembly.
-/

namespace Hex.Interval.Proof

variable {Fact Value Quote : Type}

/-- One exact node/fact pair. -/
structure NodeFact (Fact : Type) where
  node : NodeId
  fact : Fact
  deriving DecidableEq, Repr

/-- Caller-owned proof input. Scope, base program, every version-zero fact, and
the requested target are immutable replay parameters. -/
structure Input (Fact : Type) where
  scope : Policy.ScopeId
  program : Program
  facts : Array Fact
  target : NodeFact Fact
  deriving DecidableEq, Repr

/-- Function-agnostic mathematical interpretation. -/
structure Semantics (Fact : Type) where
  Value : Type
  models : Program → (NodeId → Value) → Prop
  holds : Program → (NodeId → Value) → NodeFact Fact → Prop
  holdsAgree : ∀ program left right fact,
    fact.node.index < program.nodes.size →
    models program left → models program right →
    (∀ node, node.index < program.nodes.size → left node = right node) →
    (holds program left fact ↔ holds program right fact)

namespace Semantics

def Entails (semantics : Semantics Fact) (program : Program)
    (assumptions : List (NodeFact Fact)) (conclusion : NodeFact Fact) : Prop :=
  ∀ valuation, semantics.models program valuation →
    (∀ assumption, assumption ∈ assumptions →
      semantics.holds program valuation assumption) →
    semantics.holds program valuation conclusion

def EntailsEq (semantics : Semantics Fact) (program : Program)
    (assumptions : List (NodeFact Fact)) (left right : NodeId) : Prop :=
  ∀ valuation, semantics.models program valuation →
    (∀ assumption, assumption ∈ assumptions →
      semantics.holds program valuation assumption) →
    valuation left = valuation right

/-- A package-owned binary cover. Under the exact established inputs, every
model satisfies at least one ordered branch fact. -/
def Covers (semantics : Semantics Fact) (program : Program)
    (assumptions : List (NodeFact Fact)) (left right : NodeFact Fact) : Prop :=
  ∀ valuation, semantics.models program valuation →
    (∀ assumption, assumption ∈ assumptions →
      semantics.holds program valuation assumption) →
    semantics.holds program valuation left ∨ semantics.holds program valuation right

def AgreeOn (semantics : Semantics Fact) (program : Program)
    (left right : NodeId → semantics.Value) : Prop :=
  ∀ node, node.index < program.nodes.size → left node = right node

def Extends (semantics : Semantics Fact) (before after : Program) : Prop :=
  ∀ valuation, semantics.models before valuation →
    ∃ extended, semantics.models after extended ∧
      semantics.AgreeOn before valuation extended

/-- Standard node-local fact interpretation over package-composed meanings. -/
def ofMeanings (meanings : Array (Program.Meaning Value))
    (Contains : Fact → Value → Prop) : Semantics Fact :=
  { Value
    models := Program.Models meanings
    holds := fun _ valuation fact => Contains fact.fact (valuation fact.node)
    holdsAgree := by
      intro program left right fact within _ _ agree
      rw [agree fact.node within] }

end Semantics

/-- Proof data in `Type`; constructing it requires an ordinary proof of the
exact indexed claim. Runtime values have no conversion into this structure. -/
structure Evidence (claim : Prop) : Type where
  proof : claim

/-- Exact append-only structural prefix. -/
structure Prefix (before after : Program) : Prop where
  operationSize : before.operations.size ≤ after.operations.size
  nodeSize : before.nodes.size ≤ after.nodes.size
  operationAt : ∀ index, index < before.operations.size →
    after.operations[index]? = before.operations[index]?
  nodeAt : ∀ index, index < before.nodes.size →
    after.nodes[index]? = before.nodes[index]?

namespace Prefix

theorem refl (program : Program) : Prefix program program :=
  { operationSize := Nat.le_refl _
    nodeSize := Nat.le_refl _
    operationAt := fun _ _ => rfl
    nodeAt := fun _ _ => rfl }

theorem trans {first middle last : Program}
    (left : Prefix first middle) (right : Prefix middle last) :
    Prefix first last :=
  { operationSize := Nat.le_trans left.operationSize right.operationSize
    nodeSize := Nat.le_trans left.nodeSize right.nodeSize
    operationAt := by
      intro index within
      exact Eq.trans
        (right.operationAt index
          (Nat.lt_of_lt_of_le within left.operationSize))
        (left.operationAt index within)
    nodeAt := by
      intro index within
      exact Eq.trans
        (right.nodeAt index (Nat.lt_of_lt_of_le within left.nodeSize))
        (left.nodeAt index within) }

end Prefix

/-- Semantic stability of one append-only program extension. -/
structure Stable (semantics : Semantics Fact) (before after : Program) where
  appendOnly : Prefix before after
  modelsBefore : ∀ valuation, semantics.models after valuation →
    semantics.models before valuation
  holdsOld : ∀ oldValue newValue (fact : NodeFact Fact),
    fact.node.index < before.nodes.size →
    semantics.models before oldValue → semantics.models after newValue →
    semantics.AgreeOn before oldValue newValue →
    (semantics.holds before oldValue fact ↔ semantics.holds after newValue fact)

def FactsWithin (program : Program) (facts : List (NodeFact Fact)) : Prop :=
  ∀ fact, fact ∈ facts → fact.node.index < program.nodes.size

def InputsSound (semantics : Semantics Fact) (program : Program)
    (base inputs : List (NodeFact Fact)) : Prop :=
  ∀ input, input ∈ inputs → semantics.Entails program base input

/-- Fact-domain theorem boundary. Executable narrowing and contradiction flags
are deliberately absent. -/
structure Domain (semantics : Semantics Fact) where
  top : DomainId → Fact
  topSound : ∀ program valuation node instruction,
    program.node? node = some instruction → semantics.models program valuation →
    semantics.holds program valuation { node, fact := top instruction.domain }
  meet : (program : Program) → (node : NodeId) →
    (previous proposed installed : Fact) →
    Option (Evidence (∀ valuation, semantics.models program valuation →
      (semantics.holds program valuation { node, fact := installed } ↔
        semantics.holds program valuation { node, fact := previous } ∧
        semantics.holds program valuation { node, fact := proposed })))

/-- Generic equality transport law; endpoint compatibility is checked
separately from the package equality theorem. -/
structure Laws (semantics : Semantics Fact) where
  holdsEq : ∀ program valuation left right fact,
    semantics.models program valuation → valuation left = valuation right →
    (semantics.holds program valuation { node := left, fact } ↔
      semantics.holds program valuation { node := right, fact })

inductive Role where
  | fact
  | equality
  | instance
  | refute
  | split
  deriving DecidableEq, Repr

/-- Full immutable schema address. -/
structure Key where
  rule : RuleKey
  role : Role
  bodySchema : Nat
  deriving DecidableEq, Repr

/-- Exact context supplied to a fact theorem. -/
structure FactContext (semantics : Semantics Fact) where
  scope : Policy.ScopeId
  programVersion : Nat
  program : Program
  action : Action
  assumptions : List (NodeFact Fact)
  proposed : NodeFact Fact

/-- Exact context supplied to an equality theorem. -/
structure EqualityContext (semantics : Semantics Fact) where
  scope : Policy.ScopeId
  programVersion : Nat
  program : Program
  action : Action
  equality : EqualityId
  left : NodeId
  right : NodeId
  assumptions : List (NodeFact Fact)

/-- Package proof of one exact instance step. -/
structure InstanceEvidence (semantics : Semantics Fact)
    (before after : Program) where
  stable : Stable semantics before after
  extension : Evidence (semantics.Extends before after)

/-- Exact context supplied to an instantiation theorem. -/
structure InstanceContext (semantics : Semantics Fact) where
  scope : Policy.ScopeId
  beforeVersion : Nat
  afterVersion : Nat
  before : Program
  after : Program
  action : Action
  newNodes : List NodeId

structure RefuteContext (semantics : Semantics Fact) where
  scope : Policy.ScopeId
  programVersion : Nat
  program : Program
  node : NodeId
  fact : Fact

structure SplitContext (semantics : Semantics Fact) (Plan : Type) where
  scope : Policy.ScopeId
  programVersion : Nat
  program : Program
  action : Action
  assumptions : List (NodeFact Fact)
  parent : NodeFact Fact
  left : NodeFact Fact
  right : NodeFact Fact
  plan : Plan

/-- Existentially packed package-owned fact theorem. -/
structure FactSchema (semantics : Semantics Fact) where
  key : Key
  Certificate : Type
  decode : List Nat → Option Certificate
  prove : (context : FactContext semantics) → Certificate →
    Option (Evidence (semantics.Entails context.program context.assumptions
      context.proposed))

structure EqualitySchema (semantics : Semantics Fact) where
  key : Key
  Certificate : Type
  decode : List Nat → Option Certificate
  prove : (context : EqualityContext semantics) → Certificate →
    Option (Evidence (semantics.EntailsEq context.program context.assumptions
      context.left context.right))

structure InstanceSchema (semantics : Semantics Fact) where
  key : Key
  Certificate : Type
  decode : List Nat → Option Certificate
  prove : (context : InstanceContext semantics) → Certificate →
    Option (InstanceEvidence semantics context.before context.after)

structure RefuteSchema (semantics : Semantics Fact) where
  key : Key
  Certificate : Type
  decode : List Nat → Option Certificate
  prove : (context : RefuteContext semantics) → Certificate →
    Option (Evidence (∀ valuation, semantics.models context.program valuation →
      semantics.holds context.program valuation
        { node := context.node, fact := context.fact } → False))

structure SplitSchema (semantics : Semantics Fact) (Plan : Type) where
  key : Key
  Certificate : Type
  decode : List Nat → Option Certificate
  prove : (context : SplitContext semantics Plan) → Certificate →
    Option (Evidence (semantics.Covers context.program context.assumptions
      context.left context.right))

/-- One proof package owns registrations and every schema addressed by those
rule keys. -/
structure Package (semantics : Semantics Fact) (Plan : Type := List Nat) where
  registrations : Array Registration
  facts : Array (FactSchema semantics) := #[]
  equalities : Array (EqualitySchema semantics) := #[]
  instances : Array (InstanceSchema semantics) := #[]
  refuters : Array (RefuteSchema semantics) := #[]
  splits : Array (SplitSchema semantics Plan) := #[]

/-- Bounds on retained proof-registry and quotation data.  These bounds are
checked after construction of the caller's Lean values; they do not preempt
allocation inside trusted schema decoders or theorem callbacks. -/
structure Limits where
  maxPackages : Nat
  maxSchemas : Nat
  maxBodyCells : Nat
  maxDependencies : Nat
  maxChronology : Nat
  deriving DecidableEq, Repr

inductive BuildError where
  | invalidProgram
  | packageLimit
  | schemaLimit
  | invalidRegistration (package : Nat)
  | foreignSchema (package : Nat) (key : Key)
  | wrongRole (key : Key)
  | duplicateSchema (key : Key)
  | duplicateRegistration (key : RuleKey)
  | emptyRefuterOwner (package : Nat) (key : Key)
  deriving DecidableEq, Repr

/-! Under ordinary imports, only `Registry.buildWithin` can construct this
trusted theorem registry. `import all HexIntervalMathlib.Proof` is a deliberate
trusted-internals escape hatch guarded by the repository DAG checker. -/
structure Registry (semantics : Semantics Fact) (Plan : Type := List Nat) where
  private mk ::
  registrations : Array Registration
  facts : Array (FactSchema semantics)
  equalities : Array (EqualitySchema semantics)
  instances : Array (InstanceSchema semantics)
  refuters : Array (RefuteSchema semantics)
  splits : Array (SplitSchema semantics Plan)

namespace Registry

private def make (registrations : Array Registration)
    (facts : Array (FactSchema semantics))
    (equalities : Array (EqualitySchema semantics))
    (instances : Array (InstanceSchema semantics))
    (refuters : Array (RefuteSchema semantics))
    (splits : Array (SplitSchema semantics Plan)) : Registry semantics Plan :=
  .mk registrations facts equalities instances refuters splits

def owns (package : Package semantics Plan) (key : Key) : Bool :=
  package.registrations.any fun registration => registration.key == key.rule

/-- Assemble a package-local, globally unambiguous theorem registry. -/
opaque buildWithin (limits : Limits) (program : Program)
    (packages : Array (Package semantics Plan)) :
    Except BuildError (Registry semantics Plan) := do
  if !program.check then throw .invalidProgram
  if limits.maxPackages < packages.size then throw .packageLimit
  let schemaCount := packages.foldl (fun count package =>
    count + package.facts.size + package.equalities.size + package.instances.size +
      package.refuters.size + package.splits.size) 0
  if limits.maxSchemas < schemaCount then throw .schemaLimit
  let registrations := packages.foldl
    (fun all package => all ++ package.registrations) #[]
  if !Registration.check program registrations then
    let keys := registrations.toList.map fun registration => registration.key
    let duplicate := keys.find? fun key => 1 < keys.count key
    match duplicate with
    | some key => throw (.duplicateRegistration key)
    | none => throw (.invalidRegistration 0)
  let mut facts := #[]
  let mut equalities := #[]
  let mut instances := #[]
  let mut refuters := #[]
  let mut splits := #[]
  let mut seen : List Key := []
  for index in [0:packages.size] do
    let some package := packages[index]? | throw .invalidProgram
    if !Registration.check program package.registrations then
      throw (.invalidRegistration index)
    for schema in package.facts do
      if schema.key.role != .fact then throw (.wrongRole schema.key)
      if !owns package schema.key then throw (.foreignSchema index schema.key)
      if seen.contains schema.key then throw (.duplicateSchema schema.key)
      seen := schema.key :: seen
      facts := facts.push schema
    for schema in package.equalities do
      if schema.key.role != .equality then throw (.wrongRole schema.key)
      if !owns package schema.key then throw (.foreignSchema index schema.key)
      if seen.contains schema.key then throw (.duplicateSchema schema.key)
      seen := schema.key :: seen
      equalities := equalities.push schema
    for schema in package.instances do
      if schema.key.role != Role.instance then throw (.wrongRole schema.key)
      if !owns package schema.key then throw (.foreignSchema index schema.key)
      if seen.contains schema.key then throw (.duplicateSchema schema.key)
      seen := schema.key :: seen
      instances := instances.push schema
    for schema in package.refuters do
      if schema.key.role != .refute then throw (.wrongRole schema.key)
      if package.registrations.isEmpty then throw (.emptyRefuterOwner index schema.key)
      if !owns package schema.key then throw (.foreignSchema index schema.key)
      if seen.contains schema.key then throw (.duplicateSchema schema.key)
      seen := schema.key :: seen
      refuters := refuters.push schema
    for schema in package.splits do
      if schema.key.role != .split then throw (.wrongRole schema.key)
      if !owns package schema.key then throw (.foreignSchema index schema.key)
      if seen.contains schema.key then throw (.duplicateSchema schema.key)
      seen := schema.key :: seen
      splits := splits.push schema
  pure (make registrations facts equalities instances refuters splits)

def fact? (registry : Registry semantics Plan) (key : Key) : Option (FactSchema semantics) :=
  registry.facts.toList.find? fun schema => schema.key == key

def equality? (registry : Registry semantics Plan) (key : Key) :
    Option (EqualitySchema semantics) :=
  registry.equalities.toList.find? fun schema => schema.key == key

def instance? (registry : Registry semantics Plan) (key : Key) :
    Option (InstanceSchema semantics) :=
  registry.instances.toList.find? fun schema => schema.key == key

def refuter? (registry : Registry semantics Plan) (key : Key) :
    Option (RefuteSchema semantics) :=
  registry.refuters.toList.find? fun schema => schema.key == key

def split? (registry : Registry semantics Plan) (key : Key) :
    Option (SplitSchema semantics Plan) :=
  registry.splits.toList.find? fun schema => schema.key == key

/-- Authenticate the structural portion of one quoted action against the
exact registry and program snapshots. Serial, effort, and generation remain
opaque chronology data visible to the package theorem; they carry no generic
proof authority. -/
def acceptsAction (registry : Registry semantics Plan) (program : Program)
    (action : Action) (inputs : List NodeId) : Bool :=
  match registry.registrations[action.rule.index]?, program.node? action.node with
  | some registration, some anchor =>
      let common := registration.key == action.key && registration.kind == action.kind &&
        (program.operation? anchor.op).any (fun operation => operation.key == registration.head) &&
        action.inputs.map (fun seen => seen.node) == inputs &&
        match registration.matchWatch with
        | .none => action.structuralInputs.isEmpty && action.matcherEpoch.isNone
        | .network => !action.structuralInputs.isEmpty && action.matcherEpoch.isSome
      common && match registration.binding with
      | .local =>
          Slot.resolveAll? action.node anchor registration.watches == some inputs &&
            Slot.resolveAll? action.node anchor registration.writes == some action.writes
      | .scoped =>
          registration.watches.isEmpty && registration.writes.isEmpty &&
            allDistinct inputs && allDistinct action.writes &&
            inputs.all (fun node => (program.node? node).isSome) &&
            action.writes.all (fun node => (program.node? node).isSome)
      | .global =>
          registration.watches.isEmpty && registration.writes.isEmpty &&
            inputs.isEmpty && action.writes.isEmpty
  | _, _ => false

end Registry

/-! ## Transparent schema resolution

`Registry` remains the sealed runtime theorem authority. `Resolver` is the
public plain proof-syntax view used by an elaborator after a separate sealed
bridge has authenticated exact package-local coverage. Direct callers may also
construct one without that provenance; `replayWith` checks its registrations,
schema keys, actions, and chronology, but does not establish package ownership.
Every accepted schema still returns an ordinary proof checked at the exact
claim. -/

structure Resolver (semantics : Semantics Fact) where
  registrations : Array Registration
  facts : Array (FactSchema semantics)
  equalities : Array (EqualitySchema semantics)
  instances : Array (InstanceSchema semantics)

namespace Resolver

def fact? (resolver : Resolver semantics) (key : Key) : Option (FactSchema semantics) :=
  resolver.facts.toList.find? fun schema => schema.key == key

def equality? (resolver : Resolver semantics) (key : Key) :
    Option (EqualitySchema semantics) :=
  resolver.equalities.toList.find? fun schema => schema.key == key

def instance? (resolver : Resolver semantics) (key : Key) :
    Option (InstanceSchema semantics) :=
  resolver.instances.toList.find? fun schema => schema.key == key

/-- Independently authenticate the structural portion of a quoted action.
This is deliberately identical to `Registry.acceptsAction`; the syntax replay
must not inherit authorization from the compiled runtime check. -/
def acceptsAction (resolver : Resolver semantics) (program : Program)
    (action : Action) (inputs : List NodeId) : Bool :=
  match resolver.registrations[action.rule.index]?, program.node? action.node with
  | some registration, some anchor =>
      let common := registration.key == action.key && registration.kind == action.kind &&
        (program.operation? anchor.op).any (fun operation => operation.key == registration.head) &&
        action.inputs.map (fun seen => seen.node) == inputs &&
        match registration.matchWatch with
        | .none => action.structuralInputs.isEmpty && action.matcherEpoch.isNone
        | .network => !action.structuralInputs.isEmpty && action.matcherEpoch.isSome
      common && match registration.binding with
      | .local =>
          Slot.resolveAll? action.node anchor registration.watches == some inputs &&
            Slot.resolveAll? action.node anchor registration.writes == some action.writes
      | .scoped =>
          registration.watches.isEmpty && registration.writes.isEmpty &&
            allDistinct inputs && allDistinct action.writes &&
            inputs.all (fun node => (program.node? node).isSome) &&
            action.writes.all (fun node => (program.node? node).isSome)
      | .global =>
          registration.watches.isEmpty && registration.writes.isEmpty &&
            inputs.isEmpty && action.writes.isEmpty
  | _, _ => false

end Resolver

def Registry.resolver (registry : Registry semantics Plan) : Resolver semantics :=
  { registrations := registry.registrations
    facts := registry.facts
    equalities := registry.equalities
    instances := registry.instances }

/-! ## Plain replay quotations -/

structure FactStep (Fact : Type) where
  scope : Policy.ScopeId
  programVersion : Nat
  action : Action
  node : NodeId
  previous : SeenVersion
  version : Nat
  proposed : Fact
  installed : Fact
  assumptions : List SeenVersion
  schema : Key
  body : List Nat
  deriving DecidableEq, Repr

structure EqualityStep where
  scope : Policy.ScopeId
  programVersion : Nat
  action : Action
  equality : EqualityId
  left : NodeId
  right : NodeId
  assumptions : List SeenVersion
  schema : Key
  body : List Nat
  deriving DecidableEq, Repr

structure TransportStep (Fact : Type) where
  scope : Policy.ScopeId
  programVersion : Nat
  node : NodeId
  previous : SeenVersion
  version : Nat
  equality : EqualityId
  source : SeenVersion
  installed : Fact
  deriving DecidableEq, Repr

structure InstanceStep where
  scope : Policy.ScopeId
  beforeVersion : Nat
  afterVersion : Nat
  action : Action
  after : Program
  newNodes : List NodeId
  schema : Key
  body : List Nat
  deriving DecidableEq, Repr

structure RefuteStep where
  scope : Policy.ScopeId
  programVersion : Nat
  seen : SeenVersion
  schema : Key
  body : List Nat
  deriving DecidableEq, Repr

/-- Exact theorem-bearing portion of one retained split. The ordered child
seeds are deltas, not complete child fact snapshots. -/
structure SplitStep (Fact Plan : Type) where
  scope : Policy.ScopeId
  programVersion : Nat
  action : Action
  parent : SeenVersion
  plan : Plan
  left : Search.Result.Seed Fact
  right : Search.Result.Seed Fact
  schema : Key
  body : List Nat
  deriving DecidableEq, Repr

inductive Event (Fact : Type)
  | fact (step : FactStep Fact)
  | equality (step : EqualityStep)
  | transport (step : TransportStep Fact)
  | instance (step : InstanceStep)
  deriving DecidableEq, Repr

def initialBase (input : Input Fact) : List (NodeFact Fact) :=
  List.ofFn fun index : Fin input.facts.size =>
    { node := { index := index.val }, fact := input.facts[index] }

/-- An exactly correlated target already present in the initial base needs no
program execution or runtime theorem authority. -/
theorem initialTarget (semantics : Semantics Fact) (input : Input Fact)
    (index : Nat) (within : index < input.facts.size)
    (node : input.target.node = { index })
    (fact : input.target.fact = input.facts[index]) :
    semantics.Entails input.program (initialBase input) input.target := by
  intro valuation model assumptions
  apply assumptions input.target
  rw [initialBase, List.mem_ofFn]
  refine ⟨⟨index, within⟩, ?_⟩
  exact (congrArg₂ NodeFact.mk node fact).symm

/-- Exact logical assumptions visible at one replay node. Branch assumptions
are appended one at a time and are never reconstructed from runtime facts. -/
def replayBase (input : Input Fact) (assumptions : List (NodeFact Fact)) :
    List (NodeFact Fact) :=
  initialBase input ++ assumptions

theorem initialWithin (input : Input Fact)
    (size : input.facts.size = input.program.nodes.size) :
    FactsWithin input.program (initialBase input) := by
  intro fact member
  rw [initialBase, List.mem_ofFn] at member
  obtain ⟨index, rfl⟩ := member
  simpa [size] using index.isLt

theorem replayBaseWithin (input : Input Fact) (size : input.facts.size = input.program.nodes.size)
    (assumptions : List (NodeFact Fact))
    (assumptionsWithin : FactsWithin input.program assumptions) :
    FactsWithin input.program (replayBase input assumptions) := by
  intro fact member
  rw [replayBase, List.mem_append] at member
  exact member.elim (initialWithin input size fact) (assumptionsWithin fact)

structure Resolved (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) (seen : SeenVersion) where
  fact : Fact
  within : seen.node.index < program.nodes.size
  sound : Evidence (semantics.Entails program base { node := seen.node, fact })

structure Facts (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) where
  resolve : (seen : SeenVersion) → Option (Resolved semantics program base seen)

namespace Facts

def make (resolve : (seen : SeenVersion) →
    Option (Resolved semantics program base seen)) : Facts semantics program base :=
  .mk resolve

def start (semantics : Semantics Fact) (input : Input Fact)
    (size : input.facts.size = input.program.nodes.size) :
    Facts semantics input.program (initialBase input) :=
  make fun seen =>
    if version : seen.version = 0 then
      if within : seen.node.index < input.program.nodes.size then
        let factWithin : seen.node.index < input.facts.size := by simpa [size] using within
        let index : Fin input.facts.size := ⟨seen.node.index, factWithin⟩
        some
          { fact := input.facts[index]
            within
            sound :=
              { proof := by
                  intro valuation model assumptions
                  apply assumptions { node := seen.node, fact := input.facts[index] }
                  rw [initialBase, List.mem_ofFn]
                  exact ⟨index, rfl⟩ } }
      else none
    else none

def push (facts : Facts semantics program base) (seen : SeenVersion) (fact : Fact)
    (within : seen.node.index < program.nodes.size)
    (sound : Evidence (semantics.Entails program base { node := seen.node, fact })) :
    Facts semantics program base :=
  make fun requested =>
    if exact : requested = seen then
      some ⟨fact, by simpa [exact] using within, by simpa [exact] using sound⟩
    else facts.resolve requested

end Facts

def weakenEntails (semantics : Semantics Fact)
    (sound : Evidence (semantics.Entails program oldBase fact))
    (extra : NodeFact Fact) :
    Evidence (semantics.Entails program (oldBase ++ [extra]) fact) :=
  { proof := by
      intro valuation model extended
      apply sound.proof valuation model
      intro assumption member
      exact extended assumption (List.mem_append_left [extra] member) }

structure EqualityProof (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) where
  equality : EqualityId
  left : NodeId
  right : NodeId
  sound : Evidence (semantics.EntailsEq program base left right)

structure Equalities (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) where
  count : Nat
  resolve : EqualityId → Option (EqualityProof semantics program base)

namespace Equalities

def make (count : Nat)
    (resolve : EqualityId → Option (EqualityProof semantics program base)) :
    Equalities semantics program base :=
  .mk count resolve

def empty : Equalities semantics program base := make 0 fun _ => none

def push (equalities : Equalities semantics program base)
    (proof : EqualityProof semantics program base) : Equalities semantics program base :=
  make (equalities.count + 1) fun requested =>
    if requested == proof.equality then some proof else equalities.resolve requested

end Equalities

/-- Complete proof state at one exact program version. Its dependent type
indices and assumptions prevent facts or equalities from being transplanted to
a different program or branch base without supplying the corresponding typed
semantic evidence. -/
def weakenEq (semantics : Semantics Fact)
    (sound : Evidence (semantics.EntailsEq program oldBase left right))
    (extra : NodeFact Fact) :
    Evidence (semantics.EntailsEq program (oldBase ++ [extra]) left right) :=
  { proof := by
      intro valuation model extended
      apply sound.proof valuation model
      intro assumption member
      exact extended assumption (List.mem_append_left [extra] member) }

def Equalities.weaken (equalities : Equalities semantics program oldBase)
    (extra : NodeFact Fact) : Equalities semantics program (oldBase ++ [extra]) :=
  Equalities.make equalities.count fun equality => do
    let proof ← equalities.resolve equality
    pure { proof with sound := weakenEq semantics proof.sound extra }

structure State (semantics : Semantics Fact) (input : Input Fact)
    (assumptions : List (NodeFact Fact) := []) where
  scope : Policy.ScopeId
  version : Nat
  program : Program
  baseSize : input.facts.size = input.program.nodes.size
  basePrefix : Prefix input.program program
  extension : Evidence (semantics.Extends input.program program)
  stable : Stable semantics input.program program
  /-- Program at entry to this tree node. Child proofs close back to this
  snapshot before a split join; independent child extensions cannot leak. -/
  origin : Program
  originFromInput : Prefix input.program origin
  baseWithinOrigin : FactsWithin origin (replayBase input assumptions)
  originPrefix : Prefix origin program
  originExtension : Evidence (semantics.Extends origin program)
  originStable : Stable semantics origin program
  facts : Facts semantics program (replayBase input assumptions)
  equalities : Equalities semantics program (replayBase input assumptions)

theorem stableRefl (semantics : Semantics Fact) (program : Program) :
    Stable semantics program program :=
  { appendOnly := .refl program
    modelsBefore := fun _ model => model
    holdsOld := by
      intro oldValue newValue fact within oldModel newModel agree
      exact semantics.holdsAgree program oldValue newValue fact within oldModel newModel agree }

def extendsRefl (semantics : Semantics Fact) (program : Program) :
    Evidence (semantics.Extends program program) :=
  { proof := fun valuation model => ⟨valuation, model, fun _ _ => rfl⟩ }

def State.start (semantics : Semantics Fact) (input : Input Fact)
    (size : input.facts.size = input.program.nodes.size) : State semantics input :=
  { scope := input.scope
    version := 0
    program := input.program
    baseSize := size
    basePrefix := .refl input.program
    extension := extendsRefl semantics input.program
    stable := stableRefl semantics input.program
    origin := input.program
    originFromInput := .refl input.program
    baseWithinOrigin := by simpa [replayBase] using initialWithin input size
    originPrefix := .refl input.program
    originExtension := extendsRefl semantics input.program
    originStable := stableRefl semantics input.program
    facts := by simpa [replayBase] using Facts.start semantics input size
    equalities := .empty }

inductive Error where
  | invalidInput
  | chronologyLimit
  | bodyLimit
  | dependencyLimit
  | wrongScope
  | wrongProgramVersion
  | wrongAction
  | wrongSchema
  | missingSchema
  | malformedBody
  | missingDependency (seen : SeenVersion)
  | staleVersion
  | unknownNode
  | unauthorizedWrite
  | wrongEquality
  | wrongInstance
  | wrongFinalProgram
  | wrongTarget
  | wrongSplit
  | wrongTree
  | unknownLeaf
  | proofNodeLimit
  | proofDepthLimit
  | proofBodyLimit
  | proofWorkLimit
  deriving DecidableEq, Repr

/-- Data-level alignment between one retained runtime snapshot and its checked
proof state. This check never creates evidence; it only prevents a retained
snapshot from selecting proofs for a different fact or version. -/
def State.matchesBranch [DecidableEq Fact] [DecidableEq Cause]
    (semantics : Semantics Fact) (checked : State semantics input assumptions)
    (scope : Policy.ScopeId) (branch : State.Branch Fact Cause) : Bool := Id.run do
  if checked.scope != scope || checked.version != branch.programVersion ||
      checked.program != branch.program || !branch.check then return false
  let some snapshot := branch.checkedSnapshot? | return false
  for index in [0:snapshot.facts.size] do
    let some version := branch.versions[index]? | return false
    let seen : SeenVersion := { node := { index }, version }
    let some resolved := checked.facts.resolve seen | return false
    let some fact := snapshot.facts[index]? | return false
    if resolved.fact != fact then return false
  return true

/-- Rebase every current inherited runtime fact to child-local version zero,
while installing exactly one appended branch assumption at its node. The
remaining child facts stay derived evidence and do not become assumptions. -/
structure Seeded (semantics : Semantics Fact) (input : Input Fact)
    (assumptions : List (NodeFact Fact)) (origin : Program) where
  state : State semantics input assumptions
  originEq : state.origin = origin

def seedChild [DecidableEq Fact] [DecidableEq Cause]
    (semantics : Semantics Fact) (input : Input Fact)
    (parent : State semantics input assumptions)
    (parentScope childScope : Policy.ScopeId) (runtime : State.Branch Fact Cause)
    (seed : Search.Result.Seed Fact) : Except Error
      (Seeded semantics input
        (assumptions ++ [{ node := seed.node, fact := seed.fact }]) parent.program) := do
  if !parent.matchesBranch semantics parentScope runtime then throw .wrongSplit
  if seed.previous.node != seed.node then throw .wrongSplit
  let some old := parent.facts.resolve seed.previous
    | throw (.missingDependency seed.previous)
  let some runtimeOld := runtime.factAt? seed.previous | throw .wrongSplit
  if old.fact != runtimeOld || old.fact == seed.fact then throw .wrongSplit
  let within : Evidence (seed.node.index < parent.program.nodes.size) ←
    if h : seed.node.index < parent.program.nodes.size then pure ⟨h⟩ else throw .unknownNode
  let branchFact : NodeFact Fact := { node := seed.node, fact := seed.fact }
  let inheritedWithin : FactsWithin parent.program (replayBase input assumptions) :=
    fun fact member => Nat.lt_of_lt_of_le (parent.baseWithinOrigin fact member)
      parent.originPrefix.nodeSize
  let childBaseWithin : FactsWithin parent.program
      (replayBase input (assumptions ++ [branchFact])) := by
    simpa [replayBase, List.append_assoc] using
      (show FactsWithin parent.program (replayBase input assumptions ++ [branchFact]) from by
        intro fact member
        rw [List.mem_append, List.mem_singleton] at member
        exact member.elim (inheritedWithin fact) (fun equal => by
          subst fact
          exact within.proof))
  let childFacts : Facts semantics parent.program
      (replayBase input (assumptions ++ [branchFact])) :=
    Facts.make fun requested =>
      if isLocal : requested.version = 0 then
        if seeded : requested.node = seed.node then
          some
            { fact := seed.fact
              within := by simpa [seeded] using within.proof
              sound :=
                { proof := by
                    intro valuation model assumptionsHold
                    simpa [seeded, branchFact] using
                      assumptionsHold branchFact (by simp [replayBase, branchFact]) } }
        else
          match runtime.versions[requested.node.index]? with
          | none => none
          | some version =>
              match parent.facts.resolve { node := requested.node, version } with
              | none => none
              | some resolved => some
                  { fact := resolved.fact
                    within := resolved.within
                    sound := by
                      simpa [replayBase, List.append_assoc] using
                        weakenEntails semantics resolved.sound branchFact }
      else none
  let childEqualities : Equalities semantics parent.program
      (replayBase input (assumptions ++ [branchFact])) := by
    simpa [replayBase, List.append_assoc] using parent.equalities.weaken branchFact
  pure
    { state :=
        { scope := childScope
          version := 0
          program := parent.program
          baseSize := parent.baseSize
          basePrefix := parent.basePrefix
          extension := parent.extension
          stable := parent.stable
          origin := parent.program
          originFromInput := parent.basePrefix
          baseWithinOrigin := childBaseWithin
          originPrefix := .refl parent.program
          originExtension := extendsRefl semantics parent.program
          originStable := stableRefl semantics parent.program
          facts := childFacts
          equalities := childEqualities }
      originEq := rfl }

structure ResolvedInputs (semantics : Semantics Fact) (program : Program)
    (base : List (NodeFact Fact)) where
  facts : List (NodeFact Fact)
  sound : Evidence (InputsSound semantics program base facts)

def resolveInputs (facts : Facts semantics program base) :
    List SeenVersion → Option (ResolvedInputs semantics program base)
  | [] => some { facts := [], sound := { proof := by intro _ member; simp at member } }
  | seen :: rest => do
      let head ← facts.resolve seen
      let tail ← resolveInputs facts rest
      let inputs := { node := seen.node, fact := head.fact } :: tail.facts
      let sound : Evidence (InputsSound semantics program base inputs) :=
        { proof := by
            intro input member
            rcases List.mem_cons.mp member with equal | member
            · subst input; exact head.sound.proof
            · exact tail.sound.proof input member }
      pure { facts := inputs, sound }

def installMeet (semantics : Semantics Fact) (program : Program)
    (base inputs : List (NodeFact Fact)) (node : NodeId)
    (previous proposed installed : Fact)
    (rule : Evidence (semantics.Entails program inputs { node, fact := proposed }))
    (meet : Evidence (∀ valuation, semantics.models program valuation →
      (semantics.holds program valuation { node, fact := installed } ↔
        semantics.holds program valuation { node, fact := previous } ∧
        semantics.holds program valuation { node, fact := proposed })))
    (previousSound : Evidence
      (semantics.Entails program base { node, fact := previous }))
    (inputsSound : Evidence (InputsSound semantics program base inputs)) :
    Evidence (semantics.Entails program base { node, fact := installed }) :=
  { proof := by
      intro valuation model baseHolds
      apply (meet.proof valuation model).mpr
      refine ⟨previousSound.proof valuation model baseHolds, ?_⟩
      apply rule.proof valuation model
      intro input member
      exact inputsSound.proof input member valuation model baseHolds }

def bodyCheck (limits : Limits) (key : Key) (role : Role)
    (body : List Nat) : Except Error Unit := do
  if key.role != role then throw .wrongSchema
  if limits.maxBodyCells < body.length then throw .bodyLimit

def dependenciesCheck (limits : Limits) (dependencies : List SeenVersion) :
    Except Error Unit :=
  if limits.maxDependencies < dependencies.length then throw .dependencyLimit else pure ()

def replayFactWith (limits : Limits) (resolver : Resolver semantics)
    (domain : Domain semantics) (input : Input Fact)
    (checked : State semantics input assumptions)
    (step : FactStep Fact) : Except Error (State semantics input assumptions) := do
  bodyCheck limits step.schema .fact step.body
  dependenciesCheck limits step.assumptions
  if step.scope != checked.scope then throw .wrongScope
  if step.programVersion != checked.version then throw .wrongProgramVersion
  if step.action.programVersion != checked.version || step.action.key != step.schema.rule ||
      step.action.inputs != step.assumptions then throw .wrongAction
  if !step.action.writes.contains step.node then throw .unauthorizedWrite
  let nodeEq : Evidence (step.previous.node = step.node) ←
    if h : step.previous.node = step.node then pure ⟨h⟩ else throw .staleVersion
  if step.version != step.previous.version + 1 then throw .staleVersion
  let nodeWithin : Evidence (step.node.index < checked.program.nodes.size) ←
    if h : step.node.index < checked.program.nodes.size then pure ⟨h⟩ else throw .unknownNode
  let current : SeenVersion := { node := step.node, version := step.version }
  if (checked.facts.resolve current).isSome then throw .staleVersion
  let some previous := checked.facts.resolve step.previous
    | throw (.missingDependency step.previous)
  let some resolvedInputs := resolveInputs checked.facts step.assumptions
    | throw (.missingDependency (step.assumptions.head?.getD step.previous))
  if !resolver.acceptsAction checked.program step.action
      (resolvedInputs.facts.map fun fact => fact.node) then throw .wrongAction
  let some schema := resolver.fact? step.schema | throw .missingSchema
  let some certificate := schema.decode step.body | throw .malformedBody
  let context : FactContext semantics :=
    { scope := step.scope
      programVersion := checked.version
      program := checked.program
      action := step.action
      assumptions := resolvedInputs.facts
      proposed := { node := step.node, fact := step.proposed } }
  let some rule := schema.prove context certificate | throw .malformedBody
  let some meet := domain.meet checked.program step.node previous.fact
      step.proposed step.installed | throw .malformedBody
  have previousSound : Evidence (semantics.Entails checked.program (replayBase input assumptions)
      { node := step.node, fact := previous.fact }) := by
    simpa [nodeEq.proof] using previous.sound
  let sound := installMeet semantics checked.program (replayBase input assumptions) resolvedInputs.facts
    step.node previous.fact step.proposed step.installed rule meet previousSound
      resolvedInputs.sound
  have currentWithin : current.node.index < checked.program.nodes.size := by
    simpa [current] using nodeWithin.proof
  let pushed := checked.facts.push current step.installed currentWithin sound
  pure { checked with facts := pushed }

def replayFact (limits : Limits) (registry : Registry semantics Plan)
    (domain : Domain semantics) (input : Input Fact)
    (checked : State semantics input assumptions)
    (step : FactStep Fact) : Except Error (State semantics input assumptions) :=
  replayFactWith limits registry.resolver domain input checked step

def replayEqualityWith (limits : Limits) (resolver : Resolver semantics)
    (input : Input Fact) (checked : State semantics input assumptions)
    (step : EqualityStep) : Except Error (State semantics input assumptions) := do
  bodyCheck limits step.schema .equality step.body
  dependenciesCheck limits step.assumptions
  if step.scope != checked.scope then throw .wrongScope
  if step.programVersion != checked.version then throw .wrongProgramVersion
  if step.equality.index != checked.equalities.count || step.left == step.right then
    throw .wrongEquality
  let some left := checked.program.node? step.left | throw .unknownNode
  let some right := checked.program.node? step.right | throw .unknownNode
  if left.domain != right.domain then throw .wrongEquality
  if step.action.programVersion != checked.version || step.action.key != step.schema.rule ||
      step.action.inputs != step.assumptions then throw .wrongAction
  let some resolvedInputs := resolveInputs checked.facts step.assumptions
    | throw (.missingDependency (step.assumptions.head?.getD
        { node := step.left, version := 0 }))
  if !resolver.acceptsAction checked.program step.action
      (resolvedInputs.facts.map fun fact => fact.node) then throw .wrongAction
  let some schema := resolver.equality? step.schema | throw .missingSchema
  let some certificate := schema.decode step.body | throw .malformedBody
  let context : EqualityContext semantics :=
    { scope := step.scope, programVersion := checked.version, program := checked.program
      action := step.action, equality := step.equality, left := step.left,
      right := step.right, assumptions := resolvedInputs.facts }
  let some schemaSound := schema.prove context certificate | throw .malformedBody
  let sound : Evidence (semantics.EntailsEq checked.program (replayBase input assumptions)
      step.left step.right) :=
    { proof := by
        intro valuation model baseHolds
        apply schemaSound.proof valuation model
        intro assumption member
        exact resolvedInputs.sound.proof assumption member valuation model baseHolds }
  let proof : EqualityProof semantics checked.program (replayBase input assumptions) :=
    { equality := step.equality, left := step.left, right := step.right, sound }
  pure { checked with equalities := checked.equalities.push proof }

def replayEquality (limits : Limits) (registry : Registry semantics Plan)
    (input : Input Fact) (checked : State semantics input assumptions)
    (step : EqualityStep) : Except Error (State semantics input assumptions) :=
  replayEqualityWith limits registry.resolver input checked step

def replayTransport (_limits : Limits) (domain : Domain semantics)
    (laws : Laws semantics) (input : Input Fact)
    (checked : State semantics input assumptions)
    (step : TransportStep Fact) : Except Error (State semantics input assumptions) := do
  if step.scope != checked.scope then throw .wrongScope
  if step.programVersion != checked.version then throw .wrongProgramVersion
  let nodeEq : Evidence (step.previous.node = step.node) ←
    if h : step.previous.node = step.node then pure ⟨h⟩ else throw .staleVersion
  if step.version != step.previous.version + 1 then throw .staleVersion
  let nodeWithin : Evidence (step.node.index < checked.program.nodes.size) ←
    if h : step.node.index < checked.program.nodes.size then pure ⟨h⟩ else throw .unknownNode
  let current : SeenVersion := { node := step.node, version := step.version }
  if (checked.facts.resolve current).isSome then throw .staleVersion
  let some previous := checked.facts.resolve step.previous
    | throw (.missingDependency step.previous)
  let some source := checked.facts.resolve step.source
    | throw (.missingDependency step.source)
  let some equality := checked.equalities.resolve step.equality | throw .wrongEquality
  let orientation : Evidence
      ((step.node = equality.left ∧ step.source.node = equality.right) ∨
        (step.node = equality.right ∧ step.source.node = equality.left)) ←
    if h : (step.node = equality.left ∧ step.source.node = equality.right) ∨
        (step.node = equality.right ∧ step.source.node = equality.left) then
      pure ⟨h⟩
    else throw .wrongEquality
  let some meet := domain.meet checked.program step.node previous.fact source.fact
      step.installed | throw .malformedBody
  have previousSound : Evidence (semantics.Entails checked.program (replayBase input assumptions)
      { node := step.node, fact := previous.fact }) := by
    simpa [nodeEq.proof] using previous.sound
  let proposed : Evidence
      (semantics.Entails checked.program (replayBase input assumptions)
        { node := step.node, fact := source.fact }) :=
    { proof := by
        intro valuation model baseHolds
        have equalValues := equality.sound.proof valuation model baseHolds
        have sourceHolds := source.sound.proof valuation model baseHolds
        by_cases direction : step.node = equality.left ∧ step.source.node = equality.right
        · have transported := (laws.holdsEq checked.program valuation equality.left
              equality.right source.fact model equalValues).mpr (by simpa [direction.2] using sourceHolds)
          simpa [direction.1] using transported
        · have reverse : step.node = equality.right ∧ step.source.node = equality.left := by
            exact orientation.proof.resolve_left direction
          have transported := (laws.holdsEq checked.program valuation equality.left
              equality.right source.fact model equalValues).mp (by simpa [reverse.2] using sourceHolds)
          simpa [reverse.1] using transported }
  let inputSound : Evidence (InputsSound semantics checked.program
      (replayBase input assumptions) [{ node := step.node, fact := source.fact }]) :=
    { proof := by
        intro fact member
        simp only [List.mem_singleton] at member
        subst fact
        exact proposed.proof }
  let rule : Evidence (semantics.Entails checked.program
      [{ node := step.node, fact := source.fact }]
      { node := step.node, fact := source.fact }) :=
    { proof := by intro _ _ assumptions; exact assumptions _ (by simp) }
  let sound := installMeet semantics checked.program (replayBase input assumptions)
    [{ node := step.node, fact := source.fact }] step.node previous.fact source.fact
    step.installed rule meet previousSound inputSound
  have currentWithin : current.node.index < checked.program.nodes.size := by
    simpa [current] using nodeWithin.proof
  let pushed := checked.facts.push current step.installed currentWithin sound
  pure { checked with facts := pushed }

def liftEntails (stable : Stable semantics before after)
    (baseWithin : FactsWithin before base) (factWithin : fact.node.index < before.nodes.size)
    (sound : Evidence (semantics.Entails before base fact)) :
    Evidence (semantics.Entails after base fact) :=
  { proof := by
      intro valuation afterModel afterBase
      have beforeModel := stable.modelsBefore valuation afterModel
      have beforeBase : ∀ item, item ∈ base →
          semantics.holds before valuation item := by
        intro item member
        exact (stable.holdsOld valuation valuation item (baseWithin item member)
          beforeModel afterModel (fun _ _ => rfl)).mpr (afterBase item member)
      have result := sound.proof valuation beforeModel beforeBase
      exact (stable.holdsOld valuation valuation fact factWithin beforeModel afterModel
        (fun _ _ => rfl)).mp result }

def Facts.lift (facts : Facts semantics before base) (stable : Stable semantics before after)
    (baseWithin : FactsWithin before base) (domain : Domain semantics) :
    Facts semantics after base :=
  Facts.make fun seen =>
    match facts.resolve seen with
    | some resolved => some
        { fact := resolved.fact
          within := Nat.lt_of_lt_of_le resolved.within stable.appendOnly.nodeSize
          sound := liftEntails stable baseWithin resolved.within resolved.sound }
    | none =>
        if version : seen.version = 0 then
          if fresh : before.nodes.size ≤ seen.node.index then
            if within : seen.node.index < after.nodes.size then
              match found : after.node? seen.node with
              | some instruction => some
                  { fact := domain.top instruction.domain
                    within
                    sound :=
                      { proof := by
                          intro valuation model _
                          exact domain.topSound after valuation seen.node instruction found model } }
              | none => none
            else none
          else none
        else none

def liftEq (stable : Stable semantics before after)
    (baseWithin : FactsWithin before base)
    (sound : Evidence (semantics.EntailsEq before base left right)) :
    Evidence (semantics.EntailsEq after base left right) :=
  { proof := by
      intro valuation afterModel afterBase
      have beforeModel := stable.modelsBefore valuation afterModel
      apply sound.proof valuation beforeModel
      intro item member
      exact (stable.holdsOld valuation valuation item (baseWithin item member)
        beforeModel afterModel (fun _ _ => rfl)).mpr (afterBase item member) }

def Equalities.lift (equalities : Equalities semantics before base)
    (stable : Stable semantics before after) (baseWithin : FactsWithin before base) :
    Equalities semantics after base :=
  Equalities.make equalities.count fun equality => do
    let proof ← equalities.resolve equality
    pure { proof with sound := liftEq stable baseWithin proof.sound }

def composeExtends (semantics : Semantics Fact) (basePrefix : Prefix base before)
    (left : Evidence (semantics.Extends base before))
    (right : Evidence (semantics.Extends before after)) :
    Evidence (semantics.Extends base after) :=
  { proof := by
      intro valuation model
      obtain ⟨middle, middleModel, first⟩ := left.proof valuation model
      obtain ⟨extended, extendedModel, second⟩ := right.proof middle middleModel
      exact ⟨extended, extendedModel, fun node within =>
        Eq.trans (first node within)
          (second node (Nat.lt_of_lt_of_le within basePrefix.nodeSize))⟩ }

theorem composeStable (left : Stable semantics first middle)
    (right : Stable semantics middle last) : Stable semantics first last :=
  { appendOnly := left.appendOnly.trans right.appendOnly
    modelsBefore := fun valuation model => left.modelsBefore valuation (right.modelsBefore valuation model)
    holdsOld := by
      intro oldValue newValue fact within oldModel newModel agreement
      have middleModel := right.modelsBefore newValue newModel
      exact (left.holdsOld oldValue newValue fact within oldModel middleModel agreement).trans
        (right.holdsOld newValue newValue fact
          (Nat.lt_of_lt_of_le within left.appendOnly.nodeSize) middleModel newModel
          (fun _ _ => rfl)) }

def replayInstanceWith (limits : Limits) (resolver : Resolver semantics)
    (domain : Domain semantics) (input : Input Fact)
    (checked : State semantics input assumptions)
    (step : InstanceStep) : Except Error (State semantics input assumptions) := do
  bodyCheck limits step.schema .instance step.body
  if step.scope != checked.scope then throw .wrongScope
  if step.beforeVersion != checked.version || step.afterVersion != checked.version + 1 then
    throw .wrongProgramVersion
  if step.action.programVersion != checked.version || step.action.key != step.schema.rule then
    throw .wrongAction
  if !resolver.acceptsAction checked.program step.action [] then throw .wrongAction
  if !step.after.check || !Hex.Interval.State.programPrefix checked.program step.after then
    throw .wrongInstance
  let expected := (List.range (step.after.nodes.size - checked.program.nodes.size)).map
    fun offset => { index := checked.program.nodes.size + offset : NodeId }
  if step.newNodes != expected then throw .wrongInstance
  let some schema := resolver.instance? step.schema | throw .missingSchema
  let some certificate := schema.decode step.body | throw .malformedBody
  let context : InstanceContext semantics :=
    { scope := step.scope, beforeVersion := checked.version,
      afterVersion := step.afterVersion, before := checked.program, after := step.after,
      action := step.action, newNodes := step.newNodes }
  let some proof := schema.prove context certificate | throw .malformedBody
  let currentBaseWithin : FactsWithin checked.program (replayBase input assumptions) :=
    fun fact member => Nat.lt_of_lt_of_le (checked.baseWithinOrigin fact member)
      checked.originPrefix.nodeSize
  pure
    { scope := checked.scope
      version := step.afterVersion
      program := step.after
      baseSize := checked.baseSize
      basePrefix := checked.basePrefix.trans proof.stable.appendOnly
      extension := composeExtends semantics checked.basePrefix checked.extension proof.extension
      stable := composeStable checked.stable proof.stable
      origin := checked.origin
      originFromInput := checked.originFromInput
      baseWithinOrigin := checked.baseWithinOrigin
      originPrefix := checked.originPrefix.trans proof.stable.appendOnly
      originExtension := composeExtends semantics checked.originPrefix checked.originExtension
        proof.extension
      originStable := composeStable checked.originStable proof.stable
      facts := checked.facts.lift proof.stable currentBaseWithin domain
      equalities := checked.equalities.lift proof.stable currentBaseWithin }

def replayInstance (limits : Limits) (registry : Registry semantics Plan)
    (domain : Domain semantics) (input : Input Fact)
    (checked : State semantics input assumptions)
    (step : InstanceStep) : Except Error (State semantics input assumptions) :=
  replayInstanceWith limits registry.resolver domain input checked step

def replayEventWith (limits : Limits) (resolver : Resolver semantics)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact) :
    State semantics input assumptions → Event Fact →
      Except Error (State semantics input assumptions)
  | checked, .fact step => replayFactWith limits resolver domain input checked step
  | checked, .equality step => replayEqualityWith limits resolver input checked step
  | checked, .transport step => replayTransport limits domain laws input checked step
  | checked, .instance step => replayInstanceWith limits resolver domain input checked step

def replayEvent (limits : Limits) (registry : Registry semantics Plan)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact) :
    State semantics input assumptions → Event Fact →
      Except Error (State semantics input assumptions) :=
  replayEventWith limits registry.resolver domain laws input

def replayEventsWith (limits : Limits) (resolver : Resolver semantics)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact) :
    List (Event Fact) → State semantics input assumptions →
      Except Error (State semantics input assumptions)
  | [], state => pure state
  | event :: events, state => do
      let next ← replayEventWith limits resolver domain laws input state event
      replayEventsWith limits resolver domain laws input events next

def replayEvents (limits : Limits) (registry : Registry semantics Plan)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact) :
    List (Event Fact) → State semantics input assumptions →
      Except Error (State semantics input assumptions) :=
  replayEventsWith limits registry.resolver domain laws input

/-- A successfully replayed chronology retains its checked proof state. It is
the only input accepted by later target, refutation, split, and child-seed
operations; decoded runtime state never constructs this value. -/
structure Replay (semantics : Semantics Fact) (input : Input Fact)
    (assumptions : List (NodeFact Fact)) (start : State semantics input assumptions) where
  state : State semantics input assumptions
  originEq : state.origin = start.origin := by rfl

/-- Replay from an already authenticated proof state and require the exact
final program version and structural program. Failure returns no partial
state. -/
def replayFromWith (limits : Limits) (resolver : Resolver semantics)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact)
    (start : State semantics input assumptions) (events : List (Event Fact))
    (finalVersion : Nat) (finalProgram : Program) :
    Except Error (Replay semantics input assumptions start) := do
  if limits.maxChronology < events.length then throw .chronologyLimit
  let checked ← replayEventsWith limits resolver domain laws input events start
  if checked.version != finalVersion then throw .wrongProgramVersion
  if checked.program != finalProgram then throw .wrongFinalProgram
  let originEq : Evidence (checked.origin = start.origin) ←
    if h : checked.origin = start.origin then pure ⟨h⟩ else throw .wrongFinalProgram
  pure { state := checked, originEq := originEq.proof }

def replayFrom (limits : Limits) (registry : Registry semantics Plan)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact)
    (start : State semantics input assumptions) (events : List (Event Fact))
    (finalVersion : Nat) (finalProgram : Program) :
    Except Error (Replay semantics input assumptions start) :=
  replayFromWith limits registry.resolver domain laws input start events finalVersion finalProgram

/-- Close a proof in the node's possibly extended program back to the exact
program at entry to that node. Independent child extensions therefore meet at
one common parent program before a split join. -/
def closeOrigin (checked : State semantics input assumptions) (target : NodeFact Fact)
    (targetWithin : target.node.index < checked.origin.nodes.size)
    (sound : Evidence (semantics.Entails checked.program (replayBase input assumptions) target)) :
    Evidence (semantics.Entails checked.origin (replayBase input assumptions) target) :=
  { proof := by
      intro valuation originModel originBase
      obtain ⟨extended, finalModel, agreement⟩ :=
        checked.originExtension.proof valuation originModel
      have finalBase : ∀ fact, fact ∈ replayBase input assumptions →
          semantics.holds checked.program extended fact := by
        intro fact member
        exact (checked.originStable.holdsOld valuation extended fact
          (checked.baseWithinOrigin fact member) originModel finalModel agreement).mp
            (originBase fact member)
      have finalTarget := sound.proof extended finalModel finalBase
      exact (checked.originStable.holdsOld valuation extended target targetWithin
        originModel finalModel agreement).mpr finalTarget }

/-- Replay exact chronology and close the exact target/version. -/
def replayWith [DecidableEq Fact] (limits : Limits) (resolver : Resolver semantics)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact)
    (events : List (Event Fact)) (finalVersion : Nat) (finalProgram : Program)
    (result : SeenVersion) :
    Except Error (Evidence (semantics.Entails input.program (initialBase input) input.target)) := do
  if !input.program.check then throw .invalidInput
  let size : Evidence (input.facts.size = input.program.nodes.size) ←
    if h : input.facts.size = input.program.nodes.size then pure ⟨h⟩ else throw .invalidInput
  let targetWithin : Evidence (input.target.node.index < input.program.nodes.size) ←
    if h : input.target.node.index < input.program.nodes.size then pure ⟨h⟩ else throw .invalidInput
  let replayed ← replayFromWith limits resolver domain laws input
    (State.start semantics input size.proof) events finalVersion finalProgram
  let checked := replayed.state
  let nodeEq : Evidence (result.node = input.target.node) ←
    if h : result.node = input.target.node then pure ⟨h⟩ else throw .wrongTarget
  let some resolved := checked.facts.resolve result | throw (.missingDependency result)
  let factEq : Evidence (resolved.fact = input.target.fact) ←
    if h : resolved.fact = input.target.fact then pure ⟨h⟩ else throw .wrongTarget
  pure
    { proof := by
        intro valuation baseModel baseHolds
        obtain ⟨extended, finalModel, agreement⟩ :=
          checked.extension.proof valuation baseModel
        have finalBase : ∀ fact, fact ∈ initialBase input →
            semantics.holds checked.program extended fact := by
          intro fact member
          exact (checked.stable.holdsOld valuation extended fact
            ((initialWithin input size.proof) fact member) baseModel finalModel agreement).mp
              (baseHolds fact member)
        have finalResult := resolved.sound.proof extended finalModel (by
          simpa [replayBase] using finalBase)
        have finalTarget : semantics.holds checked.program extended input.target := by
          simpa [nodeEq.proof, factEq.proof] using finalResult
        exact (checked.stable.holdsOld valuation extended input.target targetWithin.proof
          baseModel finalModel agreement).mpr finalTarget }

def replay [DecidableEq Fact] (limits : Limits) (registry : Registry semantics)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact)
    (events : List (Event Fact)) (finalVersion : Nat) (finalProgram : Program)
    (result : SeenVersion) :
    Except Error (Evidence (semantics.Entails input.program (initialBase input) input.target)) :=
  replayWith limits registry.resolver domain laws input events finalVersion finalProgram result

/-- Replay one exact established impossible fact. Runtime contradiction state
is not an argument. -/
def replayRefute (limits : Limits) (registry : Registry semantics Plan)
    (input : Input Fact) (checked : State semantics input assumptions) (step : RefuteStep)
    (target : NodeFact Fact) : Except Error
      (Evidence (semantics.Entails checked.program (replayBase input assumptions) target)) := do
  bodyCheck limits step.schema .refute step.body
  if step.scope != checked.scope then throw .wrongScope
  if step.programVersion != checked.version then throw .wrongProgramVersion
  let some established := checked.facts.resolve step.seen
    | throw (.missingDependency step.seen)
  let some schema := registry.refuter? step.schema | throw .missingSchema
  let some certificate := schema.decode step.body | throw .malformedBody
  let context : RefuteContext semantics :=
    { scope := step.scope, programVersion := checked.version, program := checked.program,
      node := step.seen.node, fact := established.fact }
  let some impossible := schema.prove context certificate | throw .malformedBody
  pure
    { proof := by
        intro valuation model baseHolds
        exact False.elim (impossible.proof valuation model
          (established.sound.proof valuation model baseHolds)) }

/-- Authenticate one package-owned binary cover against the exact checked
parent proof state. The runtime split plan and child facts remain inert data
until this theorem schema succeeds. -/
def replaySplit [DecidableEq Fact] [DecidableEq Plan]
    (limits : Limits) (registry : Registry semantics Plan)
    (input : Input Fact) (checked : State semantics input assumptions)
    (step : SplitStep Fact Plan) : Except Error
      (Evidence (semantics.Covers checked.program (replayBase input assumptions)
        { node := step.left.node, fact := step.left.fact }
        { node := step.right.node, fact := step.right.fact })) := do
  bodyCheck limits step.schema .split step.body
  dependenciesCheck limits step.action.inputs
  if step.scope != checked.scope then throw .wrongScope
  if step.programVersion != checked.version ||
      step.action.programVersion != checked.version then throw .wrongProgramVersion
  if step.action.kind != .split || step.action.key != step.schema.rule ||
      step.action.node != step.parent.node || !step.action.inputs.contains step.parent then
    throw .wrongAction
  if step.left.previous != step.parent || step.right.previous != step.parent ||
      step.left.node != step.parent.node || step.right.node != step.parent.node ||
      step.left.fact == step.right.fact then throw .wrongSplit
  let some parent := checked.facts.resolve step.parent
    | throw (.missingDependency step.parent)
  let some resolvedInputs := resolveInputs checked.facts step.action.inputs
    | throw (.missingDependency (step.action.inputs.head?.getD step.parent))
  if !registry.acceptsAction checked.program step.action
      (resolvedInputs.facts.map fun fact => fact.node) then throw .wrongAction
  let some schema := registry.split? step.schema | throw .missingSchema
  let some certificate := schema.decode step.body | throw .malformedBody
  let context : SplitContext semantics Plan :=
    { scope := checked.scope
      programVersion := checked.version
      program := checked.program
      action := step.action
      assumptions := resolvedInputs.facts
      parent := { node := step.parent.node, fact := parent.fact }
      left := { node := step.left.node, fact := step.left.fact }
      right := { node := step.right.node, fact := step.right.fact }
      plan := step.plan }
  let some cover := schema.prove context certificate | throw .malformedBody
  pure
    { proof := by
        intro valuation model baseHolds
        apply cover.proof valuation model
        intro assumption member
        exact resolvedInputs.sound.proof assumption member valuation model baseHolds }

def joinCover (semantics : Semantics Fact)
    (cover : Evidence (semantics.Covers program baseFacts leftFact rightFact))
    (left : Evidence (semantics.Entails program (baseFacts ++ [leftFact]) target))
    (right : Evidence (semantics.Entails program (baseFacts ++ [rightFact]) target)) :
    Evidence (semantics.Entails program baseFacts target) :=
  { proof := by
      intro valuation model baseHolds
      rcases cover.proof valuation model baseHolds with leftHolds | rightHolds
      · apply left.proof valuation model
        intro assumption member
        rw [List.mem_append, List.mem_singleton] at member
        exact member.elim (baseHolds assumption) (fun equal => by simpa [equal] using leftHolds)
      · apply right.proof valuation model
        intro assumption member
        rw [List.mem_append, List.mem_singleton] at member
        exact member.elim (baseHolds assumption) (fun equal => by simpa [equal] using rightHolds) }

/-! ## Retained-tree proof fold -/

/-- Exact retained parent edge echoed by an untrusted proof recipe. Replaying
the recipe requires this value to match the already-checked runtime tree; it is
neither evidence nor authority to alter that tree. -/
structure TreeEdge (Fact : Type) where
  parent : Option Search.Result.Id := none
  side : Option Search.Result.Side := none
  seed : Option (Search.Result.Seed Fact) := none
  deriving DecidableEq, Repr

/-- Proof chronology aligned by retained tree node. It is decoded untrusted
data; exact replay, parent-edge, and node-state alignment are checked before
use. Constructing this value does not quote or trust a search callback. -/
structure TreeRecipe (Fact : Type) where
  events : Array (List (Event Fact))
  edges : Array (TreeEdge Fact)
  deriving DecidableEq, Repr

/-- Independent proof-fold limits. Search has already bounded retained state;
these limits bound theorem chronology and recursive proof construction. Work
is the structural sum of nodes, event cells, and split/refuter body cells. -/
structure TreeLimits where
  maxNodes : Nat
  maxDepth : Nat
  maxBodyCells : Nat
  maxWork : Nat
  deriving DecidableEq, Repr

def Event.bodyCells : Event Fact → Nat
  | .fact step => step.body.length
  | .equality step => step.body.length
  | .transport _ => 0
  | .instance step => step.body.length

def nodeBodyCells : Search.Result.Node Fact Cause Plan Key → Nat
  | .pending _ => 0
  | .terminal _ (.target _) | .terminal _ (.unknown _) => 0
  | .terminal _ (.refute step) => step.body.length
  | .split _ step _ _ => step.body.length

def TreeRecipe.bodyCells (recipe : TreeRecipe Fact) : Nat :=
  recipe.events.toList.foldl (fun total events =>
    total + events.foldl (fun subtotal event => subtotal + event.bodyCells) 0) 0

def proofWork (tree : Search.Result.Tree Fact Cause Plan Key)
    (recipe : TreeRecipe Fact) : Nat :=
  tree.nodes.size + recipe.edges.size + recipe.events.toList.foldl
    (fun total events => total + events.length) 0 +
    recipe.bodyCells + tree.nodes.toList.foldl
      (fun total node => total + nodeBodyCells node) 0

def checkTreeLimits (limits : TreeLimits)
    (tree : Search.Result.Tree Fact Cause Plan Key) (recipe : TreeRecipe Fact) :
    Except Error Unit := do
  if tree.nodes.size != recipe.events.size || tree.nodes.size != recipe.edges.size then
    throw .wrongTree
  if limits.maxNodes < tree.nodes.size then throw .proofNodeLimit
  if tree.nodes.any (fun node => limits.maxDepth < node.source.depth) then
    throw .proofDepthLimit
  let bodies := recipe.bodyCells + tree.nodes.toList.foldl
    (fun total node => total + nodeBodyCells node) 0
  if limits.maxBodyCells < bodies then throw .proofBodyLimit
  if limits.maxWork < proofWork tree recipe then throw .proofWorkLimit

def terminalTarget [DecidableEq Fact]
    (input : Input Fact) (checked : State semantics input assumptions)
    (entry : Search.Result.Target) : Except Error
      (Evidence (semantics.Entails checked.origin (replayBase input assumptions) input.target)) := do
  if entry.scope != checked.scope then throw .wrongScope
  if entry.programVersion != checked.version then throw .wrongProgramVersion
  let some resolved := checked.facts.resolve entry.seen
    | throw (.missingDependency entry.seen)
  let nodeEq : Evidence (entry.seen.node = input.target.node) ←
    if h : entry.seen.node = input.target.node then pure ⟨h⟩ else throw .wrongTarget
  let factEq : Evidence (resolved.fact = input.target.fact) ←
    if h : resolved.fact = input.target.fact then pure ⟨h⟩ else throw .wrongTarget
  let rootWithin : Evidence (input.target.node.index < input.program.nodes.size) ←
    if h : input.target.node.index < input.program.nodes.size then pure ⟨h⟩
    else throw .invalidInput
  let originWithin : input.target.node.index < checked.origin.nodes.size :=
    Nat.lt_of_lt_of_le rootWithin.proof checked.originFromInput.nodeSize
  let sound : Evidence
      (semantics.Entails checked.program (replayBase input assumptions) input.target) := by
    simpa [nodeEq.proof, factEq.proof] using resolved.sound
  pure (closeOrigin checked input.target originWithin sound)

def foldNode [DecidableEq Fact] [DecidableEq Cause] [DecidableEq Plan]
    (limits : Limits) (treeLimits : TreeLimits)
    (registry : Registry semantics Plan) (domain : Domain semantics) (laws : Laws semantics)
    (input : Input Fact) (tree : Search.Result.Tree Fact Cause Plan Key)
    (recipe : TreeRecipe Fact) (id : Search.Result.Id)
    (assumptions : List (NodeFact Fact)) (start : State semantics input assumptions)
    (fuel : Nat) : Except Error
      (Evidence (semantics.Entails start.origin (replayBase input assumptions) input.target)) := do
  let fuelPos : Evidence (0 < fuel) ←
    if h : 0 < fuel then pure ⟨h⟩ else throw .wrongTree
  let some node := tree.nodes[id.index]? | throw .wrongTree
  let source := node.source
  let some events := recipe.events[id.index]? | throw .wrongTree
  let some edge := recipe.edges[id.index]? | throw .wrongTree
  if edge.parent != source.parent || edge.side != source.side || edge.seed != source.seed then
    throw .wrongTree
  let replayed ← replayFrom limits registry domain laws input start events
    source.branch.programVersion source.branch.program
  let checked := replayed.state
  have originEq : checked.origin = start.origin := replayed.originEq
  if !checked.matchesBranch semantics source.scope source.branch then throw .wrongTree
  match node with
  | .pending _ => throw .unknownLeaf
  | .terminal _ (.unknown _) => throw .unknownLeaf
  | .terminal _ (.target entry) =>
      let closed ← terminalTarget input checked entry
      pure (by rw [originEq] at closed; exact closed)
  | .terminal _ (.refute entry) =>
      let targetWithinRoot : Evidence
          (input.target.node.index < input.program.nodes.size) ←
        if h : input.target.node.index < input.program.nodes.size then pure ⟨h⟩
        else throw .invalidInput
      let originWithin := Nat.lt_of_lt_of_le targetWithinRoot.proof
        checked.originFromInput.nodeSize
      let refuted ← replayRefute limits registry input checked
        { scope := entry.scope, programVersion := entry.programVersion,
          seen := entry.seen, schema := entry.schema, body := entry.body }
        input.target
      let closed := closeOrigin checked input.target originWithin refuted
      pure (by rw [originEq] at closed; exact closed)
  | .split _ split leftId rightId =>
      let some leftNode := tree.nodes[leftId.index]? | throw .wrongTree
      let some rightNode := tree.nodes[rightId.index]? | throw .wrongTree
      let leftSource := leftNode.source
      let rightSource := rightNode.source
      let some leftSeed := leftSource.seed | throw .wrongTree
      let some rightSeed := rightSource.seed | throw .wrongTree
      if leftSource.parent != some id || leftSource.side != some .left ||
          rightSource.parent != some id || rightSource.side != some .right then throw .wrongTree
      let cover ← replaySplit limits registry input checked
        { scope := split.scope
          programVersion := split.programVersion
          action := split.action
          parent := split.parent
          plan := split.plan
          left := leftSeed
          right := rightSeed
          schema := split.schema
          body := split.body }
      let leftChild ← seedChild semantics input checked source.scope leftSource.scope
        source.branch leftSeed
      let rightChild ← seedChild semantics input checked source.scope rightSource.scope
        source.branch rightSeed
      let leftStart := leftChild.state
      let rightStart := rightChild.state
      let nextFuel := fuel - 1
      let nextLt : Evidence (nextFuel < fuel) :=
        { proof := Nat.sub_lt fuelPos.proof (by decide) }
      let leftProof ← foldNode limits treeLimits registry domain laws input tree recipe
        leftId (assumptions ++ [{ node := leftSeed.node, fact := leftSeed.fact }])
        leftStart nextFuel
      let rightProof ← foldNode limits treeLimits registry domain laws input tree recipe
        rightId (assumptions ++ [{ node := rightSeed.node, fact := rightSeed.fact }])
        rightStart nextFuel
      have leftOrigin : leftStart.origin = checked.program := leftChild.originEq
      have rightOrigin : rightStart.origin = checked.program := rightChild.originEq
      let joined : Evidence
          (semantics.Entails checked.program (replayBase input assumptions) input.target) := by
        apply joinCover semantics cover
        · rw [leftOrigin] at leftProof
          simpa [replayBase, List.append_assoc] using leftProof
        · rw [rightOrigin] at rightProof
          simpa [replayBase, List.append_assoc] using rightProof
      let rootWithin : Evidence (input.target.node.index < input.program.nodes.size) ←
        if h : input.target.node.index < input.program.nodes.size then pure ⟨h⟩
        else throw .invalidInput
      let originWithin := Nat.lt_of_lt_of_le rootWithin.proof checked.originFromInput.nodeSize
      let closed := closeOrigin checked input.target originWithin joined
      pure (by rw [originEq] at closed; exact closed)
termination_by fuel
decreasing_by
  all_goals
    simpa [nextFuel] using nextLt.proof

/-- Check an exact retained search tree, authenticate its root against the
caller input, and replay all leaves transactionally. Unknown or pending leaves
cannot produce a proof. A non-root source starts at program version zero from
its exact parent-plus-seed origin. Sealed driver transitions may subsequently
advance its fact history; the node-local recipe must replay that exact history
before a terminal or another split can be consumed. -/
def replayTree [DecidableEq Fact] [DecidableEq Cause] [DecidableEq Plan]
    (searchLimits : Search.Result.Limits)
    (measure : Search.Result.Measure Fact Cause Plan Key)
    (limits : Limits) (treeLimits : TreeLimits)
    (registry : Registry semantics Plan) (domain : Domain semantics) (laws : Laws semantics)
    (input : Input Fact) (tree : Search.Result.Tree Fact Cause Plan Key)
    (recipe : TreeRecipe Fact) : Except Error
      (Evidence (semantics.Entails input.program (initialBase input) input.target)) := do
  if !tree.check searchLimits measure then throw .wrongTree
  if !tree.pending.isEmpty then throw .unknownLeaf
  checkTreeLimits treeLimits tree recipe
  let some root := tree.nodes[0]? | throw .wrongTree
  let source := root.source
  if source.scope != input.scope || source.branch.baseProgram != input.program ||
      source.branch.initialFacts != input.facts then throw .wrongTree
  let size : Evidence (input.facts.size = input.program.nodes.size) ←
    if h : input.facts.size = input.program.nodes.size then pure ⟨h⟩ else throw .invalidInput
  let folded ← foldNode limits treeLimits registry domain laws input tree recipe
    { index := 0 } [] (State.start semantics input size.proof) (tree.nodes.size + 1)
  pure (by simpa [State.start, replayBase] using folded)

/-! ## Elaborator-facing expression boundary -/

/-- Package-owned expression producer. It has no proof authority beyond the
type of an expression accepted by the elaborator checks below and eventually
installed in a kernel-checked declaration. A returned expression may reference
only declarations that existed before `emit`; emitter-created declarations are
rolled back before authoritative validation. -/
structure Emitter (Quote : Type) where
  emit : Quote → Lean.MetaM Lean.Expr

/-- Run one package emitter transactionally. The returned expression contains
no unresolved metavariables or placeholders. Emitter environment, message,
information, and metavariable changes are restored and environment-dependent
caches are cleared before the expression passes `Meta.check` and exact type
checking in the caller's environment. Validation state is likewise restored
and its caches cleared on success and failure. -/
def emitChecked (emitter : Emitter Quote) (quote : Quote)
    (expected : Lean.Expr) : Lean.MetaM Lean.Expr := do
  -- `Meta.SavedState.restore` deliberately retains both the `Meta.State` and
  -- `Core.State` caches, which may depend on a declaration rolled back below.
  let restoreClean (saved : Lean.Meta.SavedState) : Lean.MetaM Unit := do
    saved.restore
    Lean.Meta.resetCache
    modifyThe Lean.Core.State fun state => { state with cache := {} }
  let emitterSaved ← Lean.Meta.saveState
  let prepared ← try
    let expected ← Lean.instantiateMVars expected
    if expected.hasSorry then
      throwError "interval proof emitter expected type contains a placeholder expression"
    if expected.hasMVar then
      throwError "interval proof emitter expected type contains unresolved metavariables"
    let candidate ← Lean.instantiateMVars (← emitter.emit quote)
    if candidate.hasSorry then
      throwError "interval proof emitter returned a placeholder expression"
    if candidate.hasMVar then
      throwError "interval proof emitter returned unresolved metavariables"
    pure (candidate, expected)
  catch error =>
    restoreClean emitterSaved
    throw error
  restoreClean emitterSaved
  let (candidate, expected) := prepared
  let validationSaved ← Lean.Meta.saveState
  try
    Lean.Meta.check candidate
    let actual ← Lean.instantiateMVars (← Lean.Meta.inferType candidate)
    if actual.hasMVar then
      throwError "interval proof emitter inferred an unresolved type"
    unless ← Lean.Meta.isDefEq actual expected do
      throwError "interval proof emitter returned type {actual}; expected {expected}"
    let candidate ← Lean.instantiateMVars candidate
    if candidate.hasMVar then
      throwError "interval proof emitter unification left unresolved metavariables"
    restoreClean validationSaved
    pure candidate
  catch error =>
    restoreClean validationSaved
    throw error

/-- Project the ordinary theorem from a successfully checked proof object. -/
theorem ofEvidence {claim : Prop} (evidence : Evidence claim) : claim :=
  evidence.proof

end Hex.Interval.Proof
