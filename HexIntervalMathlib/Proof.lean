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
advance only through package-owned theorem schemas whose complete address,
owner, body, action, scope, versions, dependencies, and chronology all match.

Schema decoders and theorem builders are package callbacks, but their returned
`Evidence` contains an ordinary Lean proof of the exact indexed proposition.
The final Meta boundary instantiates and rejects unresolved metavariables and
placeholders, runs the elaborator's structural `Meta.check`, and checks the
inferred type against the exact expected proposition by definitional equality.
It restores Meta state on success and failure. The kernel performs the final
check only when the caller installs the returned expression in a declaration.
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

/-- One proof package owns registrations and every schema addressed by those
rule keys. -/
structure Package (semantics : Semantics Fact) where
  registrations : Array Registration
  facts : Array (FactSchema semantics) := #[]
  equalities : Array (EqualitySchema semantics) := #[]
  instances : Array (InstanceSchema semantics) := #[]
  refuters : Array (RefuteSchema semantics) := #[]

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
structure Registry (semantics : Semantics Fact) where
  private mk ::
  registrations : Array Registration
  facts : Array (FactSchema semantics)
  equalities : Array (EqualitySchema semantics)
  instances : Array (InstanceSchema semantics)
  refuters : Array (RefuteSchema semantics)

namespace Registry

private def make (registrations : Array Registration)
    (facts : Array (FactSchema semantics))
    (equalities : Array (EqualitySchema semantics))
    (instances : Array (InstanceSchema semantics))
    (refuters : Array (RefuteSchema semantics)) : Registry semantics :=
  .mk registrations facts equalities instances refuters

def owns (package : Package semantics) (key : Key) : Bool :=
  package.registrations.any fun registration => registration.key == key.rule

/-- Assemble a package-local, globally unambiguous theorem registry. -/
opaque buildWithin (limits : Limits) (program : Program)
    (packages : Array (Package semantics)) : Except BuildError (Registry semantics) := do
  if !program.check then throw .invalidProgram
  if limits.maxPackages < packages.size then throw .packageLimit
  let schemaCount := packages.foldl (fun count package =>
    count + package.facts.size + package.equalities.size + package.instances.size +
      package.refuters.size) 0
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
  pure (make registrations facts equalities instances refuters)

def fact? (registry : Registry semantics) (key : Key) : Option (FactSchema semantics) :=
  registry.facts.toList.find? fun schema => schema.key == key

def equality? (registry : Registry semantics) (key : Key) :
    Option (EqualitySchema semantics) :=
  registry.equalities.toList.find? fun schema => schema.key == key

def instance? (registry : Registry semantics) (key : Key) :
    Option (InstanceSchema semantics) :=
  registry.instances.toList.find? fun schema => schema.key == key

def refuter? (registry : Registry semantics) (key : Key) :
    Option (RefuteSchema semantics) :=
  registry.refuters.toList.find? fun schema => schema.key == key

/-- Authenticate the structural portion of one quoted action against the
exact registry and program snapshots. Serial, effort, and generation remain
opaque chronology data visible to the package theorem; they carry no generic
proof authority. -/
def acceptsAction (registry : Registry semantics) (program : Program)
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

inductive Event (Fact : Type)
  | fact (step : FactStep Fact)
  | equality (step : EqualityStep)
  | transport (step : TransportStep Fact)
  | instance (step : InstanceStep)
  deriving DecidableEq, Repr

def initialBase (input : Input Fact) : List (NodeFact Fact) :=
  List.ofFn fun index : Fin input.facts.size =>
    { node := { index := index.val }, fact := input.facts[index] }

theorem initialWithin (input : Input Fact)
    (size : input.facts.size = input.program.nodes.size) :
    FactsWithin input.program (initialBase input) := by
  intro fact member
  rw [initialBase, List.mem_ofFn] at member
  obtain ⟨index, rfl⟩ := member
  simpa [size] using index.isLt

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
indices prevent facts or equalities from being transplanted to a different
program without also supplying the corresponding typed semantic evidence. -/
structure State (semantics : Semantics Fact) (input : Input Fact) where
  version : Nat
  program : Program
  baseSize : input.facts.size = input.program.nodes.size
  basePrefix : Prefix input.program program
  extension : Evidence (semantics.Extends input.program program)
  stable : Stable semantics input.program program
  facts : Facts semantics program (initialBase input)
  equalities : Equalities semantics program (initialBase input)

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
  { version := 0
    program := input.program
    baseSize := size
    basePrefix := .refl input.program
    extension := extendsRefl semantics input.program
    stable := stableRefl semantics input.program
    facts := Facts.start semantics input size
    equalities := .empty }

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
  deriving DecidableEq, Repr

def bodyCheck (limits : Limits) (key : Key) (role : Role)
    (body : List Nat) : Except Error Unit := do
  if key.role != role then throw .wrongSchema
  if limits.maxBodyCells < body.length then throw .bodyLimit

def dependenciesCheck (limits : Limits) (dependencies : List SeenVersion) :
    Except Error Unit :=
  if limits.maxDependencies < dependencies.length then throw .dependencyLimit else pure ()

def replayFact (limits : Limits) (registry : Registry semantics)
    (domain : Domain semantics) (input : Input Fact) (checked : State semantics input)
    (step : FactStep Fact) : Except Error (State semantics input) := do
  bodyCheck limits step.schema .fact step.body
  dependenciesCheck limits step.assumptions
  if step.scope != input.scope then throw .wrongScope
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
  if !registry.acceptsAction checked.program step.action
      (resolvedInputs.facts.map fun fact => fact.node) then throw .wrongAction
  let some schema := registry.fact? step.schema | throw .missingSchema
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
  have previousSound : Evidence (semantics.Entails checked.program (initialBase input)
      { node := step.node, fact := previous.fact }) := by
    simpa [nodeEq.proof] using previous.sound
  let sound := installMeet semantics checked.program (initialBase input) resolvedInputs.facts
    step.node previous.fact step.proposed step.installed rule meet previousSound
      resolvedInputs.sound
  have currentWithin : current.node.index < checked.program.nodes.size := by
    simpa [current] using nodeWithin.proof
  let pushed := checked.facts.push current step.installed currentWithin sound
  pure { checked with facts := pushed }

def replayEquality (limits : Limits) (registry : Registry semantics)
    (input : Input Fact) (checked : State semantics input)
    (step : EqualityStep) : Except Error (State semantics input) := do
  bodyCheck limits step.schema .equality step.body
  dependenciesCheck limits step.assumptions
  if step.scope != input.scope then throw .wrongScope
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
  if !registry.acceptsAction checked.program step.action
      (resolvedInputs.facts.map fun fact => fact.node) then throw .wrongAction
  let some schema := registry.equality? step.schema | throw .missingSchema
  let some certificate := schema.decode step.body | throw .malformedBody
  let context : EqualityContext semantics :=
    { scope := step.scope, programVersion := checked.version, program := checked.program
      action := step.action, equality := step.equality, left := step.left,
      right := step.right, assumptions := resolvedInputs.facts }
  let some schemaSound := schema.prove context certificate | throw .malformedBody
  let sound : Evidence (semantics.EntailsEq checked.program (initialBase input)
      step.left step.right) :=
    { proof := by
        intro valuation model baseHolds
        apply schemaSound.proof valuation model
        intro assumption member
        exact resolvedInputs.sound.proof assumption member valuation model baseHolds }
  let proof : EqualityProof semantics checked.program (initialBase input) :=
    { equality := step.equality, left := step.left, right := step.right, sound }
  pure { checked with equalities := checked.equalities.push proof }

def replayTransport (_limits : Limits) (domain : Domain semantics)
    (laws : Laws semantics) (input : Input Fact) (checked : State semantics input)
    (step : TransportStep Fact) : Except Error (State semantics input) := do
  if step.scope != input.scope then throw .wrongScope
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
  have previousSound : Evidence (semantics.Entails checked.program (initialBase input)
      { node := step.node, fact := previous.fact }) := by
    simpa [nodeEq.proof] using previous.sound
  let proposed : Evidence
      (semantics.Entails checked.program (initialBase input)
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
      (initialBase input) [{ node := step.node, fact := source.fact }]) :=
    { proof := by
        intro fact member
        simp only [List.mem_singleton] at member
        subst fact
        exact proposed.proof }
  let rule : Evidence (semantics.Entails checked.program
      [{ node := step.node, fact := source.fact }]
      { node := step.node, fact := source.fact }) :=
    { proof := by intro _ _ assumptions; exact assumptions _ (by simp) }
  let sound := installMeet semantics checked.program (initialBase input)
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

def replayInstance (limits : Limits) (registry : Registry semantics)
    (domain : Domain semantics) (input : Input Fact) (checked : State semantics input)
    (step : InstanceStep) : Except Error (State semantics input) := do
  bodyCheck limits step.schema .instance step.body
  if step.scope != input.scope then throw .wrongScope
  if step.beforeVersion != checked.version || step.afterVersion != checked.version + 1 then
    throw .wrongProgramVersion
  if step.action.programVersion != checked.version || step.action.key != step.schema.rule then
    throw .wrongAction
  if !registry.acceptsAction checked.program step.action [] then throw .wrongAction
  if !step.after.check || !Hex.Interval.State.programPrefix checked.program step.after then
    throw .wrongInstance
  let expected := (List.range (step.after.nodes.size - checked.program.nodes.size)).map
    fun offset => { index := checked.program.nodes.size + offset : NodeId }
  if step.newNodes != expected then throw .wrongInstance
  let some schema := registry.instance? step.schema | throw .missingSchema
  let some certificate := schema.decode step.body | throw .malformedBody
  let context : InstanceContext semantics :=
    { scope := step.scope, beforeVersion := checked.version,
      afterVersion := step.afterVersion, before := checked.program, after := step.after,
      action := step.action, newNodes := step.newNodes }
  let some proof := schema.prove context certificate | throw .malformedBody
  let baseWithin := initialWithin input checked.baseSize
  let currentBaseWithin : FactsWithin checked.program (initialBase input) :=
    fun fact member => Nat.lt_of_lt_of_le (baseWithin fact member) checked.basePrefix.nodeSize
  pure
    { version := step.afterVersion
      program := step.after
      baseSize := checked.baseSize
      basePrefix := checked.basePrefix.trans proof.stable.appendOnly
      extension := composeExtends semantics checked.basePrefix checked.extension proof.extension
      stable := composeStable checked.stable proof.stable
      facts := checked.facts.lift proof.stable currentBaseWithin domain
      equalities := checked.equalities.lift proof.stable currentBaseWithin }

def replayEvent (limits : Limits) (registry : Registry semantics)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact) :
    State semantics input → Event Fact → Except Error (State semantics input)
  | checked, .fact step => replayFact limits registry domain input checked step
  | checked, .equality step => replayEquality limits registry input checked step
  | checked, .transport step => replayTransport limits domain laws input checked step
  | checked, .instance step => replayInstance limits registry domain input checked step

def replayEvents (limits : Limits) (registry : Registry semantics)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact) :
    List (Event Fact) → State semantics input → Except Error (State semantics input)
  | [], state => pure state
  | event :: events, state => do
      let next ← replayEvent limits registry domain laws input state event
      replayEvents limits registry domain laws input events next

/-- Replay exact chronology and close the exact target/version. -/
def replay [DecidableEq Fact] (limits : Limits) (registry : Registry semantics)
    (domain : Domain semantics) (laws : Laws semantics) (input : Input Fact)
    (events : List (Event Fact)) (finalVersion : Nat) (finalProgram : Program)
    (result : SeenVersion) :
    Except Error (Evidence (semantics.Entails input.program (initialBase input) input.target)) := do
  if !input.program.check then throw .invalidInput
  let size : Evidence (input.facts.size = input.program.nodes.size) ←
    if h : input.facts.size = input.program.nodes.size then pure ⟨h⟩ else throw .invalidInput
  let targetWithin : Evidence (input.target.node.index < input.program.nodes.size) ←
    if h : input.target.node.index < input.program.nodes.size then pure ⟨h⟩ else throw .invalidInput
  if limits.maxChronology < events.length then throw .chronologyLimit
  let checked ← replayEvents limits registry domain laws input events
    (State.start semantics input size.proof)
  if checked.version != finalVersion then throw .wrongProgramVersion
  if checked.program != finalProgram then throw .wrongFinalProgram
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
        have finalResult := resolved.sound.proof extended finalModel finalBase
        have finalTarget : semantics.holds checked.program extended input.target := by
          simpa [nodeEq.proof, factEq.proof] using finalResult
        exact (checked.stable.holdsOld valuation extended input.target targetWithin.proof
          baseModel finalModel agreement).mpr finalTarget }

/-- Replay one exact established impossible fact. Runtime contradiction state
is not an argument. -/
def replayRefute (limits : Limits) (registry : Registry semantics)
    (input : Input Fact) (checked : State semantics input) (step : RefuteStep)
    (target : NodeFact Fact) : Except Error
      (Evidence (semantics.Entails checked.program (initialBase input) target)) := do
  bodyCheck limits step.schema .refute step.body
  if step.scope != input.scope then throw .wrongScope
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

/-! ## Elaborator-facing expression boundary -/

/-- Package-owned expression producer. It has no proof authority beyond the
type of an expression accepted by the elaborator checks below and eventually
installed in a kernel-checked declaration. -/
structure Emitter (Quote : Type) where
  emit : Quote → Lean.MetaM Lean.Expr

/-- Run one package emitter transactionally. The returned expression contains
no unresolved metavariables or placeholders, passes `Meta.check`, and has an
inferred type definitionally equal to the exact closed expected proposition.
All emitter and unification state is restored even on success. -/
def emitChecked (emitter : Emitter Quote) (quote : Quote)
    (expected : Lean.Expr) : Lean.MetaM Lean.Expr := do
  let saved ← Lean.Meta.saveState
  try
    let expected ← Lean.instantiateMVars expected
    if expected.hasMVar then
      throwError "interval proof emitter expected type contains unresolved metavariables"
    let candidate ← Lean.instantiateMVars (← emitter.emit quote)
    if candidate.hasSorry then
      throwError "interval proof emitter returned a placeholder expression"
    if candidate.hasMVar then
      throwError "interval proof emitter returned unresolved metavariables"
    Lean.Meta.check candidate
    let actual ← Lean.instantiateMVars (← Lean.Meta.inferType candidate)
    if actual.hasMVar then
      throwError "interval proof emitter inferred an unresolved type"
    unless ← Lean.Meta.isDefEq actual expected do
      throwError "interval proof emitter returned type {actual}; expected {expected}"
    let candidate ← Lean.instantiateMVars candidate
    if candidate.hasMVar then
      throwError "interval proof emitter unification left unresolved metavariables"
    saved.restore
    pure candidate
  catch error =>
    saved.restore
    throw error

/-- Project the ordinary theorem from a successfully checked proof object. -/
theorem ofEvidence {claim : Prop} (evidence : Evidence claim) : claim :=
  evidence.proof

end Hex.Interval.Proof
