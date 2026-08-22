/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Proof

@[expose] public section

/-!
# Typed runtime proof quotation

This module is the supported companion boundary from sealed Mathlib-free
`Runtime.Applied` transitions to the theorem-bearing `Proof.Event` language.
Raw executable quotations remain inert: this adapter resolves their exact
rule, role, and schema through both sealed registries, runs both the executable
format validator and the theorem-schema decoder, and reconstructs every proof
event from the authenticated typed runtime event.

Instance events are wider than `Proof.InstanceStep`: before discarding the
runtime-only fields, quotation checks the exact append-only program, binding,
application-address, and generation suffixes. Transport has no raw quote; its
proof event is derived only after independently checking the admitted equality
descriptor, orientation, exact live source fact, and installed update. These
are structural runtime authorizations, not semantic entailment authority:
only equality-schema replay proves substitution.

`quoteTreeWithin` performs a full transaction over the retained typed
transition chains and seals the exact registry with the resulting per-node
recipe. `replayTree` consumes that checked token without quoting again.
The underlying proof fold deliberately rechecks the retained tree and proof
limits once at its theorem boundary; arbitrary package decoders and theorem
callbacks remain non-preemptible. Target, refutation, and split records remain
the separately checked terminal schemas already owned by `Proof.replayTree`.
-/

namespace Hex.Interval.RuntimeProof

variable {Fact Cause Plan : Type}

/-- Stable compatibility epoch for one executable/proof registry pair. It is
not callback identity; all decoded results still cross both registries and the
typed transition checks below. -/
structure Key where
  name : String
  version : Nat
  deriving DecidableEq, Repr

abbrev Assembly (Fact Cause : Type) :=
  Executable.Assembly Fact (Runtime.Batch Fact Cause)

/-- Exact executable/theorem alignment. The private constructor prevents a
caller from transplanting a proof registry after format coverage was checked. -/
structure Registry (Fact : Type) (semantics : Proof.Semantics Fact)
    (Cause Plan : Type := List Nat) where
  private mk ::
  key : Key
  assembly : Assembly Fact Cause
  proof : Proof.Registry semantics Plan

/-- Quotation limits in addition to the retained search/runtime and proof
limits. `maxEvents` is a total retained-tree admission bound, while the
runtime limit remains the per-callback batch bound. Neither cap preempts
callback execution or equality on arbitrary caller facts.
`maxStructuralCells` charges retained bindings, applications,
equalities, and typed-event cells before recipe construction. -/
structure Limits where
  result : Search.Result.Limits
  proof : Proof.Limits
  tree : Proof.TreeLimits
  maxTransitions : Nat
  maxEvents : Nat
  maxStructuralCells : Nat
  deriving DecidableEq, Repr

inductive Resource where
  | transitions
  | events
  | structuralCells
  deriving DecidableEq, Repr

inductive Malformed where
  | quote
  | fact
  | equality
  | transport
  | instance
  | transition
  | tree
  deriving DecidableEq, Repr

inductive Error where
  | invalidRegistry
  | executable (error : Executable.Error)
  | state (error : State.BranchError)
  | proof (error : Proof.Error)
  | missingFormat (key : Executable.ReplayKey)
  | missingSchema (key : Proof.Key)
  | invalidBody (key : Proof.Key)
  | malformed (location : Malformed)
  | mismatch
  | resource (resource : Resource)
  deriving DecidableEq, Repr

/-- Promote a small checked result into the universe used by registries and
assemblies, whose package-owned certificate/cache types make them large. -/
private def promote {E A : Type} (map : E → Error) :
    Except E A → Except Error (ULift.{1, 0} A)
  | .ok value => .ok ⟨value⟩
  | .error error => .error (map error)

private def sameRegistrations (left right : Array Registration) : Bool := Id.run do
  if left.size != right.size then return false
  for index in [0:left.size] do
    let some a := left[index]? | return false
    let some b := right[index]? | return false
    if !a.same b then return false
  return true

private def proofRole : Executable.Role → Proof.Role
  | .fact => .fact
  | .equality => .equality
  | .instance => .instance

private def executableRole? : Proof.Role → Option Executable.Role
  | .fact => some .fact
  | .equality => some .equality
  | .instance => some .instance
  | .refute | .split => none

private def proofKey (rule : RuleKey) (role : Executable.Role) (schema : Nat) : Proof.Key :=
  { rule, role := proofRole role, bodySchema := schema }

private def hasSchema (proof : Proof.Registry semantics Plan) (key : Proof.Key) : Bool :=
  match key.role with
  | .fact => (proof.fact? key).isSome
  | .equality => (proof.equality? key).isSome
  | .instance => (proof.instance? key).isSome
  | .refute => (proof.refuter? key).isSome
  | .split => (proof.split? key).isSome

private def hasFormat (assembly : Assembly Fact Cause) (key : Proof.Key) : Bool :=
  match executableRole? key.role,
      Registration.find? assembly.registry.registrations key.rule with
  | some role, some (ruleId, _) =>
      match assembly.registry.formats? ruleId with
      | some (rule, formats) =>
          rule == key.rule && formats.any fun format =>
            format.role == role && format.schema == key.bodySchema
      | none => false
  | _, _ => false

private def formatCoverage (assembly : Assembly Fact Cause)
    (proof : Proof.Registry semantics Plan) : Bool := Id.run do
  for index in [0:assembly.registry.registrations.size] do
    let some (rule, formats) := assembly.registry.formats? { index } | return false
    for format in formats do
      if !hasSchema proof (proofKey rule format.role format.schema) then return false
  for schema in proof.facts do
    if !hasFormat assembly schema.key then return false
  for schema in proof.equalities do
    if !hasFormat assembly schema.key then return false
  for schema in proof.instances do
    if !hasFormat assembly schema.key then return false
  return true

/-- Seal bidirectional coverage of every typed-runtime replay format and every
fact/equality/instance proof schema. Refutation and split schemas are allowed
as terminal-only registrations and deliberately require no executable format. -/
opaque Registry.buildWithin (limits : Executable.Limits) (key : Key)
    (assembly : Assembly Fact Cause) (proof : Proof.Registry semantics Plan) :
    Except Error (Registry Fact semantics Cause Plan) := do
  let _ ← promote Error.executable (assembly.preflightWithin limits)
  if !assembly.program.check ||
      !Registration.check assembly.program proof.registrations ||
      !sameRegistrations assembly.registry.registrations proof.registrations ||
      !formatCoverage assembly proof then
    throw .invalidRegistry
  pure { key, assembly, proof }

private def inputsAvailable (branch : State.Branch Fact Cause)
    (inputs : List SeenVersion) : Bool :=
  inputs.all fun seen => (branch.factAt? seen).isSome

private def current (branch : State.Branch Fact Cause) (seen : SeenVersion) : Bool :=
  branch.versions[seen.node.index]? == some seen.version &&
    (branch.factAt? seen).isSome

private def expectedNodes (start count : Nat) : List NodeId :=
  (List.range count).map fun offset => { index := start + offset }

private def expectedApplications (start count : Nat) : List ApplicationId :=
  (List.range count).map fun offset => { index := start + offset }

private def suffix {α : Type} (before after : Array α) : List α :=
  (List.range (after.size - before.size)).filterMap fun offset =>
    after[before.size + offset]?

private def equalityPrefix (before after : Array Runtime.Equality) : Bool := Id.run do
  if after.size < before.size then return false
  for index in [0:before.size] do
    if before[index]? != after[index]? then return false
  return true

private def quoteOf : Runtime.Event Fact Cause → Option Executable.Quote
  | .fact step => some step.quote
  | .equality step => some step.quote
  | .instance step => some step.quote
  | .transport _ => none

private def eventQuotes (events : Array (Runtime.Event Fact Cause)) :
    Array Executable.Quote :=
  events.toList.filterMap quoteOf |>.toArray

private def decodeSchema (proof : Proof.Registry semantics Plan) (key : Proof.Key)
    (body : List Nat) : Bool :=
  match key.role with
  | .fact => (proof.fact? key).any fun schema => (schema.decode body).isSome
  | .equality => (proof.equality? key).any fun schema => (schema.decode body).isSome
  | .instance => (proof.instance? key).any fun schema => (schema.decode body).isSome
  | .refute => (proof.refuter? key).any fun schema => (schema.decode body).isSome
  | .split => (proof.split? key).any fun schema => (schema.decode body).isSome

private def checkQuote (limits : Proof.Limits)
    (registry : Registry Fact semantics Cause Plan) (action : Action)
    (expected : Executable.Role) (quote : Executable.Quote) :
    Except Error Proof.Key := do
  if quote.role != expected then throw (.malformed .quote)
  let some (rule, formats) := registry.assembly.registry.formats? action.rule
    | throw (.malformed .quote)
  if rule != action.key then throw (.malformed .quote)
  let replayKey : Executable.ReplayKey :=
    { rule, role := quote.role, schema := quote.schema }
  let some format := formats.find? fun format =>
      format.role == quote.role && format.schema == quote.schema
    | throw (.missingFormat replayKey)
  if !format.accepts quote then throw (.invalidBody (proofKey rule quote.role quote.schema))
  let key := proofKey rule quote.role quote.schema
  Proof.bodyCheck limits key (proofRole quote.role) quote.body |>.mapError Error.proof
  if !hasSchema registry.proof key then throw (.missingSchema key)
  if !decodeSchema registry.proof key quote.body then throw (.invalidBody key)
  pure key

private structure Cursor (Fact Cause : Type) where
  branch : State.Branch Fact Cause
  assembly : Assembly Fact Cause
  equalities : Array Runtime.Equality
  quotes : Array Executable.Quote
  eventsRev : List (Proof.Event Fact)

private def fromBranch {α : Type} : Except State.BranchError α → Except Error α
  | .ok value => .ok value
  | .error error => .error (.state error)

private def pushFact [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (registry : Registry Fact semantics Cause Plan)
    (scope : Policy.ScopeId) (applied : Runtime.Applied Fact Cause)
    (cursor : Cursor Fact Cause) (step : Runtime.FactStep Fact Cause) :
    Except Error (Cursor Fact Cause) := do
  if step.action != applied.action ||
      step.action.programVersion != cursor.branch.programVersion ||
      step.update.programVersion != cursor.branch.programVersion ||
      !step.action.writes.contains step.update.node then throw (.malformed .fact)
  let liftedKey ← promote id
    (checkQuote limits.proof registry applied.action .fact step.quote)
  let key := liftedKey.down
  let _ ← promote Error.proof
    (Proof.dependenciesCheck limits.proof applied.action.inputs)
  let liftedNext ← promote id (fromBranch (State.Branch.pushWithin limits.result.state
    cursor.branch step.update applied.after.contradictory))
  let next := liftedNext.down
  let event : Proof.Event Fact := .fact
    { scope, programVersion := cursor.branch.programVersion, action := step.action,
      node := step.update.node, previous := step.update.previous,
      version := step.update.version, proposed := step.proposed,
      installed := step.update.fact, assumptions := step.action.inputs,
      schema := key, body := step.quote.body }
  pure
    { branch := next, assembly := cursor.assembly, equalities := cursor.equalities,
      quotes := cursor.quotes.push step.quote, eventsRev := event :: cursor.eventsRev }

private def pushEquality [DecidableEq Fact]
    (limits : Limits) (registry : Registry Fact semantics Cause Plan)
    (scope : Policy.ScopeId) (applied : Runtime.Applied Fact Cause)
    (cursor : Cursor Fact Cause) (step : Runtime.EqualityStep) :
    Except Error (Cursor Fact Cause) := do
  if step.action != applied.action ||
      step.action.programVersion != cursor.branch.programVersion ||
      step.equality.index != cursor.equalities.size || step.left == step.right ||
      step.assumptions != step.action.inputs ||
      !inputsAvailable cursor.branch step.assumptions ||
      step.generation != step.action.generation then throw (.malformed .equality)
  let some left := cursor.branch.program.node? step.left | throw (.malformed .equality)
  let some right := cursor.branch.program.node? step.right | throw (.malformed .equality)
  if left.domain != right.domain then throw (.malformed .equality)
  let liftedKey ← promote id
    (checkQuote limits.proof registry applied.action .equality step.quote)
  let key := liftedKey.down
  let _ ← promote Error.proof
    (Proof.dependenciesCheck limits.proof step.assumptions)
  let equality : Runtime.Equality :=
    { left := step.left, right := step.right, generation := step.generation,
      origin := step.action, assumptions := step.assumptions, quote := step.quote }
  let event : Proof.Event Fact := .equality
    { scope, programVersion := cursor.branch.programVersion, action := step.action,
      equality := step.equality, left := step.left, right := step.right,
      assumptions := step.assumptions, schema := key, body := step.quote.body }
  pure
    { branch := cursor.branch, assembly := cursor.assembly,
      equalities := cursor.equalities.push equality,
      quotes := cursor.quotes.push step.quote, eventsRev := event :: cursor.eventsRev }

private def pushTransport [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (scope : Policy.ScopeId)
    (applied : Runtime.Applied Fact Cause) (cursor : Cursor Fact Cause)
    (step : Runtime.TransportStep Fact Cause) : Except Error (Cursor Fact Cause) := do
  if step.action != applied.action ||
      step.action.programVersion != cursor.branch.programVersion ||
      step.update.programVersion != cursor.branch.programVersion ||
      !step.action.writes.contains step.update.node ||
      !step.action.inputs.contains step.source || !current cursor.branch step.source ||
      cursor.branch.factAt? step.source != some step.update.fact then
    throw (.malformed .transport)
  let some equality := cursor.equalities[step.equality.index]?
    | throw (.malformed .transport)
  let oriented :=
    (step.update.node == equality.left && step.source.node == equality.right) ||
      (step.update.node == equality.right && step.source.node == equality.left)
  if !oriented then throw (.malformed .transport)
  let liftedNext ← promote id (fromBranch (State.Branch.pushWithin limits.result.state
    cursor.branch step.update applied.after.contradictory))
  let next := liftedNext.down
  let event : Proof.Event Fact := .transport
    { scope, programVersion := cursor.branch.programVersion, node := step.update.node,
      previous := step.update.previous, version := step.update.version,
      equality := step.equality, source := step.source, installed := step.update.fact }
  pure
    { branch := next, assembly := cursor.assembly, equalities := cursor.equalities,
      quotes := cursor.quotes, eventsRev := event :: cursor.eventsRev }

private def pushInstance [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (registry : Registry Fact semantics Cause Plan)
    (scope : Policy.ScopeId) (applied : Runtime.Applied Fact Cause)
    (cursor : Cursor Fact Cause) (step : Runtime.InstanceStep Fact) :
    Except Error (Cursor Fact Cause) := do
  if step.action != applied.action || step.action.kind != .instantiate ||
      step.action.programVersion != cursor.branch.programVersion ||
      step.generation != cursor.assembly.generation + 1 ||
      (step.newNodes.isEmpty && step.newBindings.isEmpty && step.newApplications.isEmpty) ||
      !Executable.bindingsPrefix cursor.assembly.bindings step.bindings ||
      step.newBindings != suffix cursor.assembly.bindings step.bindings ||
      step.newNodes != expectedNodes cursor.branch.program.nodes.size
        (step.after.nodes.size - cursor.branch.program.nodes.size) then
    throw (.malformed .instance)
  let nextAssembly ← cursor.assembly.extendAllWithin limits.result.runtime.executable
    step.after step.bindings step.generation |>.mapError Error.executable
  let freshApplications := nextAssembly.applications.size - cursor.assembly.applications.size
  if step.newApplications != expectedApplications cursor.assembly.applications.size
      freshApplications then throw (.malformed .instance)
  let liftedKey ← promote id
    (checkQuote limits.proof registry applied.action .instance step.quote)
  let key := liftedKey.down
  let liftedNext ← promote id (fromBranch (State.Branch.extendWithin limits.result.state
    cursor.branch step.after step.freshFacts (cursor.branch.programVersion + 1)))
  let next := liftedNext.down
  let event : Proof.Event Fact := .instance
    { scope, beforeVersion := cursor.branch.programVersion,
      afterVersion := next.programVersion, action := step.action,
      after := step.after, newNodes := step.newNodes, schema := key,
      body := step.quote.body }
  pure
    { branch := next, assembly := nextAssembly, equalities := cursor.equalities,
      quotes := cursor.quotes.push step.quote, eventsRev := event :: cursor.eventsRev }

private def pushEvent [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (registry : Registry Fact semantics Cause Plan)
    (scope : Policy.ScopeId) (applied : Runtime.Applied Fact Cause)
    (cursor : Cursor Fact Cause) : Runtime.Event Fact Cause →
      Except Error (Cursor Fact Cause)
  | .fact step => pushFact limits registry scope applied cursor step
  | .equality step => pushEquality limits registry scope applied cursor step
  | .transport step => pushTransport limits scope applied cursor step
  | .instance step => pushInstance limits registry scope applied cursor step

private def quoteAppliedRevFrom [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (registry : Registry Fact semantics Cause Plan)
    (scope : Policy.ScopeId) (assembly : Assembly Fact Cause)
    (eventsRev : List (Proof.Event Fact))
    (applied : Runtime.Applied Fact Cause) :
    Except Error (List (Proof.Event Fact) × Assembly Fact Cause) := do
  if limits.result.runtime.maxEvents < applied.events.size ||
      limits.maxEvents < applied.events.size then throw (.resource .events)
  if applied.events.isEmpty || !applied.before.check || !applied.after.check ||
      applied.serial != applied.action.serial ||
      applied.before.baseProgram != applied.after.baseProgram ||
      applied.before.initialFacts != applied.after.initialFacts ||
      !Executable.bindingsPrefix applied.beforeBindings applied.afterBindings ||
      !Executable.applicationsPrefix applied.beforeApplications applied.afterApplications ||
      !equalityPrefix applied.beforeEqualities applied.afterEqualities ||
      applied.beforeGeneration > applied.afterGeneration ||
      applied.beforeGeneration + applied.after.programVersion !=
        applied.afterGeneration + applied.before.programVersion ||
      eventQuotes applied.events != applied.quotes ||
      !State.programPrefix registry.assembly.program applied.before.baseProgram ||
      assembly.program != applied.before.program ||
      assembly.bindings != applied.beforeBindings ||
      assembly.applications.size != applied.beforeApplications.size ||
      !Executable.applicationsPrefix assembly.applications applied.beforeApplications ||
      assembly.generation != applied.beforeGeneration ||
      !Registration.check applied.before.program registry.proof.registrations ||
      !Registration.check applied.after.program registry.proof.registrations then
    throw (.malformed .transition)
  let mut cursor : Cursor Fact Cause :=
    { branch := applied.before, assembly,
      equalities := applied.beforeEqualities,
      quotes := #[], eventsRev }
  for event in applied.events do
    cursor ← pushEvent limits registry scope applied cursor event
  if cursor.branch != applied.after || cursor.assembly.program != applied.after.program ||
      cursor.assembly.bindings != applied.afterBindings ||
      cursor.assembly.applications.size != applied.afterApplications.size ||
      !Executable.applicationsPrefix cursor.assembly.applications applied.afterApplications ||
      cursor.assembly.generation != applied.afterGeneration ||
      cursor.equalities != applied.afterEqualities || cursor.quotes != applied.quotes then
    throw .mismatch
  pure (cursor.eventsRev, cursor.assembly)

/-- Sealed exact registry, retained tree, and recipe derived from all its typed
runtime transition chains. Retaining the registry inside this private-
constructor token prevents replay under a different registry which merely
reuses the same public compatibility key. -/
structure Bundle (Fact : Type) (semantics : Proof.Semantics Fact)
    (Cause Plan : Type) where
  private mk ::
  registry : Registry Fact semantics Cause Plan
  tree : Search.Result.Tree Fact Cause Plan Proof.Key
  recipe : Proof.TreeRecipe Fact

private def edgeOf (node : Search.Result.Node Fact Cause Plan Proof.Key) :
    Proof.TreeEdge Fact :=
  { parent := node.source.parent, side := node.source.side, seed := node.source.seed }

private def structuralCells (transition : Runtime.Applied Fact Cause) : Nat :=
  transition.events.size + transition.quotes.size +
    transition.beforeBindings.size + transition.afterBindings.size +
    transition.beforeApplications.size + transition.afterApplications.size +
    transition.beforeEqualities.size + transition.afterEqualities.size

private def groupSteps
    (nodeCount : Nat)
    (transitions : Array (Search.Result.Id × Runtime.Applied Fact Cause))
    : Except Error (Array (List (Runtime.Applied Fact Cause))) := do
  let mut reversed := Array.replicate nodeCount []
  for entry in transitions do
    let some steps := reversed[entry.1.index]? | throw (.malformed .tree)
    reversed := reversed.set! entry.1.index (entry.2 :: steps)
  pure (reversed.map List.reverse)

private def quoteSteps [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (registry : Registry Fact semantics Cause Plan)
    (scope : Policy.ScopeId) :
    List (Runtime.Applied Fact Cause) → List (Proof.Event Fact) →
      Assembly Fact Cause →
      Except Error (List (Proof.Event Fact) × Assembly Fact Cause)
  | [], eventsRev, assembly => pure (eventsRev, assembly)
  | transition :: rest, eventsRev, assembly => do
      let (eventsRev, assembly) ←
        quoteAppliedRevFrom limits registry scope assembly eventsRev transition
      quoteSteps limits registry scope rest eventsRev assembly

private structure TreeCursor (Fact Cause : Type) where
  seeds : Array (Option (Assembly Fact Cause))
  chronologies : Array (List (Proof.Event Fact))

private def quoteNodes [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (registry : Registry Fact semantics Cause Plan)
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key)
    (steps : Array (List (Runtime.Applied Fact Cause))) :
    Nat → TreeCursor Fact Cause → Except Error (TreeCursor Fact Cause)
  | index, cursor => do
      if tree.nodes.size ≤ index then return cursor
      let some node := tree.nodes[index]? | throw (.malformed .tree)
      let some (some seed) := cursor.seeds[index]? | throw (.malformed .tree)
      let some nodeSteps := steps[index]? | throw (.malformed .tree)
      let (eventsRev, assembly) ←
        quoteSteps limits registry node.source.scope nodeSteps [] seed
      let chronologies := cursor.chronologies.set! index eventsRev.reverse
      let seeds := match node with
        | .split _ _ left right =>
            (cursor.seeds.set! left.index (some assembly)).set! right.index (some assembly)
        | .pending _ | .terminal _ _ => cursor.seeds
      quoteNodes limits registry tree steps (index + 1) { seeds, chronologies }

private def quoteChronologies [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (registry : Registry Fact semantics Cause Plan)
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key)
    (transitions : Array (Search.Result.Id × Runtime.Applied Fact Cause)) :
    Except Error (Array (List (Proof.Event Fact))) :=
  match groupSteps tree.nodes.size transitions with
  | .error error => .error error
  | .ok steps =>
      let seeds := (Array.replicate tree.nodes.size none).set! 0 (some registry.assembly)
      let initial : TreeCursor Fact Cause :=
        { seeds, chronologies := Array.replicate tree.nodes.size [] }
      -- Tree.check proves every child id is greater than its parent id and has
      -- exactly one incoming edge. This index fold therefore sees the parent's
      -- post-chronology assembly before it reaches either child.
      match quoteNodes limits registry tree steps 0 initial with
      | .error error => .error error
      | .ok cursor => .ok cursor.chronologies

private def quoteRecipeWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (registry : Registry Fact semantics Cause Plan)
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key) :
    Except Error (Proof.TreeRecipe Fact) := do
  if !tree.check limits.result measure then throw (.malformed .tree)
  let transitions := tree.transitions
  if limits.maxTransitions < transitions.size then throw (.resource .transitions)
  let mut eventCount := 0
  let mut cells := 0
  for entry in transitions do
    eventCount := eventCount + entry.2.events.size
    cells := cells + structuralCells entry.2
    if limits.maxEvents < eventCount then throw (.resource .events)
    if limits.maxStructuralCells < cells then throw (.resource .structuralCells)
  let mut edges : Array (Proof.TreeEdge Fact) := #[]
  for node in tree.nodes do edges := edges.push (edgeOf node)
  let events ← quoteChronologies limits registry tree transitions
  for chronology in events do
    if limits.proof.maxChronology < chronology.length then
      throw (.proof .chronologyLimit)
  let recipe : Proof.TreeRecipe Fact := { events, edges }
  Proof.checkTreeLimits limits.tree tree recipe |>.mapError Error.proof
  pure recipe

/-- Quote the complete checked retained tree transactionally. No prefix recipe
escapes if any later transition, schema, body, resource, or node-chain check
fails. -/
opaque quoteTreeWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (registry : Registry Fact semantics Cause Plan)
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key) :
    Except Error (Bundle Fact semantics Cause Plan) :=
  match quoteRecipeWithin limits measure registry tree with
  | .error error => .error error
  | .ok recipe => .ok { registry, tree, recipe }

/-- Consume one checked quotation without repeating it and run the recursive
proof fold. The token retains the exact sealed registry, so replay neither
accepts a registry substitute nor repeats executable-format/schema decoding.
The proof fold still independently rechecks the retained tree and proof limits
at its theorem boundary. Raw quotes never become evidence. -/
def replayTree [DecidableEq Fact] [DecidableEq Cause] [DecidableEq Plan]
    (limits : Limits) (measure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (domain : Proof.Domain semantics) (laws : Proof.Laws semantics)
    (input : Proof.Input Fact) (bundle : Bundle Fact semantics Cause Plan) :
    Except Error
      (Proof.Evidence (semantics.Entails input.program (Proof.initialBase input) input.target)) := do
  Proof.replayTree limits.result measure limits.proof limits.tree bundle.registry.proof
    domain laws input bundle.tree bundle.recipe |>.mapError Error.proof

end Hex.Interval.RuntimeProof
