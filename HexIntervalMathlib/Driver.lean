/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Proof

@[expose] public section

/-!
# Authenticated search-to-proof recipe driver

This module owns the first supported bridge from one exact authenticated
`Search.Session` invocation to a sealed retained result tree and its separate
untrusted proof recipe. A package callback returns the runtime command and the
proof event data together; the driver never reconstructs a recipe later from
causes, contradiction flags, or diagnostics.

Callback execution and construction of arbitrary facts, causes, identifiers,
plans, and bodies remain non-preemptible. Search first authenticates the exact
selected action and package rule, then validates the echoed outcome. The
driver structurally bounds and aligns every retained event, then applies a
caller-owned logical recipe measure to every proposed/installed fact, action,
schema, body value, and seed before atomically returning the replacement
tree/recipe bundle. Measurement callbacks and arbitrary-value equality are
non-preemptible and must charge complete encodings. Neither the bundle nor
callback data is proof evidence; `Proof.replayTree` still resolves every
schema and constructs the ordinary theorem.
-/

namespace Hex.Interval.Driver

open Proof

/-- Independent logical caps for the separately retained proof recipe. -/
structure RecipeLimits where
  maxBytes : Nat
  maxWork : Nat
  deriving DecidableEq, Repr

/-- Combined retained runtime and proof-recipe limits. -/
structure Limits where
  result : Search.Result.Limits
  proof : Proof.Limits
  tree : Proof.TreeLimits
  recipe : RecipeLimits
  deriving DecidableEq, Repr

/-- Caller-owned logical encoding costs for recipe values. `cell` charges each
retained list/array cell; `event` and `edge` must charge the complete logical
encoding of their values, including nested facts, identifiers, actions,
schemas, dependency versions, body naturals, and seed data. Callback execution
and construction of the measured values remain non-preemptible. -/
structure Measure (Fact : Type) where
  cell : Search.Result.Cost
  event : Proof.Event Fact → Search.Result.Cost
  edge : Proof.TreeEdge Fact → Search.Result.Cost

/-- Exact callback outcome plus the proof events emitted by that same
invocation. The events are decoded data and are checked independently. -/
structure Echo (Fact Cause OfferId SemanticKey : Type) where
  outcome : Search.Outcome Fact Cause OfferId SemanticKey
  events : List (Proof.Event Fact)

/-- One package-owned binary split command. -/
structure Split (Fact Cause OfferId SemanticKey Plan : Type) where
  echo : Echo Fact Cause OfferId SemanticKey
  runtime : Search.Result.Split Plan Proof.Key
  left : Search.Result.Seed Fact
  right : Search.Result.Seed Fact

/-- One package invocation has exactly one controller interpretation. -/
inductive Command (Fact Cause OfferId SemanticKey Plan : Type)
  | continue (echo : Echo Fact Cause OfferId SemanticKey)
  | split (split : Split Fact Cause OfferId SemanticKey Plan)
  | target (echo : Echo Fact Cause OfferId SemanticKey) (target : Search.Result.Target)
  | refute (echo : Echo Fact Cause OfferId SemanticKey) (refute : Search.Result.Refute Proof.Key)
  | unknown (echo : Echo Fact Cause OfferId SemanticKey) (unknown : Search.Result.Unknown)
  | stop (code : Nat) (diagnostic : Option Trace.Event := none)

variable {Fact Cause OfferId SemanticKey Plan : Type}

def Command.reply : Command Fact Cause OfferId SemanticKey Plan →
    Search.Reply Fact Cause OfferId SemanticKey
  | .continue echo | .target echo _ | .refute echo _ | .unknown echo _ =>
      .outcome echo.outcome
  | Command.split proposal => .outcome proposal.echo.outcome
  | .stop code diagnostic => .failure code diagnostic

/-- One stable rule owner and its replaceable callback. The callback is
executed only after Search authenticates a selected action with this key. -/
structure Package (Fact Cause OfferId SemanticKey Plan : Type) where
  rule : RuleKey
  invoke : Search.Request Fact OfferId SemanticKey →
    Command Fact Cause OfferId SemanticKey Plan

/-- Ordinary-import-sealed exact alignment of a retained runtime tree and its
separate untrusted theorem recipe. -/
structure Bundle (Fact Cause Plan : Type) where
  private mk ::
  tree : Search.Result.Tree Fact Cause Plan Proof.Key
  recipe : Proof.TreeRecipe Fact
  /-- Cached complete logical recipe cost, rechecked on every transition. -/
  recipeCost : Search.Result.Cost

inductive Resource where
  | bytes
  | work
  deriving DecidableEq, Repr

inductive Error where
  | search (error : Search.Error)
  | result (error : Search.Result.Error)
  | proof (error : Proof.Error)
  | resource (resource : Resource)
  | mismatch
  deriving DecidableEq, Repr

/-- A checked invocation either advances the current node, retains a split or
terminal, records honest unknown state, or stops without changing the bundle. -/
inductive Step (Fact Cause OfferId SemanticKey Plan : Type)
  | continued (bundle : Bundle Fact Cause Plan)
      (session : Search.Session Fact Cause OfferId SemanticKey)
  | split (bundle : Bundle Fact Cause Plan)
  | terminal (bundle : Bundle Fact Cause Plan)
  | unknown (bundle : Bundle Fact Cause Plan)
  | stopped (stop : Search.Stop Unit Unit) (bundle : Bundle Fact Cause Plan)
      (session : Search.Session Fact Cause OfferId SemanticKey)

private def eventWithin (limits : Proof.Limits) : Proof.Event Fact → Except Error Unit
  | .fact step => do
      Proof.bodyCheck limits step.schema .fact step.body |>.mapError Error.proof
      Proof.dependenciesCheck limits step.assumptions |>.mapError Error.proof
  | .equality step => do
      Proof.bodyCheck limits step.schema .equality step.body |>.mapError Error.proof
      Proof.dependenciesCheck limits step.assumptions |>.mapError Error.proof
  | .transport _ => pure ()
  | .instance step =>
      Proof.bodyCheck limits step.schema .instance step.body |>.mapError Error.proof

/-- The supported callback driver retains only fact events: one event is
zipped with each accepted fact update. The general proof layer may replay
other event kinds when supplied through its separate programmatic APIs. -/
private def eventCost (measure : Measure Fact) : Proof.Event Fact → Except Error Search.Result.Cost
  | event@(.fact _) => pure (measure.cell + measure.event event)
  | _ => throw .mismatch

private def edgeCost (measure : Measure Fact) (edge : Proof.TreeEdge Fact) :
    Search.Result.Cost :=
  measure.cell + measure.edge edge

private def recipeCost (measure : Measure Fact) (recipe : Proof.TreeRecipe Fact) :
    Except Error Search.Result.Cost := do
  let mut total := measure.cell + measure.cell
  for events in recipe.events do
    total := total + measure.cell
    for event in events do total := total + (← eventCost measure event)
  for edge in recipe.edges do total := total + edgeCost measure edge
  pure total

private def recipeWithin (limits : RecipeLimits) (cost : Search.Result.Cost) :
    Except Error Unit := do
  if limits.maxBytes < cost.bytes then throw (.resource .bytes)
  if limits.maxWork < cost.work then throw (.resource .work)

private def edgesMatch [DecidableEq Fact]
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key)
    (recipe : Proof.TreeRecipe Fact) : Bool := Id.run do
  if tree.nodes.size != recipe.edges.size then return false
  for index in [0:tree.nodes.size] do
    let some node := tree.nodes[index]? | return false
    let some edge := recipe.edges[index]? | return false
    let source := node.source
    if edge.parent != source.parent || edge.side != source.side || edge.seed != source.seed then
      return false
  return true

private def checkRecipe [DecidableEq Fact]
    (limits : Limits) (tree : Search.Result.Tree Fact Cause Plan Proof.Key)
    (recipe : Proof.TreeRecipe Fact) : Except Error Unit := do
  Proof.checkTreeLimits limits.tree tree recipe |>.mapError Error.proof
  if !edgesMatch tree recipe then throw .mismatch
  for events in recipe.events do
    if limits.proof.maxChronology < events.length then throw (.proof .chronologyLimit)
    for event in events do eventWithin limits.proof event

private def validate [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits)
    (resultMeasure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (recipeMeasure : Measure Fact)
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key)
    (recipe : Proof.TreeRecipe Fact) : Except Error Search.Result.Cost := do
  if !tree.check limits.result resultMeasure then throw (.result .malformed)
  checkRecipe limits tree recipe
  let cost ← recipeCost recipeMeasure recipe
  recipeWithin limits.recipe cost
  pure cost

private def bundleWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits)
    (resultMeasure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (recipeMeasure : Measure Fact)
    (tree : Search.Result.Tree Fact Cause Plan Proof.Key)
    (recipe : Proof.TreeRecipe Fact) : Except Error (Bundle Fact Cause Plan) := do
  let recipeCost ← validate limits resultMeasure recipeMeasure tree recipe
  pure { tree, recipe, recipeCost }

private def checked [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits)
    (resultMeasure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (recipeMeasure : Measure Fact)
    (bundle : Bundle Fact Cause Plan) : Except Error (Bundle Fact Cause Plan) := do
  let cost ← validate limits resultMeasure recipeMeasure bundle.tree bundle.recipe
  if cost != bundle.recipeCost then throw .mismatch
  pure bundle

/-- Start an exact singleton bundle. The root chronology is initially empty. -/
opaque Bundle.startWithin [DecidableEq Fact] [DecidableEq Cause]
    (limits : Limits) (resultMeasure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (recipeMeasure : Measure Fact)
    (scope : Policy.ScopeId) (branch : State.Branch Fact Cause) :
    Except Error (Bundle Fact Cause Plan) := do
  let tree ← Search.Result.startWithin limits.result resultMeasure scope branch
    |>.mapError Error.result
  bundleWithin limits resultMeasure recipeMeasure tree { events := #[[]], edges := #[{}] }

private def factEventMatches [DecidableEq Fact]
    (request : Search.Request Fact OfferId SemanticKey)
    (update : State.Update Fact Cause) : Proof.Event Fact → Bool
  | .fact step =>
      step.scope == request.scope && step.programVersion == request.programVersion &&
      step.action == request.action && step.node == update.node &&
      step.previous == update.previous && step.version == update.version &&
      step.installed == update.fact && step.assumptions == request.action.inputs &&
      step.schema.rule == request.action.key && step.schema.role == .fact
  | _ => false

private def echoMatches [DecidableEq Fact]
    (limits : Limits) (transition : Search.Applied Fact Cause OfferId SemanticKey)
    (echo : Echo Fact Cause OfferId SemanticKey) : Except Error Unit := do
  if echo.events.length != echo.outcome.updates.size then
    throw .mismatch
  if limits.proof.maxChronology < echo.events.length then throw (.proof .chronologyLimit)
  for pair in echo.outcome.updates.toList.zip echo.events do
    if !factEventMatches transition.request pair.1 pair.2 then throw .mismatch
    eventWithin limits.proof pair.2

private def appendEvents (recipe : Proof.TreeRecipe Fact) (index : Nat)
    (events : List (Proof.Event Fact)) : Option (Proof.TreeRecipe Fact) := do
  let old ← recipe.events[index]?
  pure { recipe with events := recipe.events.set! index (old ++ events) }

private def appendChildren (recipe : Proof.TreeRecipe Fact)
    (parent : Search.Result.Id) (left right : Search.Result.Seed Fact) : Proof.TreeRecipe Fact :=
  { recipe with
    events := recipe.events.push [] |>.push []
    edges := recipe.edges
      |>.push { parent := some parent, side := some .left, seed := some left }
      |>.push { parent := some parent, side := some .right, seed := some right } }

private def emptyEcho (echo : Echo Fact Cause OfferId SemanticKey) : Bool :=
  echo.outcome.updates.isEmpty && echo.events.isEmpty

private def exactSplit (request : Search.Request Fact OfferId SemanticKey)
    (split : Search.Result.Split Plan Proof.Key) : Bool :=
  split.scope == request.scope && split.programVersion == request.programVersion &&
    split.action == request.action && split.action.kind == .split &&
    split.schema.rule == request.action.key && split.schema.role == .split

private def exactRefute (request : Search.Request Fact OfferId SemanticKey)
    (entry : Search.Result.Refute Proof.Key) : Bool :=
  entry.scope == request.scope && entry.programVersion == request.programVersion &&
    entry.seen.node == request.action.node && request.action.inputs.contains entry.seen &&
    entry.schema.rule == request.action.key && entry.schema.role == .refute

private def exactTarget (request : Search.Request Fact OfferId SemanticKey)
    (entry : Search.Result.Target) : Bool :=
  entry.scope == request.scope && entry.programVersion == request.programVersion &&
    entry.seen.node == request.action.node && request.action.inputs.contains entry.seen

/-- Execute exactly one selected package callback and atomically return its
checked retained-tree/recipe replacement. The callback result is retained
directly; no later cause-to-recipe reconstruction occurs. -/
opaque runWithin [DecidableEq Fact] [DecidableEq Cause] [DecidableEq OfferId]
    [DecidableEq SemanticKey] [DecidableEq Plan]
    (envelope : Search.Envelope) (policyMeasure : Policy.Measure OfferId SemanticKey)
    (limits : Limits) (resultMeasure : Search.Result.Measure Fact Cause Plan Proof.Key)
    (recipeMeasure : Measure Fact)
    (order : Search.Order) (package : Package Fact Cause OfferId SemanticKey Plan)
    (bundle : Bundle Fact Cause Plan)
    (session : Search.Session Fact Cause OfferId SemanticKey)
    (decision : Policy.Decision OfferId SemanticKey) :
    Except Error (Step Fact Cause OfferId SemanticKey Plan) := do
  let bundle ← checked limits resultMeasure recipeMeasure bundle
  let some (id, source) := Search.Result.current? bundle.tree | throw Error.mismatch
  if source.scope != session.scope || source.branch != session.branch then throw .mismatch
  let invocation ← Search.invokeWithWithin envelope policyMeasure package.rule
      (fun request =>
        let command := package.invoke request
        (command.reply, command)) session decision |>.mapError Error.search
  match invocation with
  | .stopped stop next => pure (.stopped stop bundle next)
  | .produced (.stopped stop next) command =>
      match command with
      | .stop _ _ => pure (.stopped stop bundle next)
      | _ => throw .mismatch
  | .produced (.applied transition) command =>
      match command with
      | .stop _ _ => throw .mismatch
      | .continue echo =>
          echoMatches limits transition echo
          if echo.outcome.updates.isEmpty then throw .mismatch
          let some recipe := appendEvents bundle.recipe id.index echo.events | throw .mismatch
          let tree ← Search.Result.advanceWithin limits.result resultMeasure bundle.tree transition
            |>.mapError Error.result
          let next ← bundleWithin limits resultMeasure recipeMeasure tree recipe
          pure (.continued next transition.after)
      | Command.split proposal =>
          echoMatches limits transition proposal.echo
          if !emptyEcho proposal.echo || !exactSplit transition.request proposal.runtime then
            throw .mismatch
          let tree ← Search.Result.splitWithin limits.result resultMeasure order bundle.tree
            proposal.runtime proposal.left proposal.right |>.mapError Error.result
          let recipe := appendChildren bundle.recipe id proposal.left proposal.right
          let next ← bundleWithin limits resultMeasure recipeMeasure tree recipe
          pure (.split next)
      | .target echo target =>
          echoMatches limits transition echo
          if !emptyEcho echo || !exactTarget transition.request target then throw .mismatch
          let tree ← Search.Result.settleWithin limits.result resultMeasure bundle.tree (.target target)
            |>.mapError Error.result
          let next ← bundleWithin limits resultMeasure recipeMeasure tree bundle.recipe
          pure (.terminal next)
      | .refute echo refute =>
          echoMatches limits transition echo
          if !emptyEcho echo || !exactRefute transition.request refute then throw .mismatch
          let tree ← Search.Result.settleWithin limits.result resultMeasure bundle.tree (.refute refute)
            |>.mapError Error.result
          let next ← bundleWithin limits resultMeasure recipeMeasure tree bundle.recipe
          pure (.terminal next)
      | .unknown echo unknown =>
          echoMatches limits transition echo
          if !emptyEcho echo || unknown.scope != transition.request.scope ||
              unknown.programVersion != transition.request.programVersion then throw .mismatch
          let tree ← Search.Result.settleWithin limits.result resultMeasure bundle.tree (.unknown unknown)
            |>.mapError Error.result
          let next ← bundleWithin limits resultMeasure recipeMeasure tree bundle.recipe
          pure (.unknown next)

end Hex.Interval.Driver
