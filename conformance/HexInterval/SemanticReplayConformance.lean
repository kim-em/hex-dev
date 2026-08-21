/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.SemanticReplay

/-!
Canary for semantic replay of two unrelated opaque unary functions.  The two
packages use different private certificate types and body encodings.  Both are
handled by the same exact-key dispatcher.
-/

namespace Hex.Interval.SemanticReplayConformance

open Experiment Propagator PayloadArena SemanticReplay

inductive Fact where
  | top
  | exact (value : Nat)
  deriving DecidableEq, Repr

namespace Fact

def Allows : Fact -> Nat -> Prop
  | .top, _ => True
  | .exact expected, actual => actual = expected

end Fact

structure UnaryMeaning where
  key : OpKey
  eval : Nat -> Nat

def Models (meanings : List UnaryMeaning) (program : Program)
    (valuation : NodeId -> Nat) : Prop :=
  ∀ meaning, meaning ∈ meanings ->
    ∀ output input instruction,
      program.node? output = some instruction ->
      (program.operation? instruction.op).map (fun operation => operation.key) =
        some meaning.key ->
      instruction.args = [input] ->
      valuation output = meaning.eval (valuation input)

def semantics (meanings : List UnaryMeaning) : Semantics Fact :=
  { Value := Nat
    models := Models meanings
    holds := fun _ valuation fact => fact.fact.Allows (valuation fact.node) }

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "semantic-replay.source" }
def leftOpKey : OpKey := { name := "semantic-replay.opaque-left" }
def rightOpKey : OpKey := { name := "semantic-replay.opaque-right" }
def leftRuleKey : RuleKey := { name := "semantic-replay.opaque-left.forward" }
def rightRuleKey : RuleKey := { name := "semantic-replay.opaque-right.forward" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def leftOperation : Operation :=
  { key := leftOpKey, inputs := [real], output := real }

def rightOperation : Operation :=
  { key := rightOpKey, inputs := [real], output := real }

def node (index : Nat) : NodeId := { index }

def instruction (operation : Nat) (args : List NodeId := []) : Node :=
  { domain := real, op := { index := operation }, args }

def program : Program :=
  { operations := #[sourceOperation, leftOperation, rightOperation]
    nodes :=
      #[instruction 0,
        instruction 1 [node 0],
        instruction 2 [node 0]] }

def leftMeaning : UnaryMeaning :=
  { key := leftOpKey, eval := fun value => value + 1 }

def rightMeaning : UnaryMeaning :=
  { key := rightOpKey, eval := fun value => value * 2 }

def meanings : List UnaryMeaning := [leftMeaning, rightMeaning]

theorem leftMeaning_mem : leftMeaning ∈ meanings :=
  List.Mem.head _

theorem rightMeaning_mem : rightMeaning ∈ meanings :=
  List.Mem.tail _ (List.Mem.head _)

theorem unaryEntails (meaning : UnaryMeaning) (member : meaning ∈ meanings)
    (program : Program) (input output : NodeId) (value : Nat)
    (instruction : Node)
    (nodeProof : program.node? output = some instruction)
    (operationProof :
      (program.operation? instruction.op).map (fun operation => operation.key) =
        some meaning.key)
    (argumentProof : instruction.args = [input]) :
    (semantics meanings).Entails program
      [{ node := input, fact := .exact value }]
      { node := output, fact := .exact (meaning.eval value) } := by
  intro valuation model assumptions
  have inputProof :
      (semantics meanings).holds program valuation
        { node := input, fact := .exact value } :=
    assumptions _ (List.Mem.head _)
  have operationLaw :=
    model meaning member output input instruction nodeProof operationProof argumentProof
  change valuation input = value at inputProof
  change valuation output = meaning.eval value
  rw [operationLaw, inputProof]

def replayUnary (meaning : UnaryMeaning) (member : meaning ∈ meanings)
    (input : CheckerInput Fact) (action : Action)
    (context : RuleFactContext input action) :
    Option (Evidence
      ((semantics meanings).Entails
        context.program context.assumptions context.proposed)) :=
  match context.assumptions, context.proposed with
  | [{ node := argument, fact := .exact value }],
      { node := output, fact := .exact proposed } =>
      if outputProof : output = action.node then
        match action.inputs with
        | [{ node := watched, version := _ }] =>
            if watchedProof : watched = argument then
              if proposedProof : proposed = meaning.eval value then
                match nodeProof : context.program.node? output with
                | none => none
                | some instruction =>
                    if argumentProof : instruction.args = [argument] then
                      if operationProof :
                          (context.program.operation? instruction.op).map
                              (fun operation => operation.key) =
                            some meaning.key then
                        some
                          { proof := by
                              subst output
                              subst watched
                              subst proposed
                              exact unaryEntails meaning member
                                context.program argument action.node value instruction
                                nodeProof operationProof argumentProof }
                      else none
                    else none
              else none
            else none
        | _ => none
      else none
  | _, _ => none

inductive LeftCertificate where
  | unit

inductive RightCertificate where
  | pair

def decodeLeft : List Nat -> Option LeftCertificate
  | [101] => some .unit
  | _ => none

def decodeRight : List Nat -> Option RightCertificate
  | [202, 203] => some .pair
  | _ => none

def leftSchema : PackedFactSchema (semantics meanings) :=
  { rule := leftRuleKey
    schema := 7
    Certificate := LeftCertificate
    decode := decodeLeft
    replay := fun input action context _ =>
      replayUnary leftMeaning leftMeaning_mem input action context }

def rightSchema : PackedFactSchema (semantics meanings) :=
  { rule := rightRuleKey
    schema := 7
    Certificate := RightCertificate
    decode := decodeRight
    replay := fun input action context _ =>
      replayUnary rightMeaning rightMeaning_mem input action context }

inductive RightEqualityCertificate where
  | reflexive

def decodeRightEquality : List Nat -> Option RightEqualityCertificate
  | [303] => some .reflexive
  | _ => none

/-- A small role-separation canary.  The schema accepts only a reflexive edge;
the engine would not admit such an edge, but the semantic dispatcher must
still inspect the exact endpoints supplied by structural replay rather than
trusting a recipe body in isolation. -/
def rightEqualitySchema : PackedEqualitySchema (semantics meanings) :=
  { rule := rightRuleKey
    schema := 8
    Certificate := RightEqualityCertificate
    decode := decodeRightEquality
    replay := fun _ _ context _ =>
      if endpointProof : context.edge.left = context.edge.right then
        some
          { proof := by
              intro valuation _ _
              rw [endpointProof] }
      else
        none }

def leftProofs : SemanticReplay.Package (semantics meanings) :=
  { factSchemas := #[leftSchema] }

def rightProofs : SemanticReplay.Package (semantics meanings) :=
  { factSchemas := #[rightSchema]
    equalitySchemas := #[rightEqualitySchema] }

def noProofs : SemanticReplay.Package (semantics meanings) :=
  { factSchemas := #[] }

def rightFactOnlyProofs : SemanticReplay.Package (semantics meanings) :=
  { factSchemas := #[rightSchema] }

def duplicateLeftProofs : SemanticReplay.Package (semantics meanings) :=
  { factSchemas := #[leftSchema, leftSchema] }

def checkerInput : CheckerInput Fact :=
  { baseProgram := program
    initialFacts := #[.exact 3, .top, .top]
    target := { node := node 2, fact := .exact 6 } }

def action (serial application rule : Nat) (key : RuleKey)
    (target input : NodeId) : Action :=
  { serial
    programVersion := 0
    application := { index := application }
    rule := { index := rule }
    key
    node := target
    kind := .forward
    effort := 0
    inputs := [{ node := input, version := 0 }]
    writes := [target] }

def leftAction : Action :=
  action 0 0 0 leftRuleKey (node 1) (node 0)

def rightAction : Action :=
  action 1 1 1 rightRuleKey (node 2) (node 0)

def registration (key : RuleKey) (head : OpKey) : Registration :=
  { key
    head
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def leftFormat : ReplayFormat :=
  { role := .fact
    schema := 7
    validateBody := fun body => body == [101] }

def rightFormat : ReplayFormat :=
  { role := .fact
    schema := 7
    validateBody := fun body => body == [202, 203] }

def rightEqualityFormat : ReplayFormat :=
  { role := .equality
    schema := 8
    validateBody := fun body => body == [303] }

def payload : PayloadId := { index := 700 }

def leftPlan (request : RuleRequest Fact) : Plan Fact :=
  match request.writes with
  | [target] =>
      { outcome :=
          .success
            [{ node := target, fact := .exact 4, payload }]
            [] { estimatedProofNodes := 1 }
        drafts :=
          [{ label := payload, role := .fact, schema := 7, body := [101] }] }
  | _ => { outcome := .failed 1, drafts := [] }

def rightPlan (request : RuleRequest Fact) : Plan Fact :=
  match request.writes with
  | [target] =>
      { outcome :=
          .success
            [{ node := target, fact := .exact 6, payload }]
            [] { estimatedProofNodes := 1 }
        drafts :=
          [{ label := payload, role := .fact, schema := 7, body := [202, 203] }] }
  | _ => { outcome := .failed 2, drafts := [] }

def leftRuntime : Propagator.Package Fact :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, leftOperation]
    handlers :=
      #[Handler.statelessPlanned
          (registration leftRuleKey leftOpKey) leftPlan #[leftFormat]] }

def rightRuntime : Propagator.Package Fact :=
  { Cache := Unit
    cache := ()
    operations := #[rightOperation]
    handlers :=
      #[Handler.statelessPlanned
          (registration rightRuleKey rightOpKey) rightPlan
          #[rightFormat, rightEqualityFormat]] }

def limits : Hex.Interval.State.Limits :=
  { maxOperations := 3
    maxNodes := 3
    maxRules := 2
    maxRegistryEntries := 8
    maxReplayFormats := 3
    maxArity := 1
    maxApplications := 2
    maxQueueEntries := 4
    maxActions := 4
    maxAcceptedFacts := 2
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 8
    maxDiagnosticValue := 8
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 1
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 0
        maxAlignmentShift := 0 } }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 2
    maxBodyCells := 3
    maxDrafts := 1
    maxDraftCells := 3
    maxAtom := 303
    maxSchema := 8
    maxUses := 1 }

def executable? : Option (Propagator.Registry Fact) :=
  match Propagator.Registry.buildWithin limits #[leftRuntime, rightRuntime] with
  | .ok registry => some registry
  | .error _ => none

def view : ProgramView :=
  { programVersion := 0
    operations := program.operations
    nodes := program.nodes
    generations := #[0, 0, 0]
    depths := #[0, 1, 1] }

def request (action : Action) (target : NodeId) : RuleRequest Fact :=
  { action
    program := view
    inputs := [{ node := node 0, fact := .exact 3, version := 0 }]
    writes := [target] }

def leftRequest : RuleRequest Fact :=
  request leftAction (node 1)

def rightRequest : RuleRequest Fact :=
  request rightAction (node 2)

def retain? (arena : Arena) (request : RuleRequest Fact)
    (invocation : Invocation Fact) : Option (Arena × Entry) :=
  let plan := invocation.plan
  match invocation.replay.freeze arenaLimits arena request.action
      plan.outcome plan.drafts with
  | .ready arena (.success [candidate] [] _) => do
      let entry ← arena.entry? candidate.payload .fact
      pure (arena, entry)
  | _ => none

structure Fixture where
  registry : SemanticReplay.Registry (semantics meanings)
  arena : Arena
  leftEntry : Entry
  rightEntry : Entry

def fixture? : Option Fixture := do
  let executable ← executable?
  let registry ←
    match SemanticReplay.Registry.build executable #[leftProofs, rightProofs] with
    | .ok registry => some registry
    | .error _ => none
  let (leftInvocation, executable) := executable.invokePlanned leftRequest
  match retain? .empty leftRequest leftInvocation with
  | none => none
  | some (arena, leftEntry) =>
      let (rightInvocation, _) := executable.invokePlanned rightRequest
      match retain? arena rightRequest rightInvocation with
      | none => none
      | some (arena, rightEntry) =>
          pure { registry, arena, leftEntry, rightEntry }

def leftContext (entry : Entry) : RuleFactContext checkerInput entry.origin :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := [{ node := node 0, fact := .exact 3 }]
    proposed := { node := node 1, fact := .exact 4 } }

def rightContext (entry : Entry) : RuleFactContext checkerInput entry.origin :=
  { program
    basePrefix := ProgramPrefix.refl program
    assumptions := [{ node := node 0, fact := .exact 3 }]
    proposed := { node := node 2, fact := .exact 6 } }

#guard
  match fixture? with
  | some fixture =>
      fixture.arena.entries.size == 2 && fixture.arena.bodyCells == 3 &&
        fixture.leftEntry.replayKey == leftSchema.key &&
        fixture.rightEntry.replayKey == rightSchema.key &&
        (fixture.registry.dispatchFact checkerInput fixture.leftEntry
          (leftContext fixture.leftEntry)).isSome &&
        (fixture.registry.dispatchFact checkerInput fixture.rightEntry
          (rightContext fixture.rightEntry)).isSome &&
        fixture.registry.coverage.factFormats ==
          #[leftSchema.key, rightSchema.key] &&
        fixture.registry.coverage.instanceFormats.isEmpty &&
        fixture.registry.coverage.equalityFormats ==
          #[rightEqualitySchema.key]
  | none => false

-- The semantic package table is paired positionally with the sealed
-- executable package table; omissions cannot shift later ownership.
#guard
  match executable? with
  | some executable =>
      match SemanticReplay.Registry.build executable #[leftProofs] with
      | .error (.packageCount executable semantic) =>
          executable == 2 && semantic == 1
      | _ => false
  | none => false

-- Exact duplicate checker addresses are rejected even within their owner.
#guard
  match executable? with
  | some executable =>
      match SemanticReplay.Registry.build executable
          #[duplicateLeftProofs, rightProofs] with
      | .error (.duplicateSchema key) => key == leftSchema.key
      | _ => false
  | none => false

-- Coverage is bidirectional in every role: omitting the right package's fact
-- checker is a precise assembly error even though its equality checker exists.
#guard
  match executable? with
  | some executable =>
      match SemanticReplay.Registry.build executable #[leftProofs, noProofs] with
      | .error (.missingSchema package key) =>
          package == 1 && key == rightSchema.key
      | _ => false
  | none => false

-- Non-fact formats are no longer deferred: omitting an equality theorem is
-- an exact coverage error at semantic-registry construction.
#guard
  match executable? with
  | some executable =>
      match SemanticReplay.Registry.build executable
          #[leftProofs, rightFactOnlyProofs] with
      | .error (.missingSchema package key) =>
          package == 1 && key == rightEqualitySchema.key
      | _ => false
  | none => false

-- Package position and the complete replay key prevent a checker contributed
-- by the right package from being installed as the left package's schema,
-- even though both packages deliberately use fact schema number seven.
#guard
  match executable? with
  | some executable =>
      match SemanticReplay.Registry.build executable #[rightProofs, leftProofs] with
      | .error (.unownedSchema package key) =>
          package == 0 && key == rightSchema.key
      | _ => false
  | none => false

-- A right-owned retained address never falls back to the left decoder merely
-- because its untrusted body contains the left package's private encoding.
#guard
  match fixture? with
  | some fixture =>
      let wrong := { fixture.rightEntry with body := [101] }
      (fixture.registry.dispatchFact checkerInput wrong
        (rightContext wrong)).isNone
  | none => false

-- Exact dispatch includes the role.  A covered equality address cannot reach
-- the fact theorem at the same rule.
#guard
  match fixture? with
  | some fixture =>
      let equality :=
        { fixture.rightEntry with role := .equality, schema := 8, body := [303] }
      (fixture.registry.dispatchFact checkerInput equality
        (rightContext equality)).isNone
  | none => false

def rightEqualityEntry : Entry :=
  { origin := rightAction
    role := .equality
    schema := 8
    body := [303] }

def rightEqualityEdge : EqualityEdge :=
  { left := node 2
    right := node 2
    generation := 0
    origin := rightAction
    payload := { index := 2 } }

def withRightEquality (arena : Arena) (entry : Entry := rightEqualityEntry) : Arena :=
  { entries := arena.entries.push entry
    bodyCells := arena.bodyCells + entry.body.length }

-- Public replay follows the retained edge's payload into the arena, checks
-- the complete originating action, and dispatches the exact equality schema.
#guard
  match fixture? with
  | some fixture =>
      (fixture.registry.replayEquality checkerInput
        (withRightEquality fixture.arena) { index := 0 } rightEqualityEdge
        program (ProgramPrefix.refl program) []).isSome
  | none => false

-- A transplanted entry with the right role/schema/body is rejected before
-- package theorem dispatch because its complete originating action differs.
#guard
  match fixture? with
  | some fixture =>
      let transplanted := { rightEqualityEntry with origin := leftAction }
      (fixture.registry.replayEquality checkerInput
        (withRightEquality fixture.arena transplanted) { index := 0 }
        rightEqualityEdge program (ProgramPrefix.refl program) []).isNone
  | none => false

-- The package theorem checks the exact endpoints rather than accepting a
-- valid-looking body for an unrelated edge.
#guard
  match fixture? with
  | some fixture =>
      let edge := { rightEqualityEdge with left := node 1 }
      (fixture.registry.replayEquality checkerInput
        (withRightEquality fixture.arena) { index := 0 } edge
        program (ProgramPrefix.refl program) []).isNone
  | none => false

def meetEvidence (previous proposed installed : Fact) :
    Option (Evidence
      (∀ value, installed.Allows value ↔
        previous.Allows value ∧ proposed.Allows value)) :=
  match previous, proposed, installed with
  | .top, .top, .top =>
      some { proof := by intro; simp [Fact.Allows] }
  | .top, .exact expected, .exact actual =>
      if valueProof : actual = expected then
        some { proof := by subst actual; intro; simp [Fact.Allows] }
      else none
  | .exact expected, .top, .exact actual =>
      if valueProof : actual = expected then
        some { proof := by subst actual; intro; simp [Fact.Allows] }
      else none
  | .exact left, .exact right, .exact installed =>
      if equalProof : left = right then
        if installedProof : installed = left then
          some
            { proof := by
                subst right
                subst installed
                intro
                simp [Fact.Allows] }
        else none
      else none
  | _, _, _ => none

def factDomain : FactDomainSchema (semantics meanings) :=
  { top := fun _ => .top
    topSound := by
      intro _ _ _ _ _ _
      trivial
    proveMeet := fun _ node previous proposed installed =>
      match meetEvidence previous proposed installed with
      | none => none
      | some evidence =>
          some
            { proof := by
                intro valuation _
                exact evidence.proof (valuation node) } }

example : (factDomain.proveMeet program (node 1) .top (.exact 4) (.exact 4)).isSome =
    true := by
  decide

def event (version value : Nat) : Hex.Interval.State.Update Fact (FactCause Fact) :=
  { programVersion := 0
    node := node 1
    previous := { node := node 1, version := version - 1 }
    fact := .exact value
    version
    cause := .rule leftAction (.exact value) { index := 0 } }

def trace (arena : Arena) : Trace Fact :=
  { program
    events := #[event 1 4, event 2 5]
    arena }

/-- A future event is physically present but inaccessible before its cursor. -/
example (arena : Arena) :
    (trace arena).eventFactAt? 1 { node := node 1, version := 2 } = none := by
  rfl

example (arena : Arena) :
    (trace arena).eventFactAt? 2 { node := node 1, version := 2 } =
      some (.exact 5) := by
  rfl

end Hex.Interval.SemanticReplayConformance
