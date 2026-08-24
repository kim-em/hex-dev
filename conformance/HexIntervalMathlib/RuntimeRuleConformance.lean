/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib.RuntimeRule
import HexIntervalMathlib.RuntimeTerminal

/-!
# Executable arithmetic-rule conformance

The canary assembles every public arithmetic handler, starts a sealed typed
runtime from the frontend-shaped version-zero facts, directly executes unary
and repeated-input binary rules, settles the exact final target, and replays
the complete retained chronology through `RuntimeTerminal`. No fallback theorem
or independently reconstructed arithmetic proof is used.
-/

namespace Hex.IntervalMathlib.RuntimeRuleConformance

open Hex.Interval
open Hex.Interval.Executable
open Hex.Interval.Rule
open Hex.Interval.Rule.Runtime

private def liftOption {α : Type} : Option α → Option (ULift.{1, 0} α)
  | some value => some ⟨value⟩
  | none => none

/-- error: Unknown constant `Hex.Interval.Rule.Runtime.Registry.mk` -/
#guard_msgs in
#check Rule.Runtime.Registry.mk

def d (value : Int) : Dyadic := .ofInt value

def endpoint : EndpointLimit :=
  { maxEndpointHeight := 64, maxAlignmentShift := 64 }

def config : Rule.Config :=
  { endpoint
    powerWork := { maxExponent := 8 }
    exponent := 2
    precisionLimits :=
      { endpoint, maxPrecisionMagnitude := 64, maxPrecisionBits := 64,
        maxTemporaryBits := 128 }
    precision := 0
    constant := d 0 }

def node (op : Nat) (args : List Nat) : Node :=
  { domain := Rule.realDomain, op := { index := op },
    args := args.map fun index => { index } }

/-- One source followed by one node for every executable built-in rule. Binary
rows deliberately repeat the source node, exercising valid repeated slots. -/
def program : Program :=
  { operations := Rule.operations
    nodes :=
      #[node 0 [], node 1 [0], node 2 [0, 0], node 3 [0, 0], node 4 [0, 0],
        node 5 [0], node 6 [0], node 7 [0, 0], node 8 [0, 0], node 9 [],
        node 10 [0], node 11 [0, 0], node 12 [0]] }

def point (value : Int) : Hex.Interval :=
  match singletonWithin endpoint (d value) with
  | .ready interval => interval
  | .resourceLimit _ => Hex.Interval.empty

def facts : Array Hex.Interval :=
  #[point 1, Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole,
    Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole,
    Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole,
    Hex.Interval.whole, Hex.Interval.whole, Hex.Interval.whole]

def stateLimits : State.Limits :=
  { maxOperations := 13, maxNodes := 13, maxRules := 12,
    maxRegistryEntries := 64, maxReplayFormats := 12, maxArity := 2,
    maxScopeNodes := 0, maxApplications := 12, maxQueueEntries := 16,
    maxActions := 12, maxMatcherVisits := 0, matcherBatchSize := 0,
    maxAcceptedFacts := 12, maxRetainedSuggestions := 0, maxEffort := 0,
    maxObservationValue := 16, maxDiagnosticValue := 16,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0,
    maxProposalItems := 1, maxInstances := 0, maxGeneration := 0,
    maxNodeDepth := 1, maxEqualities := 0, splitEndpointLimit := endpoint }

def executableLimits : Executable.Limits :=
  { state := stateLimits, maxPackages := 1,
    maxMetadataBytes := 64, maxMetadataWork := 64,
    maxCacheBytes := 12, maxCacheWork := 12,
    maxResultBytes := 1, maxResultWork := 1,
    maxQuotes := 1, maxQuoteCells := 1, maxAtom := 12, maxSchema := 1 }

def runtimeLimits : Hex.Interval.Runtime.Limits :=
  { executable := executableLimits, maxEvents := 1 }

def proofLimits : Proof.Limits :=
  { maxPackages := 1, maxSchemas := 12, maxBodyCells := 1,
    maxDependencies := 2, maxChronology := 12 }

def key : RuntimeProof.Key := { name := "arithmetic-runtime", version := 1 }

def registry? : Option (Rule.Runtime.Registry config) :=
  (Rule.Runtime.buildWithin executableLimits proofLimits key config program).toOption

def branch? : Option (State.Branch Hex.Interval Rule.Runtime.Cause) :=
  (State.Branch.startWithin stateLimits program facts).toOption

def runtime? : Option (Hex.Interval.Runtime.State Hex.Interval Rule.Runtime.Cause) := do
  match registry?, branch? with
  | some registry, some branch =>
      (Hex.Interval.Runtime.State.startWithin runtimeLimits registry.assembly branch).toOption
  | _, _ => none

def seen (index version : Nat) : SeenVersion :=
  { node := { index }, version }

def action (serial application rule : Nat) (key : RuleKey)
    (inputs : List SeenVersion) : Action :=
  { serial, programVersion := 0, application := { index := application },
    rule := { index := rule }, key, node := { index := application + 1 },
    kind := .forward, effort := 0, inputs, writes := [{ index := application + 1 }] }

def actions : List Action :=
  [action 0 0 0 Rule.negKey [seen 0 0],
   action 1 1 1 Rule.addKey [seen 0 0, seen 0 0],
   action 2 2 2 Rule.subKey [seen 0 0, seen 0 0],
   action 3 3 3 Rule.mulKey [seen 0 0, seen 0 0],
   action 4 4 4 Rule.powKey [seen 0 0],
   action 5 5 5 Rule.absKey [seen 0 0],
   action 6 6 6 Rule.minKey [seen 0 0, seen 0 0],
   action 7 7 7 Rule.maxKey [seen 0 0, seen 0 0],
   action 8 8 8 Rule.constantKey [],
   action 9 9 9 Rule.invKey [seen 0 0],
   action 10 10 10 Rule.divKey [seen 0 0, seen 0 0],
   action 11 11 11 Rule.regularizeKey [seen 0 0]]

private def run
    (state : Hex.Interval.Runtime.State Hex.Interval Rule.Runtime.Cause) :
    List Action → Option
      (Array (Hex.Interval.Runtime.Applied Hex.Interval Rule.Runtime.Cause) ×
        Hex.Interval.Runtime.State Hex.Interval Rule.Runtime.Cause)
  | [] => some (#[], state)
  | next :: rest => do
      let (transition, state) ← (state.stepWithin runtimeLimits next).toOption
      let (transitions, state) ← run state rest
      pure (#[transition] ++ transitions, state)

def run? := runtime?.bind fun state => run state actions

private def exactFact (index : Nat)
    (transition : Hex.Interval.Runtime.Applied Hex.Interval Rule.Runtime.Cause) : Bool :=
  match transition.events[0]? with
  | some (Hex.Interval.Runtime.Event.fact step) =>
      step.action == actions[index]? && step.update.node.index == index + 1 &&
        step.update.previous == seen (index + 1) 0 && step.update.version == 1 &&
        step.proposed == step.update.fact && step.quote.role == .fact &&
        step.quote.schema == 1 && step.quote.body == [index + 1] &&
        step.update.cause.rule == step.action.key &&
        step.update.cause.body == step.quote.body
  | _ => false

#guard program.check
#guard registry?.isSome
#guard branch?.isSome
#guard runtime?.isSome
#guard run?.any fun (transitions, state) =>
  transitions.size == 12 && state.serial == 12 &&
    (List.range 12).all fun index =>
      transitions[index]?.any (exactFact index)

/-! ## Retained quotation without a terminal -/

def searchLimits : Search.Limits :=
  { maxSteps := 13, maxSplits := 0, maxLeaves := 1, maxFrontier := 1,
    maxDepth := 0, maxScopes := 1, leafFuel := 12 }

def resultLimits : Search.Result.Limits :=
  { search := searchLimits, runtime := runtimeLimits, maxNodes := 1,
    maxBodyCells := 12, maxBytes := 65536, maxWork := 65536, maxCode := 16 }

def unitCost : Search.Result.Cost := { bytes := 1, work := 1 }

def measure : Search.Result.Measure Hex.Interval Rule.Runtime.Cause (List Nat) Proof.Key :=
  { node := unitCost
    branch := fun branch =>
      { bytes := branch.program.nodes.size + branch.history.size,
        work := branch.program.nodes.size + branch.history.size }
    fact := fun _ => unitCost
    action := fun _ => unitCost
    plan := fun _ => unitCost
    schema := fun _ => unitCost
    body := fun _ => unitCost
    code := fun _ => unitCost }

def adapterLimits : RuntimeProof.Limits :=
  { result := resultLimits, proof := proofLimits,
    tree := { maxNodes := 1, maxDepth := 0, maxBodyCells := 12, maxWork := 32 },
    maxTransitions := 12, maxEvents := 12, maxStructuralCells := 512 }

private def runTree
    (tree : Search.Result.Tree Hex.Interval Rule.Runtime.Cause (List Nat) Proof.Key)
    (state : Hex.Interval.Runtime.State Hex.Interval Rule.Runtime.Cause) :
    List Action → Option
      (Search.Result.Tree Hex.Interval Rule.Runtime.Cause (List Nat) Proof.Key ×
        Hex.Interval.Runtime.State Hex.Interval Rule.Runtime.Cause)
  | [] => some (tree, state)
  | next :: rest => do
      let (transition, state) ← (state.stepWithin runtimeLimits next).toOption
      let tree := (← liftOption
        (Search.Result.advanceRuntimeWithin resultLimits measure tree transition).toOption).down
      runTree tree state rest

def treeRun? : Option
    (Search.Result.Tree Hex.Interval Rule.Runtime.Cause (List Nat) Proof.Key ×
      Hex.Interval.Runtime.State Hex.Interval Rule.Runtime.Cause) :=
  match branch?, runtime? with
  | some branch, some runtime =>
      match Search.Result.startWithin resultLimits measure { index := 0 } branch with
      | .ok tree => runTree tree runtime actions
      | .error _ => none
  | _, _ => none

def bundle? : Option
    (RuntimeProof.Bundle Hex.Interval (Rule.semantics config) Rule.Runtime.Cause (List Nat)) := do
  match registry?, treeRun? with
  | some registry, some (tree, _) =>
      (RuntimeProof.quoteTreeWithin adapterLimits measure registry tree).toOption
  | _, _ => none

#guard treeRun?.any fun (tree, _) =>
  tree.transitions.size == 12 && tree.pending.length == 1
#guard bundle?.any fun bundle =>
  bundle.recipe.events.size == 1 &&
    bundle.recipe.events[0]?.any fun events =>
      events.length == 12 && (List.range 12).all fun index =>
        match events[index]? with
        | some (Proof.Event.fact step) =>
            actions[index]?.any fun action =>
              step.schema == Rule.schemaKey action.key &&
                step.body == [index + 1] && step.proposed == step.installed
        | _ => false

/-! ## Exact target settlement and semantic replay -/

def input : Proof.Input Hex.Interval :=
  { scope := { index := 0 }, program, facts,
    target := { node := { index := 12 }, fact := point 1 } }

def policyLimits : Policy.Limits :=
  { maxOffers := 12, maxBytes := 4096, maxPairs := 64, maxWork := 64,
    maxScore := 0 }

def traceLimits : Trace.Limit :=
  { maxEvents := 0, maxBytes := 0, maxWork := 0, maxCode := 16 }

def envelope : Search.Envelope :=
  { state := stateLimits, policy := policyLimits, trace := traceLimits,
    search := searchLimits }

def controllerLimits : Hex.Interval.Runtime.Controller.Limits :=
  { maxChoices := 0, result := resultLimits }

def checked? : Option (RuntimeTerminal.Checked Hex.Interval
    (Rule.semantics config) Rule.Runtime.Cause (List Nat)) := do
  let registry ← registry?
  let (tree, runtime) ← treeRun?
  let controller ← (Hex.Interval.Runtime.Controller.State.startWithin
    controllerLimits envelope measure runtime tree).toOption
  let active ← (RuntimeTerminal.Active.startWithin registry input controller).toOption
  let lineage ← (active.targetWithin resultLimits measure (seen 12 1)).toOption
  (lineage.quoteWithin adapterLimits measure).toOption

/-- This calls the theorem fold owned by the checked token, then transports its
dependent result only after confirming the token retained this exact input. -/
def replay? : Option (Proof.Evidence ((Rule.semantics config).Entails input.program
    (Proof.initialBase input) input.target)) :=
  match checked? with
  | none => none
  | some checked =>
      match RuntimeTerminal.Checked.replay adapterLimits measure
          (Rule.domain config) (Rule.laws config) checked with
      | .error _ => none
      | .ok evidence =>
          if h : RuntimeTerminal.Checked.input checked = input then
            some (h ▸ evidence)
          else none

#guard checked?.isSome
#guard replay?.isSome

/-! ## Cache, resource, and seal failures -/

def oneCacheLimits : Hex.Interval.Runtime.Limits :=
  { runtimeLimits with executable :=
      { executableLimits with maxCacheBytes := 1, maxCacheWork := 1 } }

def oneCacheRuntime? : Option
    (Hex.Interval.Runtime.State Hex.Interval Rule.Runtime.Cause) := do
  match registry?, branch? with
  | some registry, some branch =>
      (Hex.Interval.Runtime.State.startWithin oneCacheLimits registry.assembly branch).toOption
  | _, _ => none

#guard oneCacheRuntime?.any fun state =>
  match actions[0]?, actions[1]? with
  | some first, some second =>
      match state.stepWithin oneCacheLimits first with
      | .ok (_, next) =>
          match next.stepWithin oneCacheLimits second with
          | .error (.executable (.resource .cacheBytes)) =>
              (state.stepWithin oneCacheLimits first).isOk
          | _ => false
      | _ => false
  | _, _ => false

#guard runtime?.any fun state =>
  actions[0]?.any fun first =>
    match state.stepWithin runtimeLimits { first with key := Rule.addKey } with
    | .error (.executable .invalidRequest) => true
    | _ => false

/-! ## Paired opaque-operation extension -/

def opaqueOp : Operation :=
  { key := { name := "conformance.runtime.opaque" },
    inputs := [Rule.realDomain], output := Rule.realDomain }

def opaqueMeaning : Program.Meaning ℝ :=
  { operation := opaqueOp, relation := fun _ _ => True }

def opaqueKey : RuleKey := { name := "conformance.runtime.opaque.forward" }

def opaqueRule : Registration :=
  Rule.unaryRegistration opaqueKey opaqueOp

def opaqueQuote : Executable.Quote :=
  { role := .fact, schema := 1, body := [13] }

def opaqueBatch (request : RuleRequest Hex.Interval) :
    Hex.Interval.Runtime.Batch Hex.Interval Rule.Runtime.Cause :=
  { events := #[.fact
      { action := request.action
        update :=
          { programVersion := request.action.programVersion
            node := request.action.node
            previous := { node := request.action.node, version := 0 }
            fact := Hex.Interval.whole
            version := 1
            cause := { rule := opaqueKey, body := opaqueQuote.body } }
        proposed := Hex.Interval.whole
        quote := opaqueQuote }] }

def opaqueHandler : Handler Hex.Interval
    (Hex.Interval.Runtime.Batch Hex.Interval Rule.Runtime.Cause) Unit :=
  { registration := opaqueRule
    invoke := fun cache request =>
      ({ result := opaqueBatch request, quotes := #[opaqueQuote] }, cache)
    formats :=
      #[{ role := .fact, schema := 1, validateBody := fun body => body == [13] }] }

def opaqueExecutable : Executable.Package Hex.Interval
    (Hex.Interval.Runtime.Batch Hex.Interval Rule.Runtime.Cause) :=
  { Cache := Unit, cache := (), operations := #[opaqueOp], handlers := #[opaqueHandler]
    measure :=
      { metadata := { bytes := 1, work := 1 }
        application := fun _ => { bytes := 1, work := 1 }
        cache := fun _ => {}
        result := fun batch => { bytes := batch.events.size, work := batch.events.size } } }

def opaqueSchema : Proof.FactSchema (Rule.semantics
    { config with extraMeanings := #[opaqueMeaning] }) :=
  { key := { rule := opaqueKey, role := .fact, bodySchema := 1 }
    Certificate := Unit
    decode := fun body => if body == [13] then some () else none
    prove := fun context _ =>
      if proposed : context.proposed.fact = Hex.Interval.whole then
        some
          { proof := by
              intro valuation _ _
              have whole : Hex.Interval.whole.Contains
                  (valuation context.proposed.node) := by
                change Raw.Contains Hex.Interval.whole.view _
                rw [Hex.Interval.view_whole]
                exact ⟨trivial, trivial⟩
              simpa [Rule.semantics, Proof.Semantics.ofMeanings, proposed] using whole }
      else none }

def opaqueProof : Proof.Package (Rule.semantics
    { config with extraMeanings := #[opaqueMeaning] }) :=
  { registrations := #[opaqueRule], facts := #[opaqueSchema] }

def extendedConfig : Rule.Config :=
  { config with extraMeanings := #[opaqueMeaning] }

def opaqueNode : Node :=
  { domain := Rule.realDomain, op := { index := 13 }, args := [{ index := 0 }] }

def extendedProgram : Program :=
  { operations := Rule.operations.push opaqueOp,
    nodes := program.nodes.push opaqueNode }

def extendedStateLimits : State.Limits :=
  { maxOperations := 14, maxNodes := 14, maxRules := 13,
    maxRegistryEntries := 72, maxReplayFormats := 13, maxArity := 2,
    maxScopeNodes := 0, maxApplications := 13, maxQueueEntries := 16,
    maxActions := 13, maxMatcherVisits := 0, matcherBatchSize := 0,
    maxAcceptedFacts := 13, maxRetainedSuggestions := 0, maxEffort := 0,
    maxObservationValue := 16, maxDiagnosticValue := 16,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0,
    maxProposalItems := 1, maxInstances := 0, maxGeneration := 0,
    maxNodeDepth := 1, maxEqualities := 0, splitEndpointLimit := endpoint }

def extendedExecutableLimits : Executable.Limits :=
  { state := extendedStateLimits, maxPackages := 2,
    maxMetadataBytes := 72, maxMetadataWork := 72,
    maxCacheBytes := 13, maxCacheWork := 13,
    maxResultBytes := 1, maxResultWork := 1,
    maxQuotes := 1, maxQuoteCells := 1, maxAtom := 13, maxSchema := 1 }

def extendedRuntimeLimits : Hex.Interval.Runtime.Limits :=
  { executable := extendedExecutableLimits, maxEvents := 1 }

def extendedProofLimits : Proof.Limits :=
  { maxPackages := 2, maxSchemas := 13, maxBodyCells := 1,
    maxDependencies := 2, maxChronology := 13 }

def extendedRegistry? : Option (Rule.Runtime.Registry extendedConfig) :=
  (Rule.Runtime.buildWithWithin extendedExecutableLimits extendedProofLimits
    { name := "arithmetic-runtime-opaque", version := 1 } extendedConfig extendedProgram
    #[opaqueExecutable] #[opaqueProof]).toOption

def extendedFacts : Array Hex.Interval := facts.push Hex.Interval.whole

def extendedRuntime? : Option
    (Hex.Interval.Runtime.State Hex.Interval Rule.Runtime.Cause) :=
  match extendedRegistry?,
      State.Branch.startWithin extendedStateLimits extendedProgram extendedFacts with
  | some registry, .ok branch =>
      (Hex.Interval.Runtime.State.startWithin extendedRuntimeLimits
        registry.assembly branch).toOption
  | _, _ => none

def opaqueAction : Action :=
  { serial := 0, programVersion := 0, application := { index := 12 },
    rule := { index := 12 }, key := opaqueKey, node := { index := 13 },
    kind := .forward, effort := 0, inputs := [seen 0 0], writes := [{ index := 13 }] }

#guard extendedProgram.check
#guard extendedRegistry?.isSome
#guard
  match Rule.Runtime.buildWithWithin extendedExecutableLimits extendedProofLimits
      { name := "missing-opaque-proof", version := 1 } extendedConfig extendedProgram
      #[opaqueExecutable] #[] with
  | .error (.registry .invalidRegistry) => true
  | _ => false
#guard
  match Rule.Runtime.buildWithWithin extendedExecutableLimits extendedProofLimits
      { name := "missing-opaque-runtime", version := 1 } extendedConfig extendedProgram
      #[] #[opaqueProof] with
  | .error (.registry .invalidRegistry) => true
  | _ => false
#guard
  match Rule.Runtime.buildWithWithin
      { extendedExecutableLimits with maxPackages := 1 }
      extendedProofLimits { name := "opaque-package-limit", version := 1 }
      extendedConfig extendedProgram #[opaqueExecutable] #[opaqueProof] with
  | .error (.executable (.resource .packages)) => true
  | _ => false
#guard extendedRuntime?.any fun state =>
  match state.stepWithin extendedRuntimeLimits opaqueAction with
  | .ok (transition, next) =>
      next.branch.factAt? (seen 13 1) == some Hex.Interval.whole &&
        match transition.events[0]? with
        | some (Hex.Interval.Runtime.Event.fact step) =>
            step.quote == opaqueQuote && step.proposed == Hex.Interval.whole &&
              step.update.fact == Hex.Interval.whole
        | _ => false
  | _ => false

def extendedResultLimits : Search.Result.Limits :=
  { search := { searchLimits with maxSteps := 1, leafFuel := 1 },
    runtime := extendedRuntimeLimits, maxNodes := 1, maxBodyCells := 1,
    maxBytes := 16384, maxWork := 16384, maxCode := 16 }

def extendedMeasure : Search.Result.Measure Hex.Interval Rule.Runtime.Cause
    (List Nat) Proof.Key :=
  { measure with branch := fun branch =>
      { bytes := branch.program.nodes.size + branch.history.size,
        work := branch.program.nodes.size + branch.history.size } }

def extendedAdapterLimits : RuntimeProof.Limits :=
  { result := extendedResultLimits, proof := extendedProofLimits,
    tree := { maxNodes := 1, maxDepth := 0, maxBodyCells := 1, maxWork := 4 },
    maxTransitions := 1, maxEvents := 1, maxStructuralCells := 64 }

def extendedBundle? : Option (RuntimeProof.Bundle Hex.Interval
    (Rule.semantics extendedConfig) Rule.Runtime.Cause (List Nat)) :=
  match extendedRegistry?,
      State.Branch.startWithin extendedStateLimits extendedProgram extendedFacts with
  | some registry, .ok branch =>
      match Hex.Interval.Runtime.State.startWithin extendedRuntimeLimits
          registry.assembly branch,
        Search.Result.startWithin extendedResultLimits extendedMeasure { index := 0 } branch with
      | .ok runtime, .ok tree =>
          match runtime.stepWithin extendedRuntimeLimits opaqueAction with
          | .ok (transition, _) =>
              match Search.Result.advanceRuntimeWithin extendedResultLimits extendedMeasure
                  tree transition with
              | .ok tree =>
                  (RuntimeProof.quoteTreeWithin extendedAdapterLimits extendedMeasure
                    registry tree).toOption
              | .error _ => none
          | .error _ => none
      | _, _ => none
  | _, _ => none

#guard extendedBundle?.any fun bundle =>
  bundle.recipe.events[0]?.any fun events =>
    match events with
    | [.fact step] =>
        step.schema == opaqueSchema.key && step.body == [13] &&
          step.proposed == Hex.Interval.whole && step.installed == Hex.Interval.whole
    | _ => false

end Hex.IntervalMathlib.RuntimeRuleConformance
