/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.Propagator

/-!
Conformance canaries for the function-agnostic propagation experiment.

The registry interprets opaque rule keys over a tiny nested `Nat` fact domain.
No operation in the scheduler is named or implemented as arithmetic, and none
of these checks use `native_decide`.
-/

namespace Hex.Interval.PropagatorConformance

open Experiment.Propagator

abbrev Rank := Nat

/-- Larger ranks are strictly stronger synthetic facts. -/
def rankDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def real : DomainId := { index := 0 }

def sourceOp : OpKey := { name := "opaque.source" }
def unaryOp : OpKey := { name := "opaque.unary" }
def joinOp : OpKey := { name := "opaque.join3" }

def copyKey : RuleKey := { name := "opaque.copy" }
def joinKey : RuleKey := { name := "opaque.join" }
def forwardKey : RuleKey := { name := "opaque.forward" }
def backwardKey : RuleKey := { name := "opaque.backward" }

def node (index : Nat) : NodeId := { index }
def suggestion (index : Nat) : SuggestionId := { index }

def sourceNode : Node := { domain := real, op := { index := 0 }, args := [] }

def unaryNode (input : Nat) : Node :=
  { domain := real, op := { index := 1 }, args := [node input] }

def operations : Array Operation :=
  #[{ key := sourceOp, inputs := [], output := real },
    { key := unaryOp, inputs := [real], output := real }]

def generous : Limits :=
  { maxOperations := 16
    maxNodes := 64
    maxRules := 16
    maxArity := 8
    maxApplications := 128
    maxQueueEntries := 256
    maxActions := 128
    maxAcceptedFacts := 128
    maxRetainedSuggestions := 16
    maxEffort := 16
    maxObservationValue := 1024
    maxDiagnosticValue := 2048
    maxOutcomeCandidates := 8
    maxOutcomeSuggestions := 8
    maxProposalItems := 16
    maxInstances := 16
    maxGeneration := 4
    maxEqualities := 16
    splitEndpointLimit :=
      { maxEndpointHeight := 128, maxAlignmentShift := 64 } }

def copyRule : Registration :=
  { key := copyKey
    head := unaryOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def candidate (request : RuleRequest Rank) (rank : Rank) : Candidate Rank :=
  { node := request.action.node
    fact := rank
    payload := { index := request.action.serial } }

def oneInput? (request : RuleRequest Rank) : Option Rank :=
  match request.inputs with
  | [input] => some input.fact
  | _ => none

def copyInvoke (calls : List Nat) (request : RuleRequest Rank) :
    Outcome Rank × List Nat :=
  let calls := request.action.node.index :: calls
  match oneInput? request with
  | some rank => (.success [candidate request rank] [] {}, calls)
  | none => (.failed 1, calls)

def start? (program : Program) (rules : Array Registration) (facts : Array Rank)
    (limits : Limits := generous) : Option (Engine Rank) :=
  match Engine.start rankDomain program rules facts limits with
  | .ok state => some state
  | .error _ => none

/-! # Chain: arbitrary unary propagation -/

def chainProgram : Program :=
  { operations
    nodes := #[sourceNode, unaryNode 0, unaryNode 1, unaryNode 2, unaryNode 3] }

def chainResult? : Option (RunResult Rank (List Nat)) := do
  let state <- start? chainProgram #[copyRule] #[4, 0, 0, 0, 0]
  pure (drive copyInvoke 16 state [])

#guard chainProgram.check

-- A registration cannot begin above the engine's effort envelope.
#guard
  match Engine.start rankDomain chainProgram
      #[{ copyRule with initialEffort := generous.maxEffort + 1 }]
      #[4, 0, 0, 0, 0] generous with
  | .error (.resourceLimit .effort) => true
  | _ => false

#guard
  match chainResult? with
  | some result =>
      result.stop == .saturated && result.state.facts.toList == [4, 4, 4, 4, 4] &&
        result.state.metrics.requests == 4 && result.state.metrics.improvements == 4 &&
        result.state.metrics.queuePops == 4 &&
        result.state.metrics.suppressedInsertions == 3 &&
        result.state.history.all (fun event =>
          event.previous.node == event.node && event.previous.version + 1 == event.version) &&
        result.cache == [4, 3, 2, 1]
  | none => false

/-! # Fanout and opaque ternary join -/

def fanoutProgram : Program :=
  { operations := operations.push
      { key := joinOp, inputs := [real, real, real], output := real }
    nodes := #[sourceNode, unaryNode 0, unaryNode 0, unaryNode 0,
      { domain := real, op := { index := 2 }, args := [node 1, node 2, node 3] }] }

def joinRule : Registration :=
  { key := joinKey
    head := joinOp
    kind := .forward
    watches := [.argument 0, .argument 1, .argument 2]
    writes := [.result] }

def minimum? : List Nat -> Option Nat
  | [] => none
  | first :: rest => some (rest.foldl Nat.min first)

def fanoutInvoke (calls : List Nat) (request : RuleRequest Rank) :
    Outcome Rank × List Nat :=
  let calls := request.action.node.index :: calls
  if request.action.key == copyKey then
    match oneInput? request with
    | some rank => (.success [candidate request rank] [] {}, calls)
    | none => (.failed 2, calls)
  else if request.action.key == joinKey then
    match minimum? (request.inputs.map fun input => input.fact) with
    | some rank => (.success [candidate request rank] [] {}, calls)
    | none => (.failed 3, calls)
  else
    (.failed 4, calls)

def fanoutResult? : Option (RunResult Rank (List Nat)) := do
  let state <- start? fanoutProgram #[copyRule, joinRule] #[4, 0, 0, 0, 0]
  pure (drive fanoutInvoke 16 state [])

#guard fanoutProgram.check

-- Three changes all wake the join, but the coalescing queue retains one call.
#guard
  match fanoutResult? with
  | some result =>
      result.stop == .saturated && result.state.facts.toList == [4, 4, 4, 4, 4] &&
        result.state.metrics.requests == 4 && result.state.metrics.improvements == 4 &&
        result.state.metrics.queueInsertions == 4 &&
        result.state.metrics.suppressedInsertions == 3 &&
        result.cache == [4, 3, 2, 1]
  | none => false

/-! # Forward/backward propagation over an acyclic expression DAG -/

def forwardRule : Registration :=
  { key := forwardKey
    head := unaryOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def backwardRule : Registration :=
  { key := backwardKey
    head := unaryOp
    kind := .backward
    watches := [.result]
    writes := [.argument 0] }

def cycleInvoke (calls : List String) (request : RuleRequest Rank) :
    Outcome Rank × List String :=
  let calls := request.action.key.name :: calls
  match oneInput? request with
  | none => (.failed 5, calls)
  | some rank =>
      let rank := Nat.min 5 (rank + 1)
      match request.writes with
      | [target] =>
          (.success
            [{ node := target, fact := rank, payload := { index := request.action.serial } }]
            [] {}, calls)
      | _ => (.failed 10, calls)

def cycleResult? : Option (RunResult Rank (List String)) := do
  let state <- start? { operations, nodes := #[sourceNode, unaryNode 0] }
    #[forwardRule, backwardRule] #[0, 1]
  pure (drive cycleInvoke 16 state [])

#guard
  match cycleResult? with
  | some result =>
      result.stop == .saturated && result.state.facts.toList == [5, 5] &&
        result.state.metrics.requests == 7 && result.state.metrics.improvements == 5 &&
        result.state.metrics.suppressedInsertions == 0 &&
        result.cache.length == 7
  | none => false

/-! # Several independent methods for one opaque function -/

def methodRule (key : RuleKey) (kind : ActionKind := .forward) : Registration :=
  { key
    head := unaryOp
    kind
    watches := [.argument 0]
    writes := [.result] }

def coarseKey : RuleKey := { name := "method.coarse" }
def alternateKey : RuleKey := { name := "method.alternate" }
def improveKey : RuleKey := { name := "method.improve" }
def weakerKey : RuleKey := { name := "method.weaker" }
def emptyKey : RuleKey := { name := "method.no-change" }

def methodInvoke (calls : List String) (request : RuleRequest Rank) :
    Outcome Rank × List String :=
  let calls := request.action.key.name :: calls
  let produced rank := (.success [candidate request rank] [] {}, calls)
  if request.action.key == coarseKey then produced 1
  else if request.action.key == alternateKey then produced 2
  else if request.action.key == improveKey then produced 3
  else if request.action.key == weakerKey then produced 2
  else (.noChange {}, calls)

def methodResult? : Option (RunResult Rank (List String)) := do
  let rules := #[methodRule coarseKey, methodRule alternateKey,
    methodRule improveKey .improve, methodRule weakerKey .improve,
    methodRule emptyKey]
  let state <- start? { operations, nodes := #[sourceNode, unaryNode 0] }
    rules #[4, 0]
  pure (drive methodInvoke 16 state [])

#guard
  match methodResult? with
  | some result =>
      result.stop == .saturated && result.state.facts.toList == [4, 3] &&
        result.state.metrics.requests == 5 && result.state.metrics.candidates == 4 &&
        result.state.metrics.improvements == 3 && result.state.metrics.ruleNoChange == 1 &&
        result.state.history.size == 3
  | none => false

/-! # Structural requests are suggestions, not mutation authority -/

def instantiateKey : RuleKey := { name := "shape.add-expression" }

def instantiateRule : Registration :=
  { key := instantiateKey
    head := unaryOp
    kind := .instantiate
    watches := [.argument 0]
    writes := [.result] }

def proposedUnary (input : NodeId) : ProposedNode :=
  { domain := real
    op := { index := 1 }
    args := [.existing input] }

def instantiateInvoke (calls : Nat) (request : RuleRequest Rank) :
    Outcome Rank × Nat :=
  let proposal : InstantiationRequest :=
    { key := 7
      triggers := [request.action.node]
      claimedGeneration := 1
      nodes := [proposedUnary request.action.node]
      equalities := []
      payload := { index := 11 } }
  (.success [] [.instantiate proposal] {}, calls + 1)

def instantiationResult? : Option (RunResult Rank Nat) := do
  let state <- start? { operations, nodes := #[sourceNode, unaryNode 0] }
    #[instantiateRule] #[4, 0]
  pure (drive instantiateInvoke 4 state 0)

#guard
  match instantiationResult? with
  | some result =>
      result.stop == .saturated && result.cache == 1 &&
        result.state.program.nodes.size == 2 && result.state.suggestions.size == 1 &&
        result.state.history.isEmpty
  | none => false

/-! # Selecting a request atomically extends the network -/

def generatedOp : OpKey := { name := "opaque.generated" }
def generatedKey : RuleKey := { name := "opaque.generated.copy" }

def dynamicOperations : Array Operation :=
  operations.push { key := generatedOp, inputs := [real], output := real }

def generatedRule : Registration :=
  { key := generatedKey
    head := generatedOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def proposedGenerated (input : NodeId) : ProposedNode :=
  { domain := real
    op := { index := 2 }
    args := [.existing input] }

def dynamicProposal (request : RuleRequest Rank) (generation : Nat := 1) :
    InstantiationRequest :=
  { key := 19
    triggers := [request.action.node]
    claimedGeneration := generation
    nodes := [proposedGenerated request.action.node]
    equalities := []
    payload := { index := 23 } }

def dynamicInvoke (calls : List String) (request : RuleRequest Rank) :
    Outcome Rank × List String :=
  let calls := request.action.key.name :: calls
  if request.action.key == copyKey || request.action.key == generatedKey then
    match oneInput? request with
    | some rank => (.success [candidate request rank] [] {}, calls)
    | none => (.failed 6, calls)
  else if request.action.key == instantiateKey then
    (.success [] [.instantiate (dynamicProposal request)] {}, calls)
  else
    (.failed 7, calls)

def dynamicInitial? (limits : Limits := generous) :
    Option (RunResult Rank (List String)) := do
  let program : Program :=
    { operations := dynamicOperations, nodes := #[sourceNode, unaryNode 0] }
  let state <- start? program #[copyRule, instantiateRule, generatedRule] #[4, 0] limits
  pure (drive dynamicInvoke 8 state [])

def dynamicAdmitted? : Option (Engine Rank × List String × SuggestionId) := do
  let initial <- dynamicInitial?
  let selected := suggestion 0
  match initial.state.admitInstantiation selected with
  | .admitted [newNode] state =>
      if newNode == node 2 then some (state, initial.cache, selected) else none
  | _ => none

def dynamicFinal? : Option (RunResult Rank (List String) × SuggestionId) := do
  let (state, cache, selected) <- dynamicAdmitted?
  pure (drive dynamicInvoke 8 state cache, selected)

#guard
  match dynamicAdmitted? with
  | some (state, _, _) =>
      state.program.nodes.size == 3 && state.programVersion == 1 &&
        state.generations.toList == [0, 0, 1] && state.applications.size == 3 &&
        state.metrics.admittedInstances == 1 && state.metrics.generatedNodes == 1 &&
        match state.instanceHistory[0]? with
        | some event => event.substitution == [node 1, node 0]
        | none => false
  | none => false

#guard
  match dynamicFinal? with
  | some (result, _) =>
      result.stop == .saturated && result.state.facts.toList == [4, 4, 4] &&
        result.state.metrics.requests == 3 && result.state.metrics.improvements == 2 &&
        result.state.history.size == 2
  | none => false

-- Selecting the same structural extension twice allocates nothing.
#guard
  match dynamicFinal? with
  | some (result, selected) =>
      match result.state.admitInstantiation selected with
      | .duplicate state =>
          state.program.nodes.size == 3 && state.instances.length == 1 &&
            state.metrics.duplicateInstances == 1
      | _ => false
  | none => false

-- A one-step-short node budget leaves the original two-node program intact.
#guard
  match dynamicInitial? { generous with maxNodes := 2 } with
  | some initial =>
      match initial.state.admitInstantiation (suggestion 0) with
      | .resourceLimit .nodes state =>
          state.program.nodes.size == 2 && state.instances.isEmpty &&
            state.metrics.generatedNodes == 0
      | _ => false
  | none => false

/-! ## CSE does not create a proof dependency -/

def cseAnchorKey : RuleKey := { name := "shape.cse-anchor" }
def cseSourceKey : RuleKey := { name := "shape.cse-source" }

def cseRule (key : RuleKey) : Registration :=
  { key
    head := unaryOp
    kind := .instantiate
    watches := [.argument 0]
    writes := [] }

def cseProposal (request : RuleRequest Rank) (left : NodeId) :
    InstantiationRequest :=
  { key := left.index
    triggers := [request.action.node, left]
    /- Deliberately wrong: this package hint is not admission authority. -/
    claimedGeneration := 0
    nodes := [proposedGenerated request.action.node]
    equalities :=
      [{ left := .existing left
         right := .proposed 0
         payload := { index := left.index } }]
    payload := { index := left.index } }

def cseInvoke (calls : Nat) (request : RuleRequest Rank) :
    Outcome Rank × Nat :=
  if request.action.key == cseAnchorKey then
    (.success [] [.instantiate (cseProposal request request.action.node)] {}, calls + 1)
  else if request.action.key == cseSourceKey then
    (.success [] [.instantiate (cseProposal request (node 0))] {}, calls + 1)
  else
    (.failed 10, calls + 1)

def cseInitial? : Option (RunResult Rank Nat) := do
  let program : Program :=
    { operations := dynamicOperations, nodes := #[sourceNode, unaryNode 0] }
  let state <- start? program #[cseRule cseAnchorKey, cseRule cseSourceKey]
    #[4, 0] { generous with maxGeneration := 1 }
  pure (drive cseInvoke 8 state 0)

def cseOrder? (first second : SuggestionId) : Option (Engine Rank) := do
  let initial <- cseInitial?
  let firstRetained <- initial.state.suggestions[first.index]?
  let secondRetained <- initial.state.suggestions[second.index]?
  if initial.state.instantiationGeneration? firstRetained != some 1 ||
      initial.state.instantiationGeneration? secondRetained != some 1 then
    none
  else
    match initial.state.admitInstantiation first with
    | .admitted [fresh] state =>
        if fresh != node 2 then none else
        let retained := state.suggestions[second.index]?
        match retained with
        | none => none
        | some retained =>
            if !state.actionFresh retained.action ||
                state.instantiationGeneration? retained != some 1 then
              none
            else
              match state.admitInstantiation second with
              | .admitted [] final => some final
              | _ => none
    | _ => none

def exactCseState (state : Engine Rank) : Bool :=
  state.programVersion == 2 && state.program.nodes.size == 3 &&
    state.generations.toList == [0, 0, 1] &&
    state.equalities.size == 2 && state.instances.length == 2 &&
    state.instanceHistory.size == 2 &&
    state.instanceHistory.toList.all (fun event => event.generation == 1) &&
    state.equalities.toList.all (fun edge => edge.generation == 1) &&
    state.equalities.toList.any (fun edge => edge.sameEndpoints (node 0) (node 2)) &&
    state.equalities.toList.any (fun edge => edge.sameEndpoints (node 1) (node 2))

-- Either proposal may materialize `generated(anchor)` first.  The second
-- append-stable proposal then CSE-hits that output but remains generation one,
-- so both equalities are admitted under the exact generation-one cap.
#guard
  match cseOrder? (suggestion 0) (suggestion 1),
      cseOrder? (suggestion 1) (suggestion 0) with
  | some anchorFirst, some sourceFirst =>
      exactCseState anchorFirst && exactCseState sourceFirst
  | _, _ => false

/-! ## Two successive shape triggers exercise general generation recurrence -/

def nextOp : OpKey := { name := "opaque.next-generation" }
def nextCopyKey : RuleKey := { name := "opaque.next.copy" }
def nextInstantiateKey : RuleKey := { name := "shape.add-next-generation" }

def ladderOperations : Array Operation :=
  dynamicOperations.push { key := nextOp, inputs := [real], output := real }

def nextCopyRule : Registration :=
  { key := nextCopyKey
    head := nextOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def nextInstantiateRule : Registration :=
  { key := nextInstantiateKey
    head := generatedOp
    kind := .instantiate
    watches := [.argument 0]
    writes := [.result] }

def proposedNext (input : NodeId) : ProposedNode :=
  { domain := real
    op := { index := 3 }
    args := [.existing input] }

def ladderProposal (request : RuleRequest Rank) : InstantiationRequest :=
  if request.action.key == instantiateKey then
    dynamicProposal request 1
  else
    { key := 29
      triggers := [request.action.node]
      claimedGeneration := 2
      nodes := [proposedNext request.action.node]
      equalities := []
      payload := { index := 31 } }

def ladderInvoke (calls : List String) (request : RuleRequest Rank) :
    Outcome Rank × List String :=
  let calls := request.action.key.name :: calls
  if request.action.key == copyKey || request.action.key == generatedKey ||
      request.action.key == nextCopyKey then
    match oneInput? request with
    | some rank => (.success [candidate request rank] [] {}, calls)
    | none => (.failed 8, calls)
  else if request.action.key == instantiateKey ||
      request.action.key == nextInstantiateKey then
    (.success [] [.instantiate (ladderProposal request)] {}, calls)
  else
    (.failed 9, calls)

def ladderInitial? (limits : Limits := generous) :
    Option (RunResult Rank (List String)) := do
  let program : Program :=
    { operations := ladderOperations, nodes := #[sourceNode, unaryNode 0] }
  let rules := #[copyRule, instantiateRule, generatedRule,
    nextInstantiateRule, nextCopyRule]
  let state <- start? program rules #[4, 0] limits
  pure (drive ladderInvoke 8 state [])

def ladderAfterFirst? (limits : Limits := generous) :
    Option (RunResult Rank (List String)) := do
  let initial <- ladderInitial? limits
  match initial.state.admitInstantiation (suggestion 0) with
  | .admitted [newNode] state =>
      if newNode == node 2 then some (drive ladderInvoke 8 state initial.cache)
      else none
  | _ => none

def ladderFinal? : Option (RunResult Rank (List String)) := do
  let first <- ladderAfterFirst?
  match first.state.admitInstantiation (suggestion 1) with
  | .admitted [newNode] state =>
      if newNode == node 3 then some (drive ladderInvoke 8 state first.cache)
      else none
  | _ => none

#guard
  match ladderFinal? with
  | some result =>
      result.stop == .saturated && result.state.facts.toList == [4, 4, 4, 4] &&
        result.state.generations.toList == [0, 0, 1, 2] &&
        result.state.programVersion == 2 && result.state.instances.length == 2 &&
        result.state.metrics.admittedInstances == 2 &&
        result.state.metrics.generatedNodes == 2 &&
        result.state.metrics.requests == 5 && result.state.metrics.improvements == 3
  | none => false

-- The second instance is correctly blocked by a generation-one cap.
#guard
  match ladderAfterFirst? { generous with maxGeneration := 1 } with
  | some first =>
      match first.state.admitInstantiation (suggestion 1) with
      | .resourceLimit .generation state =>
          state.program.nodes.size == 3 && state.instances.length == 1 &&
            state.generations.toList == [0, 0, 1]
      | _ => false
  | none => false

-- A registry claim cannot launder a generation-one invocation back to
-- generation one.  The engine ignores the claim and derives generation two
-- from the action anchor even when the trigger list and draft mention only a
-- shallow node.
#guard
  match ladderAfterFirst? with
  | some first =>
      match first.state.suggestions[1]? with
      | some retained =>
          let proposal : InstantiationRequest :=
            { key := 97
              triggers := []
              claimedGeneration := 1
              nodes := [proposedNext (node 0)]
              equalities := []
              payload := { index := 101 } }
          match first.state.admitRetained
              { action := retained.action
                suggestion := .instantiate proposal
                splitVersion := none } with
          | .admitted [fresh] state =>
              fresh == node 3 && state.programVersion == 2 &&
                state.generations.toList == [0, 0, 1, 2] &&
                match state.instanceHistory[1]? with
                | some event => event.generation == 2
                | none => false
          | _ => false
      | none => false
  | none => false

/-! # One atomic batch: CSE, several products, and an equality draft -/

def batchKey : RuleKey := { name := "shape.batch" }

def batchRule : Registration :=
  { key := batchKey
    head := unaryOp
    kind := .instantiate
    watches := [.argument 0]
    writes := [] }

def proposedGeneratedRef (input : NodeRef) : ProposedNode :=
  { domain := real
    op := { index := 2 }
    args := [input] }

def proposedNextRef (input : NodeRef) : ProposedNode :=
  { domain := real
    op := { index := 3 }
    args := [input] }

def batchEquality (anchor : NodeId) : ProposedEquality :=
  { left := .existing anchor
    right := .proposed 2
    payload := { index := 41 } }

def batchInvoke (calls : Nat) (request : RuleRequest Rank) : Outcome Rank × Nat :=
  let proposal : InstantiationRequest :=
    { key := 37
      triggers := [request.action.node]
      claimedGeneration := 1
      nodes :=
        [proposedGeneratedRef (.existing request.action.node),
          proposedGeneratedRef (.existing request.action.node),
          proposedNextRef (.proposed 0)]
      equalities := [batchEquality request.action.node]
      payload := { index := 43 } }
  (.success [] [.instantiate proposal] {}, calls + 1)

def batchAdmitted? : Option (Engine Rank) := do
  let program : Program :=
    { operations := ladderOperations, nodes := #[sourceNode, unaryNode 0] }
  let state <- start? program #[batchRule] #[4, 0]
  let initial := drive batchInvoke 4 state 0
  match initial.state.admitInstantiation (suggestion 0) with
  | .admitted [first, second] state =>
      if first == node 2 && second == node 3 then some state else none
  | _ => none

#guard
  match batchAdmitted? with
  | some state =>
      state.program.nodes.size == 4 && state.generations.toList == [0, 0, 1, 1] &&
        state.equalities.size == 1 && state.instances.length == 1 &&
        state.instanceHistory.size == 1 &&
        match state.instanceHistory[0]? with
        | some event =>
            event.programVersion == 1 && event.origin.programVersion == 0 &&
              event.origin.key == batchKey && event.origin.node == node 1 &&
              event.origin.kind == .instantiate &&
              event.origin.inputs == [{ node := node 0, version := 0 }] &&
              event.products == [node 2, node 2, node 3] &&
              event.newNodes == [node 2, node 3] && event.generation == 1 &&
              event.equalities.length == 1 && event.payload == { index := 43 }
        | none => false
  | none => false

/-! # Equality is one atomic, undirected contractor -/

structure PairRank where
  first : Nat
  second : Nat
  deriving DecidableEq, Repr

def pair (first second : Nat) : PairRank := { first, second }

def pairDomain : FactDomain PairRank where
  top _ := pair 0 0
  narrow _ current candidate :=
    let merged := pair (Nat.max current.first candidate.first)
      (Nat.max current.second candidate.second)
    if merged == current then .noChange else .improved merged

def pairEqualityKey : RuleKey := { name := "shape.pair-equality" }

def pairEqualityRule : Registration :=
  { key := pairEqualityKey
    head := unaryOp
    kind := .instantiate
    watches := [.result]
    writes := [] }

def pairEqualityInvoke (calls : Nat) (request : RuleRequest PairRank) :
    Outcome PairRank × Nat :=
  let proposal : InstantiationRequest :=
    { key := 47
      triggers := [request.action.node]
      claimedGeneration := 1
      nodes := []
      equalities :=
        [{ left := .existing (node 0)
           right := .existing (node 1)
           payload := { index := 53 } }]
      payload := { index := 59 } }
  (.success [] [.instantiate proposal] {}, calls + 1)

def pairProgram : Program :=
  { operations, nodes := #[sourceNode, sourceNode, unaryNode 0] }

def pairInitial? (limits : Limits := generous) : Option (RunResult PairRank Nat) := do
  let state <- match Engine.start pairDomain pairProgram #[pairEqualityRule]
      #[pair 4 0, pair 0 5, pair 0 0] limits with
    | .ok state => some state
    | .error _ => none
  pure (drive pairEqualityInvoke 8 state 0)

def pairAdmitted? (limits : Limits := generous) : Option (Engine PairRank) := do
  let initial <- pairInitial? limits
  match initial.state.admitInstantiation (suggestion 0) with
  | .admitted [] state => some state
  | _ => none

def pairFinal? (limits : Limits := generous) : Option (RunResult PairRank Nat) := do
  let state <- pairAdmitted? limits
  pure (drive pairEqualityInvoke 8 state 1)

/-- A second instance adds one node while explicitly reusing the equality
created by the first instance. -/
def pairReuseAdmitted? : Option (Engine PairRank) := do
  let state <- pairAdmitted?
  let retained <- state.suggestions[0]?
  let proposal : InstantiationRequest :=
    { key := 103
      triggers := []
      claimedGeneration := 1
      nodes := [proposedUnary (node 1)]
      equalities :=
        [{ left := .existing (node 1)
           right := .existing (node 0)
           payload := { index := 107 } }]
      payload := { index := 109 } }
  let action := { retained.action with programVersion := state.programVersion }
  match state.admitRetained
      { action, suggestion := .instantiate proposal, splitVersion := none } with
  | .admitted [newNode] next => if newNode == node 3 then some next else none
  | _ => none

-- Equality endpoints are unordered, the pair set is sorted, and reversed
-- repetitions do not create a distinct instance identity.
#guard
  resolveRequestedPairs 3 [] pairProgram
      [{ left := .existing (node 1), right := .existing (node 2), payload := { index := 0 } },
       { left := .existing (node 1), right := .existing (node 0), payload := { index := 1 } },
       { left := .existing (node 2), right := .existing (node 1), payload := { index := 2 } }] ==
    some
      [{ first := node 0, second := node 1 },
       { first := node 1, second := node 2 }]

-- A repeated pure-equality selection is a duplicate rather than an empty new
-- instance after the edge has entered the live equality table.
#guard
  match pairAdmitted? with
  | some state =>
      match state.admitInstantiation (suggestion 0) with
      | .duplicate next =>
          next.equalities.size == 1 && next.instances.length == 1 &&
            next.metrics.duplicateInstances == 1
      | _ => false
  | none => false

-- Replay provenance names a reused link just as precisely as a fresh link.
#guard
  match pairReuseAdmitted? with
  | some state =>
      state.equalities.size == 1 && state.program.nodes.size == 4 &&
        state.programVersion == 2 && state.instanceHistory.size == 2 &&
        match state.instanceHistory[0]?, state.instanceHistory[1]? with
        | some first, some second =>
            first.equalities == [{ index := 0 }] &&
              second.equalities == [{ index := 0 }] && second.newNodes == [node 3]
        | _, _ => false
  | none => false

-- A differently labelled request from the same engine-owned invocation whose
-- complete structural effect already exists is a no-op: an untrusted request
-- label cannot manufacture a new family, snapshot, or instance slot.
#guard
  match pairAdmitted? with
  | some state =>
      match state.suggestions[0]? with
      | some retained =>
          let proposal : InstantiationRequest :=
            { key := 113
              triggers := []
              claimedGeneration := 1
              nodes := []
              equalities :=
                [{ left := .existing (node 0)
                   right := .existing (node 1)
                   payload := { index := 127 } }]
              payload := { index := 131 } }
          let currentAction :=
            { retained.action with programVersion := state.programVersion }
          match state.admitRetained
              { action := currentAction
                suggestion := .instantiate proposal
                splitVersion := none } with
          | .duplicate next =>
              next.programVersion == 1 && next.instances.length == 1 &&
                next.instanceHistory.size == 1 && next.equalities.size == 1
          | _ => false
      | none => false
  | none => false

-- Direct equality contraction cannot interleave with an outstanding external
-- rule request.
#guard
  match pairAdmitted? with
  | some state =>
      match state.equalities[0]? with
      | some edge =>
          let pending := { state with pending := some edge.origin }
          match pending.contractEquality { index := 0 } with
          | .invalid .pendingReply 0 next =>
              next.pending.isSome && next.facts == pending.facts &&
                next.versions == pending.versions && next.history.isEmpty
          | _ => false
      | none => false
  | none => false

#guard
  match pairFinal? with
  | some result =>
      result.stop == .saturated &&
        result.state.facts.toList == [pair 4 5, pair 4 5, pair 0 0] &&
        result.state.metrics.requests == 1 && result.state.metrics.equalityRuns == 2 &&
        result.state.metrics.equalityImprovements == 2 &&
        result.state.metrics.queuePops == 3 && result.state.history.size == 2 &&
        match result.state.equalities[0]?, result.state.history[0]?,
            result.state.history[1]? with
        | some edge, some left, some right =>
            edge.origin.key == pairEqualityKey && edge.origin.node == node 2 &&
              left.node == node 0 && left.previous == { node := node 0, version := 0 } &&
              right.node == node 1 && right.previous == { node := node 1, version := 0 } &&
              match left.cause, right.cause with
              | .transport leftEquality leftSource, .transport rightEquality rightSource =>
                  leftEquality == { index := 0 } && rightEquality == { index := 0 } &&
                    leftSource == { node := node 1, version := 0 } &&
                    rightSource == { node := node 0, version := 0 }
              | _, _ => false
        | _, _, _ => false
  | none => false

-- Both endpoint updates roll back when their combined history budget is short.
#guard
  match pairFinal? { generous with maxAcceptedFacts := 1 } with
  | some result =>
      result.stop == .engineResource .acceptedFacts &&
        result.state.facts.toList == [pair 4 0, pair 0 5, pair 0 0] &&
        result.state.history.isEmpty && result.state.equalities.size == 1
  | none => false

-- A failed wakeup also rolls back both transported facts and their history.
#guard
  match pairFinal? { generous with maxQueueEntries := 2 } with
  | some result =>
      result.stop == .engineResource .queueEntries &&
        result.state.facts.toList == [pair 4 0, pair 0 5, pair 0 0] &&
        result.state.history.isEmpty && result.state.metrics.equalityImprovements == 0
  | none => false

-- The equality and its queue entry are part of the atomic admission commit.
#guard
  match pairInitial? { generous with maxQueueEntries := 1 } with
  | some initial =>
      match initial.state.admitInstantiation (suggestion 0) with
      | .resourceLimit .queueEntries state =>
          state.equalities.isEmpty && state.instances.isEmpty &&
            state.programVersion == 0 && state.queue.size == 1
      | _ => false
  | none => false

-- Equality work consumes the same deterministic action budget as rule work.
#guard
  match pairFinal? { generous with maxActions := 2 } with
  | some result =>
      result.stop == .engineResource .actions && result.state.metrics.requests == 1 &&
        result.state.metrics.equalityRuns == 1 && result.state.metrics.queuePops == 2 &&
        result.state.facts.toList == [pair 4 5, pair 4 5, pair 0 0]
  | none => false

/-! # An equal alternate joins the ordinary propagator network -/

def alternateEqualityKey : RuleKey := { name := "shape.equal-alternate" }

def alternateEqualityRule : Registration :=
  { key := alternateEqualityKey
    head := unaryOp
    kind := .instantiate
    watches := [.argument 0]
    writes := [] }

def alternateEqualityProposal (request : RuleRequest Rank) : InstantiationRequest :=
  { key := 61
    triggers := [request.action.node]
    claimedGeneration := 1
    nodes :=
      [proposedGeneratedRef (.existing request.action.node),
        proposedNextRef (.proposed 0)]
    equalities :=
      [{ left := .existing request.action.node
         right := .proposed 0
         payload := { index := 67 } }]
    payload := { index := 71 } }

def alternateEqualityInvoke (calls : List String) (request : RuleRequest Rank) :
    Outcome Rank × List String :=
  let calls := request.action.key.name :: calls
  if request.action.key == alternateEqualityKey then
    (.success [] [.instantiate (alternateEqualityProposal request)] {}, calls)
  else if request.action.key == nextCopyKey then
    match oneInput? request with
    | some rank => (.success [candidate request rank] [] {}, calls)
    | none => (.failed 11, calls)
  else
    (.failed 12, calls)

def alternateEqualityInitial? (limits : Limits := generous) :
    Option (RunResult Rank (List String)) := do
  let program : Program :=
    { operations := ladderOperations, nodes := #[sourceNode, unaryNode 0] }
  let state <- start? program #[alternateEqualityRule, nextCopyRule] #[4, 4] limits
  pure (drive alternateEqualityInvoke 8 state [])

def alternateEqualityAdmitted? (limits : Limits := generous) :
    Option (Engine Rank × List String) := do
  let initial <- alternateEqualityInitial? limits
  match initial.state.admitInstantiation (suggestion 0) with
  | .admitted [alternate, consumer] state =>
      if alternate == node 2 && consumer == node 3 then some (state, initial.cache) else none
  | _ => none

def alternateEqualityFinal? : Option (RunResult Rank (List String)) := do
  let (state, cache) <- alternateEqualityAdmitted?
  pure (drive alternateEqualityInvoke 8 state cache)

#guard
  match alternateEqualityFinal? with
  | some result =>
      result.stop == .saturated && result.state.facts.toList == [4, 4, 4, 4] &&
        result.state.metrics.requests == 2 && result.state.metrics.equalityRuns == 2 &&
        result.state.metrics.equalityImprovements == 1 &&
        result.state.metrics.improvements == 2 && result.state.history.size == 2 &&
        result.cache == [nextCopyKey.name, alternateEqualityKey.name] &&
        match result.state.history[0]?, result.state.history[1]? with
        | some transported, some propagated =>
            transported.node == node 2 && propagated.node == node 3 &&
              match transported.cause, propagated.cause with
              | .transport equality source, .rule action _ =>
                  equality == { index := 0 } && source == { node := node 1, version := 0 } &&
                    action.key == nextCopyKey &&
                      action.inputs == [{ node := node 2, version := 1 }]
              | _, _ => false
        | _, _ => false
  | none => false

-- The new nodes, equality watcher, and arbitrary application commit together.
#guard
  match alternateEqualityInitial? { generous with maxQueueEntries := 2 } with
  | some initial =>
      match initial.state.admitInstantiation (suggestion 0) with
      | .resourceLimit .queueEntries state =>
          state.program.nodes.size == 2 && state.applications.size == 1 &&
            state.equalities.isEmpty && state.instances.isEmpty && state.programVersion == 0
      | _ => false
  | none => false

/-! # Bounded observations, effort, and structural requests -/

def firstChainRequest? : Option (RuleRequest Rank × Engine Rank) := do
  let initial <- start? chainProgram #[copyRule] #[4, 0, 0, 0, 0]
  match initial.poll with
  | .request request awaiting => some (request, awaiting)
  | _ => none

def oversizedMalformedDomain : FactDomain Rank where
  top _ := 0
  narrow _ _ _ := .malformed (generous.maxDiagnosticValue + 1)

def oversizedResourceDomain : FactDomain Rank where
  top _ := 0
  narrow _ _ _ := .resourceLimit (generous.maxDiagnosticValue + 1)

def firstRequestWith? (domain : FactDomain Rank) :
    Option (RuleRequest Rank × Engine Rank) := do
  let initial <-
    match Engine.start domain chainProgram #[copyRule] #[4, 0, 0, 0, 0] generous with
    | .ok state => some state
    | .error _ => none
  match initial.poll with
  | .request request awaiting => some (request, awaiting)
  | _ => none

-- Append-only recompilation must preserve every existing concrete
-- application exactly, not merely preserve the old array length.
#guard
  match firstChainRequest? with
  | some (_, state) =>
      match state.applications[0]? with
      | some first =>
          applicationsPrefix state.applications (state.applications.push first) &&
            !applicationsPrefix state.applications
              (state.applications.set! 0 { first with effort := first.effort + 1 })
      | none => false
  | none => false

-- Fact-domain diagnostics cross the same independent representation cap as
-- callback diagnostics before they can enter driver or policy events.
#guard
  match firstRequestWith? oversizedMalformedDomain with
  | some (request, awaiting) =>
      match awaiting.submit (request.action.reply
          (.success [candidate request 4] [] {})) with
      | .invalid .oversizedObservation state =>
          state.pending.isNone && state.history.isEmpty
      | _ => false
  | none => false

#guard
  match firstRequestWith? oversizedResourceDomain with
  | some (request, awaiting) =>
      match awaiting.submit (request.action.reply
          (.success [candidate request 4] [] {})) with
      | .invalid .oversizedObservation state =>
          state.pending.isNone && state.history.isEmpty
      | _ => false
  | none => false

-- Reply-provided policy telemetry is checked before it can enter retained
-- observations or affect any fact.
#guard
  match firstChainRequest? with
  | some (request, awaiting) =>
      match awaiting.submit (request.action.reply
          (.noChange { arithmeticWork := generous.maxObservationValue + 1 })) with
      | .invalid .oversizedObservation state =>
          state.pending.isNone && state.history.isEmpty && state.suggestions.isEmpty
      | _ => false
  | none => false

-- Advisory-suggestion capacity cannot discard a valid fact improvement.  The
-- bounded prefix is retained and overflow is an observation, not a failed
-- reply transaction.
#guard
  match start? chainProgram #[copyRule] #[4, 0, 0, 0, 0]
      { generous with maxRetainedSuggestions := 0 } with
  | some initial =>
      match initial.poll with
      | .request request awaiting =>
          match awaiting.submit (request.action.reply
              (.success [candidate request 4] [.retry 1] {})) with
          | .accepted state =>
              state.facts.toList == [4, 4, 0, 0, 0] && state.history.size == 1 &&
                state.suggestions.isEmpty && state.metrics.droppedSuggestions == 1 &&
                state.metrics.candidates == 1
          | _ => false
      | _ => false
  | none => false

-- A failure code is an opaque diagnostic identifier, not a logical cost
-- magnitude governed by the performed-work budget.  It has its own cap.
#guard
  match firstChainRequest? with
  | some (request, awaiting) =>
      match awaiting.submit (request.action.reply
          (.failed (generous.maxObservationValue + 1))) with
      | .accepted state =>
          state.pending.isNone && state.metrics.ruleFailures == 1 && state.history.isEmpty
      | _ => false
  | none => false

#guard
  match firstChainRequest? with
  | some (request, awaiting) =>
      match awaiting.submit (request.action.reply
          (.failed (generous.maxDiagnosticValue + 1))) with
      | .invalid .oversizedObservation state =>
          state.pending.isNone && state.metrics.ruleFailures == 0 && state.history.isEmpty
      | _ => false
  | none => false

-- The direct submit API rejects a delayed/transplanted serial without
-- clearing the current request latch.
#guard
  match firstChainRequest? with
  | some (request, awaiting) =>
      let reply : Reply Rank :=
        { serial := request.action.serial + 1
          programVersion := request.action.programVersion
          application := request.action.application
          outcome := .inapplicable }
      match awaiting.submit reply with
      | .invalid .mismatchedAction state =>
          state.pending.isSome && state.metrics.replies == 0 && state.history.isEmpty
      | _ => false
  | none => false

-- Effort is rule-specific, but its representation is still engine-bounded.
#guard
  match firstChainRequest? with
  | some (request, awaiting) =>
      match awaiting.submit (request.action.reply
          (.success [] [.retry (generous.maxEffort + 1)] {})) with
      | .invalid .oversizedEffort state =>
          state.pending.isNone && state.history.isEmpty && state.suggestions.isEmpty
      | _ => false
  | none => false

-- Trigger cardinality and every trigger reference are part of the proposal's
-- own boundedness predicate, including callers which invoke it directly.
#guard
  match firstChainRequest? with
  | some (request, awaiting) =>
      let proposal : InstantiationRequest :=
        { key := 73
          triggers := List.replicate (generous.maxProposalItems + 1) (node 0)
          claimedGeneration := 1
          nodes := []
          equalities := []
          payload := { index := 79 } }
      match awaiting.submit (request.action.reply
          (.success [] [.instantiate proposal] {})) with
      | .invalid .oversizedProposal state =>
          state.pending.isNone && state.history.isEmpty && state.suggestions.isEmpty
      | _ => false
  | none => false

end Hex.Interval.PropagatorConformance
