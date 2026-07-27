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

/-! ## Chain: arbitrary unary propagation -/

def chainProgram : Program :=
  { operations
    nodes := #[sourceNode, unaryNode 0, unaryNode 1, unaryNode 2, unaryNode 3] }

def chainResult? : Option (RunResult Rank (List Nat)) := do
  let state <- start? chainProgram #[copyRule] #[4, 0, 0, 0, 0]
  pure (drive copyInvoke 16 state [])

#guard chainProgram.check

#guard
  match chainResult? with
  | some result =>
      result.stop == .saturated && result.state.facts.toList == [4, 4, 4, 4, 4] &&
        result.state.metrics.requests == 4 && result.state.metrics.improvements == 4 &&
        result.state.metrics.queuePops == 4 &&
        result.state.metrics.suppressedInsertions == 3 &&
        result.cache == [4, 3, 2, 1]
  | none => false

/-! ## Fanout and opaque ternary join -/

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

/-! ## Forward/backward propagation over an acyclic expression DAG -/

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

/-! ## Several independent methods for one opaque function -/

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

/-! ## Structural requests are suggestions, not mutation authority -/

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

/-! ## Selecting a request atomically extends the network -/

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
        state.metrics.admittedInstances == 1 && state.metrics.generatedNodes == 1
  | none => false

#guard
  match dynamicFinal? with
  | some (result, _) =>
      result.stop == .saturated && result.state.facts.toList == [4, 4, 4] &&
        result.state.metrics.requests == 3 && result.state.metrics.improvements == 2 &&
        result.state.history.size == 2
  | none => false

-- Selecting the same family/substitution twice allocates nothing.
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

/-! ## One atomic batch: CSE, several products, and an equality draft -/

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
            event.products == [node 2, node 2, node 3] &&
              event.newNodes == [node 2, node 3] && event.generation == 1 &&
              event.equalities.length == 1 && event.payload == { index := 43 }
        | none => false
  | none => false

end Hex.Interval.PropagatorConformance
