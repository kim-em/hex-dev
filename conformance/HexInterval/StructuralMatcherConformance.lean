/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.StructuralMatcher

/-!
# Structural matcher cursor conformance

These checks use only stable structural identifiers.  The final canary
recognizes `sin (-x)` and constructs the expressions, equality, and arbitrary
propagator scope needed to use oddness.  No endpoint representation or
rational arithmetic participates.
-/

namespace Hex.Interval.StructuralMatcherConformance

open Experiment.Propagator
open Experiment.Propagator.StructuralMatcher

def generations (nodes equalities applications : Array Nat) : Key -> Option Nat
  | .node node => nodes[node.index]?
  | .equality equality => equalities[equality.index]?
  | .application application => applications[application.index]?

def view0 : View :=
  { programVersion := 0
    size := { nodes := 3, equalities := 2, applications := 2 } }

def generation0 : Key -> Option Nat :=
  generations #[0, 1, 1] #[2, 3] #[0, 4]

def cursor0 : Cursor :=
  Cursor.start view0

def limits (visits batch : Nat) : StructuralMatcher.Limits :=
  { maxVisits := visits, batchSize := batch }

def exactInputs : Array Input :=
  #[{ key := .node { index := 0 }, generation := 0 },
    { key := .node { index := 1 }, generation := 1 },
    { key := .node { index := 2 }, generation := 1 },
    { key := .equality { index := 0 }, generation := 2 },
    { key := .equality { index := 1 }, generation := 3 },
    { key := .application { index := 0 }, generation := 0 },
    { key := .application { index := 1 }, generation := 4 }]

#guard cursor0.base == {} && cursor0.limit == { nodes := 3, equalities := 2, applications := 2 }

#guard
  match take generation0 (limits 7 2) view0 cursor0 with
  | .yielded inputs cursor =>
      inputs == exactInputs.extract 0 2 && cursor.offset == 2 &&
        cursor.visits == 2 && !cursor.exhausted
  | _ => false

def runAll : Option (Array Input × Cursor) := do
  let .yielded first cursor := take generation0 (limits 7 2) view0 cursor0 | none
  let .yielded second cursor := take generation0 (limits 7 2) view0 cursor | none
  let .yielded third cursor := take generation0 (limits 7 2) view0 cursor | none
  let .yielded fourth cursor := take generation0 (limits 7 2) view0 cursor | none
  let .exhausted cursor := take generation0 (limits 7 2) view0 cursor | none
  pure (first ++ second ++ third ++ fourth, cursor)

-- Multi-batch concatenation is the exact canonical stream, and only the
-- engine-produced terminal step reports exhaustion.
#guard
  match runAll with
  | some (inputs, cursor) =>
      inputs == exactInputs && cursor.offset == 7 &&
        cursor.visits == 7 && cursor.exhausted
  | none => false

-- A one-short cumulative visit limit leaves the cursor unchanged and cannot
-- report exhaustion.
#guard
  match take generation0 (limits 6 7) view0 cursor0 with
  | .resourceLimit cursor => cursor == cursor0
  | _ => false

#guard
  match take generation0 (limits 7 0) view0 cursor0 with
  | .invalidCursor => true
  | _ => false

def cursorAfterOne : Option Cursor := do
  let .yielded _ cursor := take generation0 (limits 7 2) view0 cursor0 | none
  pure cursor

-- Renewal is legal only after the frozen epoch is exhausted.
#guard
  match cursorAfterOne with
  | some cursor =>
      match renew view0 cursor with
      | .error .cursorNotExhausted => true
      | _ => false
  | none => false

def exhausted0 : Cursor :=
  { cursor0 with offset := 7, visits := 7 }

-- Renewal without a structural delta preserves the exhausted cursor and
-- cannot manufacture an endless stream of empty epochs.
#guard
  match renew { view0 with programVersion := 1 } exhausted0 with
  | .ok cursor => cursor == exhausted0
  | .error _ => false

def grownView : View :=
  { programVersion := 1
    size := { nodes := 4, equalities := 3, applications := 4 } }

def grownGeneration : Key -> Option Nat :=
  generations #[0, 1, 1, 2] #[2, 3, 5] #[0, 4, 5, 6]

def deltaInputs : Array Input :=
  #[{ key := .node { index := 3 }, generation := 2 },
    { key := .equality { index := 2 }, generation := 5 },
    { key := .application { index := 2 }, generation := 5 },
    { key := .application { index := 3 }, generation := 6 }]

-- Network growth during an epoch cannot alter its frozen stream.
#guard
  match cursorAfterOne with
  | some cursor =>
      match take grownGeneration (limits 7 5) grownView cursor with
      | .yielded inputs next =>
          inputs == exactInputs.extract 2 7 && next.offset == 7 &&
            next.limit == cursor.limit
      | _ => false
  | none => false

def renewed? : Except Error Cursor :=
  renew grownView exhausted0

-- Renewal exposes exactly the append delta in stable identifier order.
#guard
  match renewed? with
  | .ok cursor =>
      cursor.epoch == 1 && cursor.visits == 7 && cursor.offset == 0 &&
        cursor.base == exhausted0.limit && cursor.limit == grownView.size &&
        match take grownGeneration (limits 11 4) grownView cursor with
        | .yielded inputs next =>
            inputs == deltaInputs && next.exhausted && next.visits == 11
        | _ => false
  | .error _ => false

-- Arena shrink and snapshot rollback are rejected without traversal.
#guard
  match renew
      { view0 with
        programVersion := 1
        size := { nodes := 2, equalities := 2, applications := 2 } }
      exhausted0 with
  | .error .invalidCursor => true
  | _ => false

#guard
  match renew { grownView with programVersion := 0 }
      { exhausted0 with programVersion := 1 } with
  | .error .staleSnapshot => true
  | _ => false

-- Fixed view, cursor, and limits give the exact same step.
#guard
  match take generation0 (limits 7 3) view0 cursor0,
      take generation0 (limits 7 3) view0 cursor0 with
  | .yielded left leftCursor, .yielded right rightCursor =>
      left == right && leftCursor == rightCursor
  | _, _ => false

/-! ## Arbitrary-function instantiation canary -/

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "matcher.source" }
def negKey : OpKey := { name := "matcher.neg" }
def sinKey : OpKey := { name := "matcher.sin" }

def sinContractKey : RuleKey := { name := "matcher.sin.contract" }

def operations : Array Operation :=
  #[{ key := sourceKey, inputs := [], output := real },
    { key := negKey, inputs := [real], output := real },
    { key := sinKey, inputs := [real], output := real }]

def node (index : Nat) : NodeId := { index }

def initialProgram : Program :=
  { operations
    nodes :=
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 1 }, args := [node 0] },
        { domain := real, op := { index := 2 }, args := [node 1] }] }

def extendedProgram : Program :=
  { initialProgram with
    nodes := initialProgram.nodes ++
      #[{ domain := real, op := { index := 0 }, args := [] },
        { domain := real, op := { index := 1 }, args := [node 3] },
        { domain := real, op := { index := 2 }, args := [node 4] }] }

def programView (program : Program) (version : Nat) : ProgramView :=
  { programVersion := version
    operations := program.operations
    nodes := program.nodes
    generations := Array.replicate program.nodes.size 0
    depths := program.depths?.getD #[] }

/-- Package-owned semantic filtering of one engine-enumerated anchor. -/
def sinNeg? (program : ProgramView) (input : Input) : Option (NodeId × NodeId) := do
  let .node anchor := input.key | none
  if program.operationKey? anchor != some sinKey then none else pure ()
  let expression <- program.node? anchor
  let [negated] := expression.args | none
  if program.operationKey? negated != some negKey then none else pure ()
  let negation <- program.node? negated
  let [argument] := negation.args | none
  pure (anchor, argument)

/-- Once `sin (-x)` appears, instantiate `sin x`, `-(sin x)`, their oddness
equality, and a range contractor over the newly useful `sin x` node. -/
def oddnessRequest? (program : ProgramView) (input : Input) :
    Option InstantiationRequest := do
  let (anchor, argument) <- sinNeg? program input
  let (sinId, _) <- program.findOp? sinKey
  let (negId, _) <- program.findOp? negKey
  pure
    { key := 41
      nodes :=
        [{ domain := real, op := sinId, args := [.existing argument] },
          { domain := real, op := negId, args := [.proposed 0] }]
      equalities :=
        [{ left := .existing anchor
           right := .proposed 1
           payload := { index := 43 } }]
      scopes :=
        [{ rule := sinContractKey
           anchor := .proposed 0
           watches := [.existing argument]
           writes := [.proposed 0] }]
      payload := { index := 47 } }

def shapeView0 : View :=
  { programVersion := 0
    size := { nodes := 3 } }

def shapeGeneration0 : Key -> Option Nat :=
  generations #[0, 0, 0] #[] #[]

def initialMatch? : Option (Cursor × InstantiationRequest) := do
  let .yielded inputs cursor :=
    take shapeGeneration0 (limits 3 3) shapeView0 (Cursor.start shapeView0) | none
  let request <- inputs.toList.findSome? (oddnessRequest? (programView initialProgram 0))
  pure (cursor, request)

#guard initialProgram.check
#guard extendedProgram.check

#guard
  match initialMatch? with
  | some (cursor, request) =>
      cursor.exhausted &&
        match request.nodes, request.equalities, request.scopes with
        | [sinNode, negNode], [equality], [scope] =>
            sinNode.op == { index := 2 } && sinNode.args == [.existing (node 0)] &&
              negNode.op == { index := 1 } && negNode.args == [.proposed 0] &&
              equality.left == .existing (node 2) &&
              equality.right == .proposed 1 &&
              scope.rule == sinContractKey && scope.anchor == .proposed 0 &&
              scope.watches == [.existing (node 0)] &&
              scope.writes == [.proposed 0]
        | _, _, _ => false
  | none => false

def shapeView1 : View :=
  { programVersion := 1
    size := { nodes := 6 } }

def shapeGeneration1 : Key -> Option Nat :=
  generations #[0, 0, 0, 1, 1, 1] #[] #[]

-- After append-only growth, renewal exposes only the new suffix and the same
-- package filter finds the second `sin (-x)` occurrence.
#guard
  match initialMatch? with
  | some (cursor, _) =>
      match renew shapeView1 cursor with
      | .ok cursor =>
          match take shapeGeneration1 (limits 6 3) shapeView1 cursor with
          | .yielded inputs next =>
              inputs.map (fun input => input.key) ==
                  #[.node (node 3), .node (node 4), .node (node 5)] &&
                next.exhausted &&
                match inputs.toList.findSome?
                    (oddnessRequest? (programView extendedProgram 1)) with
                | some request =>
                    match request.equalities with
                    | [equality] => equality.left == .existing (node 5)
                    | _ => false
                | none => false
          | _ => false
      | .error _ => false
  | none => false

/-! ## Existing atomic admission path -/

abbrev Rank := Nat

def rankDomain : FactDomain Rank where
  top _ := 0
  narrow _ current candidate :=
    if current < candidate then .improved candidate else .noChange

def matcherKey : RuleKey := { name := "matcher.sin.oddness" }

def matcherRule : Registration :=
  { key := matcherKey
    head := sinKey
    kind := .instantiate
    watches := []
    writes := [] }

def sinContractRule : Registration :=
  { key := sinContractKey
    head := sinKey
    kind := .improve
    watches := []
    writes := []
    binding := .scoped }

def engineLimits : Experiment.Propagator.Limits :=
  { maxOperations := 4
    maxNodes := 8
    maxRules := 4
    maxArity := 2
    maxScopeNodes := 2
    maxApplications := 8
    maxQueueEntries := 16
    maxActions := 16
    maxAcceptedFacts := 8
    maxRetainedSuggestions := 4
    maxEffort := 2
    maxObservationValue := 16
    maxDiagnosticValue := 16
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 2
    maxProposalItems := 4
    maxInstances := 4
    maxGeneration := 4
    maxNodeDepth := 8
    maxEqualities := 4
    splitEndpointLimit :=
      { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def started? : Option (Engine Rank) :=
  match Engine.start rankDomain initialProgram
      #[matcherRule, sinContractRule] #[0, 0, 0] engineLimits with
  | .ok state => some state
  | .error _ => none

-- The engine wrapper reads creation generations directly from the three
-- structural arenas; freezing the size view does not copy those arenas.
#guard
  match started? with
  | some state =>
      let view := Experiment.Propagator.StructuralMatcher.Engine.matcherView state
      match Experiment.Propagator.StructuralMatcher.Engine.takeMatches
          state (limits 4 4) (Cursor.start view) with
      | .yielded inputs cursor =>
          inputs ==
              #[{ key := .node (node 0), generation := 0 },
                { key := .node (node 1), generation := 0 },
                { key := .node (node 2), generation := 0 },
                { key := .application { index := 0 }, generation := 0 }] &&
            cursor.exhausted
      | _ => false
  | none => false

def retained? : Option (Engine Rank) := do
  let state <- started?
  let request <- oddnessRequest? (programView initialProgram 0)
    { key := .node (node 2), generation := 0 }
  match state.poll with
  | .request invocation awaiting =>
      if invocation.action.key != matcherKey || invocation.action.node != node 2 then
        none
      else
        match awaiting.submit
            (invocation.action.reply (.success [] [.instantiate request] {})) with
        | .accepted plan retained =>
            if plan.kept.length == 1 && retained.suggestions.size == 1 then
              some retained
            else
              none
        | _ => none
  | _ => none

structure Fingerprint where
  programVersion : Nat
  nodes : Nat
  bindings : Nat
  applications : Nat
  equalities : Nat
  facts : Nat
  history : Nat
  instances : Nat
  instanceHistory : Nat
  queue : Nat
  queueHead : Nat
  suggestions : Nat
  pending : Bool
  deriving DecidableEq, Repr

def fingerprint (state : Engine Rank) : Fingerprint :=
  { programVersion := state.programVersion
    nodes := state.program.nodes.size
    bindings := state.bindings.size
    applications := state.applications.size
    equalities := state.equalities.size
    facts := state.facts.size
    history := state.history.size
    instances := state.instances.length
    instanceHistory := state.instanceHistory.size
    queue := state.queue.size
    queueHead := state.queueHead
    suggestions := state.suggestions.size
    pending := state.pending.isSome }

def refusedUnchanged (resource : Resource) (limits : Experiment.Propagator.Limits) : Bool :=
  match retained? with
  | none => false
  | some state =>
      match ({ state with limits }).admitInstantiation { index := 0 } with
      | .resourceLimit actual after =>
          actual == resource && fingerprint after == fingerprint { state with limits }
      | _ => false

-- Every one-short structural capacity rejects the whole transition.
#guard refusedUnchanged .nodes { engineLimits with maxNodes := 4 }
#guard refusedUnchanged .equalities { engineLimits with maxEqualities := 0 }
#guard refusedUnchanged .applications { engineLimits with maxApplications := 2 }
#guard refusedUnchanged .queueEntries { engineLimits with maxQueueEntries := 3 }

-- The affordable transition atomically adds the function expressions,
-- oddness equality, arbitrary-scope propagator, local matcher application,
-- generations, and queue work.
#guard
  match retained? with
  | some retained =>
      match retained.admitInstantiation { index := 0 } with
      | .admitted [sinX, negSinX] state =>
          sinX == node 3 && negSinX == node 4 &&
            state.programVersion == 1 && state.program.nodes.size == 5 &&
            state.bindings.size == 1 && state.applications.size == 3 &&
            state.equalities.size == 1 && state.queueHead == 1 &&
            state.queue.size == 4 && state.instanceHistory.size == 1 &&
            state.generations[3]? == some 1 && state.generations[4]? == some 1 &&
            match state.bindings[0]?, state.applications[1]?,
                state.applications[2]?, state.equalities[0]?,
                state.instanceHistory[0]? with
            | some binding, some scopedApp, some localApp, some equality, some event =>
                binding.rule == sinContractKey && binding.anchor == sinX &&
                  binding.watches == [node 0] && binding.writes == [sinX] &&
                  scopedApp.node == sinX && scopedApp.watches == [node 0] &&
                  scopedApp.writes == [sinX] && scopedApp.generation == 1 &&
                  localApp.node == sinX && localApp.rule.index == 0 &&
                  localApp.generation == 1 &&
                  equality.left == node 2 && equality.right == negSinX &&
                  equality.generation == 1 &&
                  event.newNodes == [sinX, negSinX] &&
                  event.newApplications == [{ index := 1 }] &&
                  event.equalities == [{ index := 0 }]
            | _, _, _, _, _ => false
      | _ => false
  | none => false

end Hex.Interval.StructuralMatcherConformance
