/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.DyadicRules

/-!
End-to-end conformance for concrete arbitrary-function propagators.  These
fixtures run the generic worklist; they do not call interval operations in
place of the registry when checking the final facts.
-/

namespace Hex.Interval.DyadicRulesConformance

open Experiment Propagator
open DyadicRules

def d (value : Int) : Dyadic := Dyadic.ofInt value

def real : DomainId := { index := 0 }
def sourceOp : OpKey := { name := "real.source" }

def endpointLimit : EndpointLimit where
  maxEndpointHeight := 128
  maxAlignmentShift := 64

def config : Config :=
  { endpointLimit
    reciprocalBasePrecision := 2
    maxReciprocalEffort := 4 }

def registry : Registry := { config }

def limits : Experiment.Propagator.Limits :=
  { maxOperations := 16
    maxNodes := 32
    maxRules := 16
    maxArity := 4
    maxApplications := 64
    maxQueueEntries := 256
    maxActions := 128
    maxAcceptedFacts := 128
    maxRetainedSuggestions := 32
    maxEffort := 8
    maxObservationValue := 256
    maxOutcomeCandidates := 4
    maxOutcomeSuggestions := 4
    maxProposalItems := 16
    maxInstances := 8
    maxGeneration := 4
    maxEqualities := 8
    splitEndpointLimit := endpointLimit }

def allOperations : Array Operation :=
  operations real |>.push { key := sourceOp, inputs := [], output := real }

def instruction (operation : Nat) (args : List NodeId := []) : Node :=
  { domain := real, op := { index := operation }, args }

def node (index : Nat) : NodeId := { index }
def suggestion (index : Nat) : SuggestionId := { index }

def finite (lower : Int) (lowerStrict : Bool)
    (upper : Int) (upperStrict : Bool) : Raw :=
  .bounds (.finite (d lower) lowerStrict) (.finite (d upper) upperStrict)

def whole : Raw := .bounds .unbounded .unbounded

def exactFact (state : Engine Fact) (index : Nat) (expected : Raw) : Bool :=
  (state.facts[index]?).any fun fact => fact.view == expected

/-! ## Exact backward singleton multiplication -/

/-- Nodes are `2`, `y`, and `z = 2*y`.  The output and input cuts deliberately
mix strict and closed endpoints. -/
def scaleProgram : Program :=
  { operations := allOperations
    nodes :=
      #[instruction 7,
        instruction 7,
        instruction 3 [node 0, node 1]] }

def scaleStart? : Option (Engine Fact) :=
  match DyadicInterval.start endpointLimit scaleProgram registrations
      #[finite 2 false 2 false,
        .bounds (.finite 0 true) .unbounded,
        finite 2 true 6 false]
      limits with
  | .ok state => some state
  | .error _ => none

def scaleFinal? : Option (RunResult Fact Unit) := do
  let state <- scaleStart?
  pure (drive registry.invokeWithCache 32 state ())

#guard scaleProgram.check
#guard registrationsCheck scaleProgram registrations

-- The unbounded forward image is honestly inapplicable.  The exact singleton
-- backward contractor nevertheless derives `(1,3]`, then the now-finite
-- forward rule confirms the existing `(2,6]` output.
#guard
  match scaleFinal? with
  | some result =>
      result.stop == .saturated && result.state.metrics.requests == 6 &&
        result.state.metrics.improvements == 1 &&
        result.state.metrics.ruleInapplicable == 4 &&
        exactFact result.state 0 (finite 2 false 2 false) &&
        exactFact result.state 1 (finite 1 true 3 false) &&
        exactFact result.state 2 (finite 2 true 6 false)
  | none => false

/-! ## Mixed forward/backward cycles -/

/-- Three disconnected components exercise negation backward, subtraction
backward-left, and an open square image in one worklist. -/
def cycleProgram : Program :=
  { operations := allOperations
    nodes :=
      #[instruction 7,
        instruction 1 [node 0],
        instruction 7,
        instruction 7,
        instruction 2 [node 3, node 2],
        instruction 7,
        instruction 4 [node 5]] }

def cycleStart? : Option (Engine Fact) :=
  match DyadicInterval.start endpointLimit cycleProgram registrations
      #[whole,
        finite 1 false 2 false,
        finite 1 false 2 false,
        whole,
        finite 3 false 4 false,
        finite (-1) true 1 true,
        whole]
      limits with
  | .ok state => some state
  | .error _ => none

def cycleFinal? : Option (RunResult Fact Unit) := do
  let state <- cycleStart?
  pure (drive registry.invokeWithCache 48 state ())

#guard cycleProgram.check
#guard registrationsCheck cycleProgram registrations

#guard
  match cycleFinal? with
  | some result =>
      result.stop == .saturated && !result.state.contradictory &&
        exactFact result.state 0 (finite (-2) false (-1) false) &&
        exactFact result.state 1 (finite 1 false 2 false) &&
        exactFact result.state 2 (finite 1 false 2 false) &&
        exactFact result.state 3 (finite 4 false 6 false) &&
        exactFact result.state 4 (finite 3 false 4 false) &&
        exactFact result.state 5 (finite (-1) true 1 true) &&
        exactFact result.state 6 (finite 0 false 1 true)
  | none => false

/-! ## Dependency loss and centered instantiation -/

/-- `x`, `1`, `1-x`, and `x*(1-x)`. -/
def centeredProgram : Program :=
  { operations := allOperations
    nodes :=
      #[instruction 7,
        instruction 0,
        instruction 2 [node 1, node 0],
        instruction 3 [node 0, node 2]] }

def centeredStart? : Option (Engine Fact) :=
  match DyadicInterval.start endpointLimit centeredProgram registrations
      #[finite 0 false 1 false,
        finite 1 false 1 false,
        whole,
        whole]
      limits with
  | .ok state => some state
  | .error _ => none

def centeredInitial? : Option (RunResult Fact Unit) := do
  let state <- centeredStart?
  pure (drive registry.invokeWithCache 32 state ())

def centeredFinal? : Option (RunResult Fact Unit) := do
  let initial <- centeredInitial?
  match initial.state.admitInstantiation (suggestion 0) with
  | .admitted [centered] state =>
      if centered == node 4 then
        some (drive registry.invokeWithCache 32 state ())
      else
        none
  | _ => none

#guard centeredProgram.check
#guard registrationsCheck centeredProgram registrations

-- Ordinary interval evaluation loses the dependency between the two
-- occurrences of `x` and obtains only `[0,1]`.  The shape rule has no fact
-- inputs, but retains an engine-indexed proposal for the alternate form.
#guard
  match centeredInitial? with
  | some result =>
      result.stop == .saturated && result.state.programVersion == 0 &&
        result.state.suggestions.size == 1 &&
        exactFact result.state 2 (finite 0 false 1 false) &&
        exactFact result.state 3 (finite 0 false 1 false) &&
        match result.state.suggestions[0]? with
        | some retained =>
            retained.action.key == centeredInstantiateKey &&
              retained.action.inputs.isEmpty &&
              match retained.suggestion with
              | .instantiate request =>
                  request.triggers == [node 3, node 0, node 2, node 1] &&
                    request.claimedGeneration == 1 && request.nodes.length == 1 &&
                    request.equalities.length == 1
              | _ => false
        | none => false
  | none => false

-- Admission creates the opaque centered node and equality.  Its arbitrary
-- propagator proves `[0,1/4]`; equality transport then improves the original
-- product to the same fact.
#guard
  match centeredFinal? with
  | some result =>
      result.stop == .saturated && result.state.programVersion == 1 &&
        result.state.program.nodes.size == 5 && result.state.equalities.size == 1 &&
        result.state.generations[4]? == some 1 &&
        exactFact result.state 3
          (.bounds (.finite 0 false) (.finite quarter false)) &&
        exactFact result.state 4
          (.bounds (.finite 0 false) (.finite quarter false)) &&
        match result.state.program.node? (node 4), result.state.equalities[0]? with
        | some centered, some equality =>
            centered.args == [node 0] &&
              (result.state.program.operation? centered.op).any
                (fun operation => operation.key == centeredOp) &&
              equality.left == node 3 && equality.right == node 4
        | _, _ => false
  | none => false

/-! ## Retry and malformed dispatch boundaries -/

def reciprocalProgram : Program :=
  { operations := allOperations
    nodes := #[instruction 7, instruction 5 [node 0]] }

def reciprocalStart? : Option (Engine Fact) :=
  match DyadicInterval.start endpointLimit reciprocalProgram registrations
      #[finite 3 false 3 false, whole] limits with
  | .ok state => some state
  | .error _ => none

def reciprocalFirstRequest? : Option (RuleRequest Fact) := do
  let state <- reciprocalStart?
  match state.poll with
  | .request request _ => some request
  | _ => none

-- Precision two encloses `1/3` by open quarter-grid endpoints and emits the
-- next effort as an advisory retry.
#guard
  match reciprocalFirstRequest? with
  | some request =>
      match registry.invoke request with
      | .success [candidate] [.retry 1] _ =>
          candidate.node == node 1 &&
            candidate.fact.view ==
              .bounds (.finite quarter true) (.finite half true)
      | _ => false
  | none => false

def bogusRequest : RuleRequest Fact :=
  { action :=
      { serial := 0
        programVersion := 0
        application := { index := 0 }
        rule := { index := 0 }
        key := { name := "unknown.rule" }
        node := node 0
        kind := .forward
        effort := 0
        inputs := [] }
    program :=
      { programVersion := 0
        operations := #[]
        nodes := #[]
        generations := #[] }
    inputs := []
    writes := [] }

-- A callback outside the versioned registry cannot manufacture a candidate;
-- unknown dispatch is a diagnostic failure with no writes.
#guard
  match registry.invoke bogusRequest with
  | .failed 255 => true
  | _ => false

end Hex.Interval.DyadicRulesConformance
