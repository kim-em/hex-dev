/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Arbitrary sine and negation packages over a small range lattice

This Mathlib-free vertical exercises the function-package boundary without a
rational-arithmetic backend.  A global structural matcher recognizes
`sin (-x)`, proposes the two auxiliary expressions `sin x` and `-(sin x)`,
and records their equality with the original expression.  Independent local
sine and negation propagators then refine the two new nodes.

`Range` is deliberately tiny: it contains only the regions needed by the
example.  Neither the scheduler nor this module assigns those regions a real
meaning.  The Mathlib companion owns that interpretation and all theorem
schemas.
-/

namespace Hex.Interval.Experiment.SineSign

open Propagator PayloadArena

/-! ## Mathlib-free fact domain -/

/-- A finite range lattice used to test arbitrary-function propagation.
`unit` will be interpreted as `[0, 1]` by the Mathlib companion. -/
inductive Range where
  | all
  | unit
  | nonnegative
  | nonpositive
  | zero
  | empty
  deriving DecidableEq, Repr

namespace Range

/-- Exact intersection in the small range lattice. -/
def meet : Range -> Range -> Range
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .unit, .unit => .unit
  | .unit, .nonnegative | .nonnegative, .unit => .unit
  | .unit, .nonpositive | .nonpositive, .unit => .zero
  | .unit, .zero | .zero, .unit => .zero
  | .nonnegative, .nonnegative => .nonnegative
  | .nonnegative, .nonpositive | .nonpositive, .nonnegative => .zero
  | .nonnegative, .zero | .zero, .nonnegative => .zero
  | .nonpositive, .nonpositive => .nonpositive
  | .nonpositive, .zero | .zero, .nonpositive => .zero
  | .zero, .zero => .zero

/-- Stable certificate atom for one range. -/
def code : Range -> Nat
  | .all => 0
  | .unit => 1
  | .nonnegative => 2
  | .nonpositive => 3
  | .zero => 4
  | .empty => 5

/-- Decode the stable certificate atom for one range. -/
def ofCode? : Nat -> Option Range
  | 0 => some .all
  | 1 => some .unit
  | 2 => some .nonnegative
  | 3 => some .nonpositive
  | 4 => some .zero
  | 5 => some .empty
  | _ => none

end Range

/-- Engine-facing intersection for the small range lattice. -/
def factDomain : FactDomain Range where
  top _ := .all
  narrow _ current proposed :=
    let installed := Range.meet current proposed
    if installed == current then
      .noChange
    else if installed == .empty then
      .contradiction installed
    else
      .improved installed

/-! ## Opaque operation and rule keys -/

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "sine-sign.source" }
def negationKey : OpKey := { name := "sine-sign.negation" }
def sineKey : OpKey := { name := "sine-sign.sine" }

def negationRuleKey : RuleKey := { name := "sine-sign.negation.forward" }
def sineRuleKey : RuleKey := { name := "sine-sign.sine.nonnegative" }
def oddnessRuleKey : RuleKey := { name := "sine-sign.sine.oddness" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def negationOperation : Operation :=
  { key := negationKey, inputs := [real], output := real }

def sineOperation : Operation :=
  { key := sineKey, inputs := [real], output := real }

def operations : Array Operation :=
  #[sourceOperation, negationOperation, sineOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }

def negatedSourceInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

def sineNegatedSourceInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 1] }

/-- The caller graph for `sin (-x)`. -/
def baseProgram : Program :=
  { operations
    nodes :=
      #[sourceInstruction, negatedSourceInstruction,
        sineNegatedSourceInstruction] }

def sineSourceInstruction : Node :=
  { domain := real, op := { index := 2 }, args := [node 0] }

def negatedSineInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 3] }

/-- The exact graph obtained by the oddness instantiator. -/
def extendedProgram : Program :=
  { operations
    nodes := baseProgram.nodes ++ #[sineSourceInstruction, negatedSineInstruction] }

/-! ## Separate arbitrary-function propagators -/

def negationRule : Registration :=
  { key := negationRuleKey
    head := negationKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def sineRule : Registration :=
  { key := sineRuleKey
    head := sineKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def oddnessRule : Registration :=
  { key := oddnessRuleKey
    head := sineKey
    kind := .instantiate
    watches := []
    writes := []
    binding := .global
    watchesProgram := true
    matchWatch := .network }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body =>
      match body with
      | [code] => (Range.ofCode? code).isSome
      | _ => false }

def instanceFormat : ReplayFormat :=
  { role := .instance
    schema := 1
    validateBody := fun body => body == [1] }

def equalityFormat : ReplayFormat :=
  { role := .equality
    schema := 1
    validateBody := fun body => body == [1] }

def negationImage? : Range -> Option Range
  | .all => none
  | .unit | .nonnegative => some .nonpositive
  | .nonpositive => some .nonnegative
  | .zero => some .zero
  | .empty => some .empty

def sineImage? : Range -> Option Range
  | .unit => some .nonnegative
  | .zero => some .zero
  | _ => none

def unaryPlan (image? : Range -> Option Range) (label : PayloadId)
    (request : RuleRequest Range) : Plan Range :=
  match request.inputs, request.writes with
  | [input], [target] =>
      match image? input.fact with
      | none => { outcome := .noChange {}, drafts := [] }
      | some fact =>
          { outcome :=
              .success [{ node := target, fact, payload := label }] [] {}
            drafts :=
              [{ label
                 role := .fact
                 schema := 1
                 body := [fact.code] }] }
  | _, _ => { outcome := .failed 1, drafts := [] }

/-- Executable negation propagation, independent of sine. -/
def negationPlan : RuleRequest Range -> Plan Range :=
  unaryPlan negationImage? (payload 20)

/-- Executable sine sign propagation, independent of negation. -/
def sinePlan : RuleRequest Range -> Plan Range :=
  unaryPlan sineImage? (payload 21)

/-! ## Shape-triggered oddness instantiation -/

/-- Recognize `sin (-x)` and add `sin x`, `-(sin x)`, and their equality to
the original expression.  This is expression-network growth, not arithmetic
fact propagation. -/
def oddness? (view : ProgramView) (input : StructuralInput) :
    Option InstantiationRequest := do
  let .node anchor := input.key | none
  if view.operationKey? anchor != some sineKey then none else pure ()
  let expression <- view.node? anchor
  let [negated] := expression.args | none
  if view.operationKey? negated != some negationKey then none else pure ()
  let negation <- view.node? negated
  let [argument] := negation.args | none
  let (sineId, _) <- view.findOp? sineKey
  let (negationId, _) <- view.findOp? negationKey
  pure
    { key := 1
      nodes :=
        [{ domain := real, op := sineId, args := [.existing argument] },
          { domain := real, op := negationId, args := [.proposed 0] }]
      equalities :=
        [{ left := .existing anchor
           right := .proposed 1
           payload := payload 23 }]
      payload := payload 22 }

def oddnessPlan (request : RuleRequest Range) : Plan Range :=
  match request.action.structuralInputs.findSome? (oddness? request.program) with
  | none => { outcome := .noChange {}, drafts := [] }
  | some proposal =>
      { outcome := .success [] [.instantiate proposal] {}
        drafts :=
          [{ label := payload 22
             role := .instance
             schema := 1
             body := [1] },
           { label := payload 23
             role := .equality
             schema := 1
             body := [1] }] }

/-! ## Independently assembled packages -/

/-- Nullary source expressions.  This package contributes no propagator. -/
def sourcePackage : Package Range :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation]
    handlers := #[] }

/-- The negation operation and its standalone forward propagator. -/
def negationPackage : Package Range :=
  { Cache := Unit
    cache := ()
    operations := #[negationOperation]
    handlers :=
      #[Handler.statelessPlanned negationRule negationPlan #[factFormat]] }

/-- The sine operation, sine-sign propagator, and oddness instantiator.  The
matcher declares negation as an exact external dependency. -/
def sinePackage : Package Range :=
  { Cache := Unit
    cache := ()
    operations := #[sineOperation]
    requiredOperations := #[negationOperation]
    handlers :=
      #[Handler.statelessPlanned sineRule sinePlan #[factFormat],
        Handler.statelessPlanned oddnessRule oddnessPlan
          #[instanceFormat, equalityFormat]] }

def packages : Array (Package Range) :=
  #[sourcePackage, negationPackage, sinePackage]

/-! ## A bounded proof-producing session -/

def engineLimits : Propagator.Limits :=
  { maxOperations := 3
    maxNodes := 5
    maxRules := 3
    maxRegistryEntries := 16
    maxReplayFormats := 4
    maxArity := 1
    maxScopeNodes := 1
    maxApplications := 7
    maxQueueEntries := 24
    maxActions := 16
    maxMatcherVisits := 8
    matcherBatchSize := 8
    maxAcceptedFacts := 8
    maxRetainedSuggestions := 2
    maxEffort := 1
    maxObservationValue := 16
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 1
    maxProposalItems := 4
    maxInstances := 1
    maxGeneration := 1
    maxNodeDepth := 4
    maxEqualities := 1
    splitEndpointLimit :=
      { maxEndpointHeight := 8, maxAlignmentShift := 4 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 24
    maxTraversal := 256
    maxLiveOffers := 24 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 16
    maxBodyCells := 32
    maxDrafts := 8
    maxDraftCells := 8
    maxAtom := 32
    maxSchema := 1
    maxUses := 8 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

/-- Start the actual arbitrary-function example from `x ∈ [0,1]`; neither
the negated input nor the requested sine expression has an initial bound. -/
def start : Except PolicySession.StartError (PolicySession.Session Range) :=
  PolicySession.Session.start factDomain baseProgram packages
    #[.unit, .all, .all] limits

end Hex.Interval.Experiment.SineSign
