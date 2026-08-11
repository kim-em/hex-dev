/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Mathlib-free exponential-sign propagator

This second arbitrary-function vertical is intentionally unrelated to rational
arithmetic and to sine's oddness instantiation.  A standalone package declares
an opaque exponential operation and an unconditional positivity propagator.
Its Mathlib companion supplies the real interpretation and proof schema.
-/

namespace Hex.Interval.Experiment.ExpSign

open Propagator PayloadArena

/-- Minimal fact lattice for exponential positivity. -/
inductive Bound where
  | all
  | nonnegative
  | negative
  | empty
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .nonnegative, .nonnegative => .nonnegative
  | .negative, .negative => .negative
  | .nonnegative, .negative | .negative, .nonnegative => .empty

def code : Bound → Nat
  | .all => 0
  | .nonnegative => 1
  | .empty => 2
  | .negative => 3

def ofCode? : Nat → Option Bound
  | 0 => some .all
  | 1 => some .nonnegative
  | 2 => some .empty
  | 3 => some .negative
  | _ => none

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "exp-sign.source" }
def expKey : OpKey := { name := "exp-sign.exp" }
def expRuleKey : RuleKey := { name := "exp-sign.exp.nonnegative" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def expOperation : Operation :=
  { key := expKey, inputs := [real], output := real }

def operations : Array Operation := #[sourceOperation, expOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }

def expInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

/-- Caller graph for `exp x`. -/
def program : Program :=
  { operations, nodes := #[sourceInstruction, expInstruction] }

def expRule : Registration :=
  { key := expRuleKey
    head := expKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body =>
      match body with
      | [code] => (Bound.ofCode? code).isSome
      | _ => false }

/-- Exponential positivity is independent of the input interval. -/
def expPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [_], [target] =>
      { outcome :=
          .success
            [{ node := target, fact := .nonnegative, payload := payload 0 }]
            [] {}
        drafts :=
          [{ label := payload 0
             role := .fact
             schema := 1
             body := [Bound.nonnegative.code] }] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation]
    handlers := #[] }

def expPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[expOperation]
    handlers := #[Handler.statelessPlanned expRule expPlan #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, expPackage]

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

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages #[.all, .all] limits

end Hex.Interval.Experiment.ExpSign
