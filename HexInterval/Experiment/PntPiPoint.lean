/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession
public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# Source-pinned PNT+ π bound

This package exposes a provider-agnostic constant-enclosure boundary. The
Mathlib-free side authenticates only the π operation key, exact request fact,
and rational upper cut; the Mathlib companion supplies the proved identity and
bound.
-/

namespace Hex.Interval.Experiment.PntPiPoint

open Propagator PayloadArena

structure Cut where
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

inductive Bound where
  | all
  | request
  | upper (cut : Cut)
  | empty
  deriving DecidableEq, Repr

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    if current == proposed then .noChange
    else match current, proposed with
      | _, .all => .noChange
      | .all, proposed => .improved proposed
      | _, _ => .malformed 1

structure Certificate where
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

def certificate : Certificate := { numerator := 315, denominator := 100 }
def Certificate.cut (value : Certificate) : Cut :=
  { numerator := value.numerator, denominator := value.denominator }
def Certificate.valid (value : Certificate) : Bool :=
  value == certificate && decide (0 < value.denominator)
def encode (value : Certificate) : List Nat := [value.numerator, value.denominator]
def decode? : List Nat → Option Certificate
  | [numerator, denominator] =>
      let value : Certificate := { numerator, denominator }
      if value.valid then some value else none
  | _ => none

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "pnt-pi-point.source" }
def piKey : OpKey := { name := "pnt-pi-point.pi" }
def ruleKey : RuleKey := { name := "pnt-pi-point.bound" }
def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def piOperation : Operation := { key := piKey, inputs := [real], output := real }
def operations : Array Operation := #[sourceOperation, piOperation]
def node (index : Nat) : NodeId := { index }
def payload : PayloadId := { index := 0 }
def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def piInstruction : Node := { domain := real, op := { index := 1 }, args := [node 0] }
def program : Program := { operations, nodes := #[sourceInstruction, piInstruction] }

def registration : Registration :=
  { key := ruleKey, head := piKey, kind := .forward,
    watches := [.argument 0], writes := [.result] }
def factFormat : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun body => (decode? body).isSome }

def plan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      if input.fact == .request then
        { outcome :=
            .success [{ node := target, fact := .upper certificate.cut, payload }] []
              { arithmeticWork := 1, estimatedProofNodes := 4 },
          drafts :=
            [{ label := payload, role := .fact, schema := 1,
               body := encode certificate }] }
      else { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }
def piPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[piOperation],
    handlers := #[Handler.statelessPlanned registration plan #[factFormat]] }
def packages : Array (Package Bound) := #[sourcePackage, piPackage]

def checkerInput : SemanticReplay.CheckerInput Bound :=
  { baseProgram := program, initialFacts := #[.request, .all],
    target := { node := node 1, fact := .upper certificate.cut } }

def engineLimits : State.Limits :=
  { maxOperations := 2, maxNodes := 2, maxRules := 1, maxRegistryEntries := 8,
    maxReplayFormats := 2, maxArity := 1, maxScopeNodes := 1, maxApplications := 2,
    maxQueueEntries := 8, maxActions := 4, maxMatcherVisits := 2,
    matcherBatchSize := 2, maxAcceptedFacts := 2, maxRetainedSuggestions := 0,
    maxEffort := 0, maxObservationValue := 8, maxDiagnosticValue := 315,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0, maxProposalItems := 1,
    maxInstances := 0, maxGeneration := 0, maxNodeDepth := 2, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 4 } }
def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8, maxTraversal := 32, maxLiveOffers := 8 }
def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4, maxBodyCells := 4, maxDrafts := 2, maxDraftCells := 4,
    maxAtom := 315, maxSchema := 1, maxUses := 2 }
def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.PntPiPoint
