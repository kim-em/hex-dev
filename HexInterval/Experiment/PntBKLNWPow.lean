/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Mathlib-free PNT+ BKLNW power-sum probe

This package replaces the source-pinned use of
`LeanCert.CertifiedBounds.BKLNW.pow433_upper`.  The untrusted provider retains
the sum limit, split coordinates, dyadic exponents, exact tail cardinality,
and rational output cut.  `validCertificate` checks the finite arithmetic;
the Mathlib companion proves that every accepted certificate bounds the exact
PNT+ finite sum.
-/

namespace Hex.Interval.Experiment.PntBKLNWPow

open Propagator PayloadArena

inductive Bound where
  | all
  | upper
  | empty
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .upper, .upper => .upper

end Bound

/-- Certificate for the analytic two-band sum fold. -/
structure FoldCertificate where
  limit : Nat
  isolatedIndex : Nat
  tailStart : Nat
  isolatedExponent : Nat
  tailExponent : Nat
  tailCardinality : Nat
  targetNumerator : Nat
  targetDenominator : Nat
  deriving DecidableEq, Repr

def certificate : FoldCertificate :=
  { limit := 433
    isolatedIndex := 4
    tailStart := 5
    isolatedExponent := 36
    tailExponent := 57
    tailCardinality := 429
    targetNumerator := 100000001948
    targetDenominator := 100000000000 }

def certificateBody (value : FoldCertificate) : List Nat :=
  [value.limit, value.isolatedIndex, value.tailStart,
    value.isolatedExponent, value.tailExponent, value.tailCardinality,
    value.targetNumerator, value.targetDenominator]

def decodeCertificate? : List Nat → Option FoldCertificate
  | [limit, isolatedIndex, tailStart, isolatedExponent, tailExponent,
      tailCardinality, targetNumerator, targetDenominator] =>
      some
        { limit, isolatedIndex, tailStart, isolatedExponent, tailExponent,
          tailCardinality, targetNumerator, targetDenominator }
  | _ => none

def alphaNumerator : Nat := 10 ^ 16 + 193571378
def alphaDenominator : Nat := 10 ^ 16

def sumNumerator (value : FoldCertificate) : Nat :=
  2 ^ (value.isolatedExponent + value.tailExponent) +
    2 ^ value.tailExponent + value.tailCardinality * 2 ^ value.isolatedExponent

def sumDenominator (value : FoldCertificate) : Nat :=
  2 ^ (value.isolatedExponent + value.tailExponent)

/-- Pure-natural certificate predicate.  Besides the source coordinates it
checks both dyadic exponent inequalities, the exact number of tail terms, the
analytic rational upper bound, and containment in the pinned PNT+ target. -/
def Valid (value : FoldCertificate) : Prop :=
  value.limit = 433 ∧ value.isolatedIndex = 4 ∧ value.tailStart = 5 ∧
    value.tailCardinality + 4 = value.limit ∧
    12 * value.isolatedExponent ≤ value.limit ∧
    15 * value.tailExponent ≤ 2 * value.limit ∧
    0 < value.targetDenominator ∧
    alphaNumerator * sumNumerator value * value.targetDenominator ≤
      value.targetNumerator * (alphaDenominator * sumDenominator value) ∧
    value.targetNumerator * 100000000000 ≤
      100000002937 * value.targetDenominator

instance (value : FoldCertificate) : Decidable (Valid value) := by
  unfold Valid
  infer_instance

def validCertificate (value : FoldCertificate) : Bool := decide (Valid value)

def body : List Nat := certificateBody certificate

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }
def foldKey : OpKey := { name := "pnt-bklnw.pow-fold" }
def foldRuleKey : RuleKey := { name := "pnt-bklnw.checked-pow-fold" }

def foldOperation : Operation := { key := foldKey, inputs := [], output := real }
def operations : Array Operation := #[foldOperation]

def node : NodeId := { index := 0 }
def payload : PayloadId := { index := 0 }
def instruction : Node := { domain := real, op := { index := 0 }, args := [] }
def program : Program := { operations, nodes := #[instruction] }

def foldRule : Registration :=
  { key := foldRuleKey
    head := foldKey
    kind := .forward
    watches := []
    writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun cells =>
      (decodeCertificate? cells).any validCertificate }

def planForBody (cells : List Nat) (request : RuleRequest Bound) : Plan Bound :=
  match decodeCertificate? cells with
  | some value =>
      if validCertificate value then
        match request.inputs, request.writes with
        | [], [target] =>
            { outcome :=
                .success [{ node := target, fact := .upper, payload }] []
                  { arithmeticWork := value.tailCardinality,
                    estimatedProofNodes := 12 }
              drafts :=
                [{ label := payload, role := .fact, schema := 1, body := cells }] }
        | _, _ => { outcome := .failed 1, drafts := [] }
      else
        { outcome := .failed 2, drafts := [] }
  | none => { outcome := .failed 3, drafts := [] }

def foldPlan : RuleRequest Bound → Plan Bound := planForBody body

def package : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[foldOperation]
    handlers := #[Handler.statelessPlanned foldRule foldPlan #[factFormat]] }

def packages : Array (Package Bound) := #[package]

def engineLimits : Propagator.Limits :=
  { maxOperations := 1
    maxNodes := 1
    maxRules := 1
    maxRegistryEntries := 4
    maxReplayFormats := 1
    maxArity := 0
    maxScopeNodes := 1
    maxApplications := 1
    maxQueueEntries := 4
    maxActions := 2
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 1
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 512
    maxDiagnosticValue := 512
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 1
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 4, maxTraversal := 8, maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 1
    maxBodyCells := 8
    maxDrafts := 1
    maxDraftCells := 8
    maxAtom := 100000002937
    maxSchema := 1
    maxUses := 1 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages #[.all] limits

end Hex.Interval.Experiment.PntBKLNWPow
