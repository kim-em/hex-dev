/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Mathlib-free PNT+ exponential-tail probe

This package is the executable half of the source-pinned
`LogTables.exp_neg_lt_1e_neg_100` acceptance vertical.  It consumes an input
known to be at most `-231` and proposes the opaque fact that its exponential
is below `10^-100`.  The certificate records the range-reduction point, the
decimal exponent, and the rational upper enclosure used for `exp (-1)`.

The executable package deliberately has no real-number or scientific-decimal
semantics.  Its Mathlib companion checks the certificate by range reduction
and exact rational arithmetic, then generic replay closes both the boundary
leaf and the reusable monotone theorem.
-/

namespace Hex.Interval.Experiment.PntExpTail

open Propagator PayloadArena

/-- Finite real-set lattice needed by the tail probe.  `atMostNeg231` is
strictly stronger than `atMostNeg230`, and both are stronger than the positive
scientific-decimal upper cut. -/
inductive Bound where
  | all
  | atMostNeg231
  | atMostNeg230
  | belowTenNeg100
  | empty
  deriving DecidableEq, Repr

namespace Bound

/-- Exact intersection for the probe's finite real-set lattice. -/
def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .atMostNeg231, _ | _, .atMostNeg231 => .atMostNeg231
  | .atMostNeg230, _ | _, .atMostNeg230 => .atMostNeg230
  | .belowTenNeg100, .belowTenNeg100 => .belowTenNeg100

end Bound

/-- The checked provider recipe: reduce at `-231`, target `10^-100`, and use
`46/125` as an outward rational upper enclosure for `exp (-1)`. -/
structure ReductionCertificate where
  reductionPoint : Nat
  decimalExponent : Nat
  pointNumerator : Nat
  pointDenominator : Nat
  deriving DecidableEq, Repr

def tailCertificate : ReductionCertificate :=
  { reductionPoint := 231
    decimalExponent := 100
    pointNumerator := 46
    pointDenominator := 125 }

def tailBody : List Nat :=
  [tailCertificate.reductionPoint, tailCertificate.decimalExponent,
    tailCertificate.pointNumerator, tailCertificate.pointDenominator]

def decodeCertificate? : List Nat → Option ReductionCertificate
  | [231, 100, 46, 125] => some tailCertificate
  | _ => none

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "pnt-exp-tail.source" }
def expKey : OpKey := { name := "pnt-exp-tail.exp" }
def tailRuleKey : RuleKey := { name := "pnt-exp-tail.range-reduce" }

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

/-- Caller graph for `Real.exp (-x)`.  The source node is interpreted as
`-x` by ordinary theorem closure. -/
def program : Program :=
  { operations, nodes := #[sourceInstruction, expInstruction] }

def tailRule : Registration :=
  { key := tailRuleKey
    head := expKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body => decodeCertificate? body == some tailCertificate }

/-- The provider only accepts the certified `-231` boundary.  In particular,
an input bounded merely by `-230` is an incompatible enclosure, not a request
for more precision. -/
def tailPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      if input.fact == .atMostNeg231 then
        { outcome :=
            .success
              [{ node := target, fact := .belowTenNeg100, payload := payload 0 }]
              [] { arithmeticWork := 231, estimatedProofNodes := 4 }
          drafts :=
            [{ label := payload 0
               role := .fact
               schema := 1
               body := tailBody }] }
      else
        { outcome := .noChange {}, drafts := [] }
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
    handlers := #[Handler.statelessPlanned tailRule tailPlan #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, expPackage]

def engineLimits : Propagator.Limits :=
  { maxOperations := 2
    maxNodes := 3
    maxRules := 1
    maxRegistryEntries := 8
    maxReplayFormats := 2
    maxArity := 1
    maxScopeNodes := 1
    maxApplications := 2
    maxQueueEntries := 8
    maxActions := 4
    maxMatcherVisits := 2
    matcherBatchSize := 2
    maxAcceptedFacts := 2
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 256
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 1
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 2
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8
    maxTraversal := 32
    maxLiveOffers := 8 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4
    maxBodyCells := 8
    maxDrafts := 2
    maxDraftCells := 4
    maxAtom := 256
    maxSchema := 1
    maxUses := 2 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages
    #[.atMostNeg231, .all] limits

end Hex.Interval.Experiment.PntExpTail
