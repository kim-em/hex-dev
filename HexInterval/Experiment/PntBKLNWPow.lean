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

def engineLimits : Hex.Interval.State.Limits :=
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

/-! ## Complete source-pinned power ladder

The original `pow433` canary above deliberately remains stable.  The smaller
PNT+ bounds need a finer provider: exact rational upper bounds for the bases
`2^(1/k - 1/3)`, `4 ≤ k ≤ 20`, followed by one uniform `k ≥ 21` tail.  The
following schema is parameterized by the source limit and authenticates the
source endpoint rather than selecting a theorem by an unchecked tag. -/

/-- One source-pinned row of the BKLNW `pow*_upper` interface. -/
structure SourceRecord where
  limit : Nat
  targetNumerator : Nat
  targetDenominator : Nat
  deriving DecidableEq, Repr

def sourceRecord? : Nat → Option SourceRecord
  | 29 => some ⟨29, 14263, 10000⟩
  | 37 => some ⟨37, 12196, 10000⟩
  | 44 => some ⟨44, 11211, 10000⟩
  | 51 => some ⟨51, 107087, 100000⟩
  | 58 => some ⟨58, 104320, 100000⟩
  | 63 => some ⟨63, 103253, 100000⟩
  | 145 => some ⟨145, 10002421, 10000000⟩
  | 217 => some ⟨217, 1000003758, 1000000000⟩
  | 289 => some ⟨289, 100000007813, 100000000000⟩
  | 361 => some ⟨361, 100000002125, 100000000000⟩
  | 433 => some ⟨433, 100000002937, 100000000000⟩
  | _ => none

def sourceLimits : List Nat := [29, 37, 44, 51, 58, 63, 145, 217, 289, 361, 433]

/-- The shared rational-base certificate.  The base table itself is
package-owned; these fields authenticate its interpretation and the exact
source row being requested. -/
structure LadderCertificate where
  limit : Nat
  exactStart : Nat
  exactStop : Nat
  tailStart : Nat
  tailCardinality : Nat
  baseDenominator : Nat
  targetNumerator : Nat
  targetDenominator : Nat
  deriving DecidableEq, Repr

def baseDenominator : Nat := 100000000

/-- Upward-rounded eight-decimal bounds for `2^(1/k - 1/3)`, `k = 4..21`.
The Mathlib companion proves every entry from the package-owned log-2 series
and an exponential remainder bound. -/
def baseNumerators : List Nat :=
  [94387432, 91172249, 89089872, 87631643, 86553657, 85724399,
    85066717, 84532368, 84089642, 83716839, 83398610, 83123790,
    82884066, 82673118, 82486060, 82319051, 82169032, 82033536]

def exactBaseNumerators : List Nat := baseNumerators.take 17
def tailBaseNumerator : Nat := baseNumerators.getD 17 0

def sumPowers (exponent : Nat) : List Nat → Nat
  | [] => 0
  | value :: values => value ^ exponent + sumPowers exponent values

def ladderSumNumerator (value : LadderCertificate) : Nat :=
  value.baseDenominator ^ value.limit +
    sumPowers value.limit exactBaseNumerators +
    value.tailCardinality * tailBaseNumerator ^ value.limit

def ladderSumDenominator (value : LadderCertificate) : Nat :=
  value.baseDenominator ^ value.limit

def ladderCertificateFor? (limit : Nat) : Option LadderCertificate := do
  let source ← sourceRecord? limit
  some
    { limit := source.limit
      exactStart := 4
      exactStop := 20
      tailStart := 21
      tailCardinality := source.limit - 20
      baseDenominator
      targetNumerator := source.targetNumerator
      targetDenominator := source.targetDenominator }

def ladderCertificateBody (value : LadderCertificate) : List Nat :=
  [value.limit, value.exactStart, value.exactStop, value.tailStart,
    value.tailCardinality, value.baseDenominator,
    value.targetNumerator, value.targetDenominator]

def decodeLadderCertificate? : List Nat → Option LadderCertificate
  | [limit, exactStart, exactStop, tailStart, tailCardinality,
      denominator, targetNumerator, targetDenominator] =>
      some
        { limit, exactStart, exactStop, tailStart, tailCardinality,
          baseDenominator := denominator, targetNumerator, targetDenominator }
  | _ => none

/-- The checker pins the split, base-table scale, exact source endpoint, tail
cardinality, and the final all-natural rational inequality. -/
def LadderValid (value : LadderCertificate) : Prop :=
  sourceRecord? value.limit =
      some ⟨value.limit, value.targetNumerator, value.targetDenominator⟩ ∧
    21 ≤ value.limit ∧
    value.exactStart = 4 ∧ value.exactStop = 20 ∧ value.tailStart = 21 ∧
    value.tailCardinality + 20 = value.limit ∧
    value.baseDenominator = baseDenominator ∧
    0 < value.targetDenominator ∧
    alphaNumerator * ladderSumNumerator value * value.targetDenominator ≤
      value.targetNumerator *
        (alphaDenominator * ladderSumDenominator value)

instance (value : LadderCertificate) : Decidable (LadderValid value) := by
  unfold LadderValid
  infer_instance

def validLadderCertificate (value : LadderCertificate) : Bool :=
  decide (LadderValid value)

def defaultLadderCertificate : LadderCertificate :=
  ⟨0, 0, 0, 0, 0, 0, 0, 0⟩

def ladder29 : LadderCertificate :=
  (ladderCertificateFor? 29).getD defaultLadderCertificate
def ladder37 : LadderCertificate :=
  (ladderCertificateFor? 37).getD defaultLadderCertificate
def ladder44 : LadderCertificate :=
  (ladderCertificateFor? 44).getD defaultLadderCertificate
def ladder51 : LadderCertificate :=
  (ladderCertificateFor? 51).getD defaultLadderCertificate
def ladder58 : LadderCertificate :=
  (ladderCertificateFor? 58).getD defaultLadderCertificate
def ladder63 : LadderCertificate :=
  (ladderCertificateFor? 63).getD defaultLadderCertificate
def ladder145 : LadderCertificate :=
  (ladderCertificateFor? 145).getD defaultLadderCertificate
def ladder217 : LadderCertificate :=
  (ladderCertificateFor? 217).getD defaultLadderCertificate
def ladder289 : LadderCertificate :=
  (ladderCertificateFor? 289).getD defaultLadderCertificate
def ladder361 : LadderCertificate :=
  (ladderCertificateFor? 361).getD defaultLadderCertificate

def ladderFactFormat : ReplayFormat :=
  { role := .fact
    schema := 2
    validateBody := fun cells =>
      (decodeLadderCertificate? cells).any validLadderCertificate }

def ladderPlanForBody (cells : List Nat) (request : RuleRequest Bound) : Plan Bound :=
  match decodeLadderCertificate? cells with
  | some value =>
      if validLadderCertificate value then
        match request.inputs, request.writes with
        | [], [target] =>
            { outcome :=
                .success [{ node := target, fact := .upper, payload }] []
                  { arithmeticWork := value.limit * 18,
                    estimatedProofNodes := 36 }
              drafts :=
                [{ label := payload, role := .fact, schema := 2, body := cells }] }
        | _, _ => { outcome := .failed 1, drafts := [] }
      else { outcome := .failed 2, drafts := [] }
  | none => { outcome := .failed 3, drafts := [] }

def ladderPackageFor (value : LadderCertificate) : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[foldOperation]
    handlers := #[Handler.statelessPlanned foldRule
      (ladderPlanForBody (ladderCertificateBody value)) #[ladderFactFormat]] }

def ladderPackagesFor (value : LadderCertificate) : Array (Package Bound) :=
  #[ladderPackageFor value]

def ladderStart (value : LadderCertificate) :
    Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program (ladderPackagesFor value) #[.all]
    { limits with
      engine := { limits.engine with
        maxEffort := value.limit * 18
        maxObservationValue := value.limit * 18
        maxDiagnosticValue := value.limit * 18 }
      arena := { limits.arena with
        maxAtom := max limits.arena.maxAtom value.targetNumerator
        maxSchema := 2 } }

end Hex.Interval.Experiment.PntBKLNWPow
