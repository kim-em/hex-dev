/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntBKLNWExp

@[expose] public section

/-!
# Source-pinned BKLNW Table 10 `a₂` certificates

The 38 supporting `a₂` declarations in pinned PNT+ rows 21--24 and 26--59
all use one head-plus-tail exponential estimate.  This Mathlib-free package
authenticates the source argument, `floor (b / log 2)`, rational target, log
window, and package-owned exponential-table scale before proposing an upper
fact.  It does not evaluate the surrounding `B_8_exact` reduction.
-/

namespace Hex.Interval.Experiment.PntTable10A2

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

structure SourceRecord where
  argument : Nat
  floor : Nat
  targetNumerator : Nat
  targetDenominator : Nat
  deriving DecidableEq, Repr

def sourceRecord? : Nat → Option SourceRecord
  | 0 => some ⟨21, 30, 14394, 10000⟩
  | 1 => some ⟨22, 31, 13845, 10000⟩
  | 2 => some ⟨23, 33, 13405, 10000⟩
  | 3 => some ⟨24, 34, 12999, 10000⟩
  | 4 => some ⟨26, 37, 125, 100⟩
  | 5 => some ⟨27, 38, 122, 100⟩
  | 6 => some ⟨28, 40, 120, 100⟩
  | 7 => some ⟨29, 41, 118, 100⟩
  | 8 => some ⟨30, 43, 11531, 10000⟩
  | 9 => some ⟨31, 44, 11383, 10000⟩
  | 10 => some ⟨32, 46, 11257, 10000⟩
  | 11 => some ⟨33, 47, 11144, 10000⟩
  | 12 => some ⟨34, 49, 11047, 10000⟩
  | 13 => some ⟨35, 50, 10959, 10000⟩
  | 14 => some ⟨36, 51, 10883, 10000⟩
  | 15 => some ⟨37, 53, 10815, 10000⟩
  | 16 => some ⟨38, 54, 10755, 10000⟩
  | 17 => some ⟨39, 56, 10702, 10000⟩
  | 18 => some ⟨40, 57, 10654, 10000⟩
  | 19 => some ⟨41, 59, 10612, 10000⟩
  | 20 => some ⟨42, 60, 10573, 10000⟩
  | 21 => some ⟨43, 62, 1054, 1000⟩
  | 22 => some ⟨44, 63, 10508, 10000⟩
  | 23 => some ⟨45, 64, 10480, 10000⟩
  | 24 => some ⟨46, 66, 10455, 10000⟩
  | 25 => some ⟨47, 67, 10433, 10000⟩
  | 26 => some ⟨48, 69, 10412, 10000⟩
  | 27 => some ⟨49, 70, 10394, 10000⟩
  | 28 => some ⟨50, 72, 10377, 10000⟩
  | 29 => some ⟨51, 73, 10362, 10000⟩
  | 30 => some ⟨52, 75, 10348, 10000⟩
  | 31 => some ⟨53, 76, 10335, 10000⟩
  | 32 => some ⟨54, 77, 10324, 10000⟩
  | 33 => some ⟨55, 79, 10314, 10000⟩
  | 34 => some ⟨56, 80, 10304, 10000⟩
  | 35 => some ⟨57, 82, 10295, 10000⟩
  | 36 => some ⟨58, 83, 10287, 10000⟩
  | 37 => some ⟨59, 85, 10280, 10000⟩
  | _ => none

def logLowerNumerator : Nat := 69314718055994530941
def logUpperNumerator : Nat := 69314718055994530942
def logDenominator : Nat := 10 ^ 20

structure Certificate where
  sourceIndex : Nat
  argument : Nat
  floor : Nat
  targetNumerator : Nat
  targetDenominator : Nat
  logLower : Nat
  logUpper : Nat
  logScale : Nat
  baseScale : Nat
  deriving DecidableEq, Repr

def certificateFor? (sourceIndex : Nat) : Option Certificate := do
  let source ← sourceRecord? sourceIndex
  some
    { sourceIndex
      argument := source.argument
      floor := source.floor
      targetNumerator := source.targetNumerator
      targetDenominator := source.targetDenominator
      logLower := logLowerNumerator
      logUpper := logUpperNumerator
      logScale := logDenominator
      baseScale := PntBKLNWExp.baseDenominator }

def defaultCertificate : Certificate := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def certificates : List Certificate :=
  (List.range 38).map fun index =>
    (certificateFor? index).getD defaultCertificate

def row21 : Certificate := (certificateFor? 0).getD defaultCertificate
def row59 : Certificate := (certificateFor? 37).getD defaultCertificate

def certificateBody (value : Certificate) : List Nat :=
  [value.sourceIndex, value.argument, value.floor, value.targetNumerator,
    value.targetDenominator, value.logLower, value.logUpper, value.logScale,
    value.baseScale]

def decodeCertificate? : List Nat → Option Certificate
  | [sourceIndex, argument, floor, targetNumerator, targetDenominator,
      logLower, logUpper, logScale, baseScale] =>
      some
        { sourceIndex, argument, floor, targetNumerator, targetDenominator,
          logLower, logUpper, logScale, baseScale }
  | _ => none

def tailCardinality (value : Certificate) : Nat := value.floor - 11

def upperSumNumerator (value : Certificate) : Nat :=
  value.baseScale ^ value.argument +
    PntBKLNWExp.bandPowerSum PntBKLNWExp.upperBaseNumerator value.argument 12 +
    tailCardinality value *
      PntBKLNWExp.upperBaseNumerator 13 ^ value.argument

def sumDenominator (value : Certificate) : Nat :=
  value.baseScale ^ value.argument

def Valid (value : Certificate) : Prop :=
  value.sourceIndex < 38 ∧
    sourceRecord? value.sourceIndex =
      some ⟨value.argument, value.floor, value.targetNumerator,
        value.targetDenominator⟩ ∧
    value.logLower = logLowerNumerator ∧
    value.logUpper = logUpperNumerator ∧
    value.logScale = logDenominator ∧
    value.baseScale = PntBKLNWExp.baseDenominator ∧
    12 ≤ value.floor ∧
    value.floor * value.logUpper ≤ value.argument * value.logScale ∧
    value.argument * value.logScale < (value.floor + 1) * value.logLower ∧
    0 < value.targetDenominator ∧
    PntBKLNWExp.alphaNumerator * upperSumNumerator value *
        value.targetDenominator ≤
      value.targetNumerator *
        (PntBKLNWExp.alphaDenominator * sumDenominator value)

instance (value : Certificate) : Decidable (Valid value) := by
  unfold Valid
  infer_instance

def validCertificate (value : Certificate) : Bool := decide (Valid value)

def arithmeticWork (value : Certificate) : Nat :=
  value.argument * 10

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }
def foldKey : OpKey := { name := "pnt-table10.a2-fold" }
def foldRuleKey : RuleKey := { name := "pnt-table10.checked-a2-fold" }
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
                  { arithmeticWork := arithmeticWork value
                    estimatedProofNodes := 64 }
              drafts :=
                [{ label := payload, role := .fact, schema := 1, body := cells }] }
        | _, _ => { outcome := .failed 1, drafts := [] }
      else { outcome := .failed 2, drafts := [] }
  | none => { outcome := .failed 3, drafts := [] }

def packageFor (value : Certificate) : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[foldOperation]
    handlers := #[Handler.statelessPlanned foldRule
      (planForBody (certificateBody value)) #[factFormat]] }

def packagesFor (value : Certificate) : Array (Package Bound) := #[packageFor value]

def engineLimitsFor (value : Certificate) : State.Limits :=
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
    maxEffort := arithmeticWork value
    maxObservationValue := arithmeticWork value
    maxDiagnosticValue := max 512 (arithmeticWork value)
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
    maxBodyCells := 9
    maxDrafts := 1
    maxDraftCells := 9
    maxAtom := 10 ^ 20
    maxSchema := 1
    maxUses := 1 }

def limitsFor (value : Certificate) : PolicySession.Limits :=
  { engine := engineLimitsFor value, policy := policyLimits, arena := arenaLimits }

def start (value : Certificate) :
    Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program (packagesFor value) #[.all]
    (limitsFor value)

end Hex.Interval.Experiment.PntTable10A2
