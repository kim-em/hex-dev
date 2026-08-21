/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Mathlib-free PNT+ BKLNW exponential-sum certificates

The pinned BKLNW interface asks for two-sided bounds on
`(1+alpha) * f (exp b)` at eleven integer arguments.  One checked schema
authenticates the source row, the exact finite-sum split, a package-owned
two-sided table for `exp (1/k - 1/3)`, and both rational output cuts.
-/

namespace Hex.Interval.Experiment.PntBKLNWExp

open Propagator PayloadArena

inductive Bound where
  | all
  | window
  | empty
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .window, .window => .window

end Bound

structure SourceRecord where
  argument : Nat
  floor : Nat
  lowerNumerator : Nat
  upperNumerator : Nat
  targetDenominator : Nat
  deriving DecidableEq, Repr

def sourceRecord? : Nat → Option SourceRecord
  | 0 => some ⟨20, 28, 14262, 14263, 10000⟩
  | 1 => some ⟨25, 36, 12195, 12196, 10000⟩
  | 2 => some ⟨30, 43, 11210, 11211, 10000⟩
  | 3 => some ⟨35, 50, 107086, 107087, 100000⟩
  | 4 => some ⟨40, 57, 104319, 104320, 100000⟩
  | 5 => some ⟨43, 62, 103252, 103253, 100000⟩
  | 6 => some ⟨100, 144, 10002420, 10002421, 10000000⟩
  | 7 => some ⟨150, 216, 1000003748, 1000003758, 1000000000⟩
  | 8 => some ⟨200, 288, 100000007713, 100000007813, 100000000000⟩
  | 9 => some ⟨250, 360, 100000002025, 100000002125, 100000000000⟩
  | 10 => some ⟨300, 432, 100000001937, 100000002037, 100000000000⟩
  | _ => none

structure Certificate where
  sourceIndex : Nat
  argument : Nat
  floor : Nat
  exactStop : Nat
  tailStart : Nat
  tailCardinality : Nat
  baseDenominator : Nat
  lowerNumerator : Nat
  upperNumerator : Nat
  targetDenominator : Nat
  deriving DecidableEq, Repr

def baseDenominator : Nat := 1000000000000

def lowerBaseNumerator : Nat → Nat
  | 4 => 920044414629
  | 5 => 875173319042
  | 6 => 846481724890
  | 7 => 826565437624
  | 8 => 811936346150
  | 9 => 800737402916
  | 10 => 791889566336
  | 11 => 784723194053
  | 12 => 778800783071
  | 13 => 773824437226
  | 14 => 769584313961
  | 15 => 765928338364
  | 16 => 762743609746
  | 17 => 759944553775
  | 18 => 757465128396
  | 19 => 755253552953
  | 20 => 753268656454
  | 21 => 751477293075
  | 22 => 749852477940
  | 23 => 748372019432
  | 24 => 747017500310
  | 25 => 745773508091
  | 26 => 744627046352
  | 27 => 743567079205
  | 28 => 742584175080
  | 29 => 741670225442
  | 30 => 740818220681
  | 31 => 740022070064
  | 32 => 739276455951
  | 33 => 738576714918
  | 34 => 737918740160
  | 35 => 737298900852
  | 36 => 736713975138
  | 37 => 736161094132
  | 38 => 735637694869
  | 39 => 735141480591
  | 40 => 734670387060
  | 41 => 734222553860
  | 42 => 733796299850
  | 43 => 733390102074
  | 44 => 733002577591
  | 45 => 732632467739
  | 46 => 732278624487
  | 47 => 731939998539
  | 48 => 731615628946
  | 49 => 731304633997
  | 50 => 731006203218
  | 51 => 730719590321
  | 52 => 730444106973
  | 53 => 730179117276
  | 54 => 729924032871
  | 55 => 729678308573
  | 56 => 729441438486
  | 57 => 729212952525
  | 58 => 728992413300
  | 59 => 728779413327
  | 60 => 728573572511
  | 61 => 728374535885
  | 62 => 728181971568
  | 63 => 727995568914
  | 64 => 727815036845
  | _ => 0

def upperBaseNumerator : Nat → Nat
  | 4 => 920044414630
  | 5 => 875173319043
  | 6 => 846481724891
  | 7 => 826565437625
  | 8 => 811936346151
  | 9 => 800737402917
  | 10 => 791889566337
  | 11 => 784723194054
  | 12 => 778800783072
  | 13 => 773824437227
  | 14 => 769584313962
  | 15 => 765928338365
  | 16 => 762743609747
  | 17 => 759944553776
  | 18 => 757465128397
  | 19 => 755253552954
  | 20 => 753268656455
  | 21 => 751477293076
  | 22 => 749852477941
  | 23 => 748372019433
  | 24 => 747017500311
  | 25 => 745773508092
  | 26 => 744627046353
  | 27 => 743567079206
  | 28 => 742584175081
  | 29 => 741670225443
  | 30 => 740818220682
  | 31 => 740022070065
  | 32 => 739276455952
  | 33 => 738576714919
  | 34 => 737918740161
  | 35 => 737298900853
  | 36 => 736713975139
  | 37 => 736161094133
  | 38 => 735637694870
  | 39 => 735141480592
  | 40 => 734670387061
  | 41 => 734222553861
  | 42 => 733796299851
  | 43 => 733390102075
  | 44 => 733002577592
  | 45 => 732632467740
  | 46 => 732278624488
  | 47 => 731939998540
  | 48 => 731615628947
  | 49 => 731304633998
  | 50 => 731006203219
  | 51 => 730719590322
  | 52 => 730444106974
  | 53 => 730179117277
  | 54 => 729924032872
  | 55 => 729678308574
  | 56 => 729441438487
  | 57 => 729212952526
  | 58 => 728992413301
  | 59 => 728779413328
  | 60 => 728573572512
  | 61 => 728374535886
  | 62 => 728181971569
  | 63 => 727995568915
  | 64 => 727815036846
  | _ => 0

/-- Sum the table powers with indices `4..stop`. -/
def bandPowerSum (numerator : Nat → Nat) (exponent : Nat) : Nat → Nat
  | 0 => 0
  | stop + 1 =>
      if 4 ≤ stop + 1 then
        bandPowerSum numerator exponent stop + numerator (stop + 1) ^ exponent
      else
        0

def lowerSumNumerator (value : Certificate) : Nat :=
  value.baseDenominator ^ value.argument +
    bandPowerSum lowerBaseNumerator value.argument value.exactStop

def upperSumNumerator (value : Certificate) : Nat :=
  value.baseDenominator ^ value.argument +
    bandPowerSum upperBaseNumerator value.argument value.exactStop +
    value.tailCardinality *
      upperBaseNumerator value.tailStart ^ value.argument

def sumDenominator (value : Certificate) : Nat :=
  value.baseDenominator ^ value.argument

def certificateFor? (sourceIndex : Nat) : Option Certificate := do
  let source ← sourceRecord? sourceIndex
  let exactStop := min source.floor 63
  some
    { sourceIndex
      argument := source.argument
      floor := source.floor
      exactStop
      tailStart := exactStop + 1
      tailCardinality := source.floor - exactStop
      baseDenominator
      lowerNumerator := source.lowerNumerator
      upperNumerator := source.upperNumerator
      targetDenominator := source.targetDenominator }

def defaultCertificate : Certificate := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩

def certificates : List Certificate :=
  (List.range 11).map fun index =>
    (certificateFor? index).getD defaultCertificate

def exp20 : Certificate := (certificateFor? 0).getD defaultCertificate
def exp25 : Certificate := (certificateFor? 1).getD defaultCertificate
def exp30 : Certificate := (certificateFor? 2).getD defaultCertificate
def exp35 : Certificate := (certificateFor? 3).getD defaultCertificate
def exp40 : Certificate := (certificateFor? 4).getD defaultCertificate
def exp43 : Certificate := (certificateFor? 5).getD defaultCertificate
def exp100 : Certificate := (certificateFor? 6).getD defaultCertificate
def exp150 : Certificate := (certificateFor? 7).getD defaultCertificate
def exp200 : Certificate := (certificateFor? 8).getD defaultCertificate
def exp250 : Certificate := (certificateFor? 9).getD defaultCertificate
def exp300 : Certificate := (certificateFor? 10).getD defaultCertificate

def certificateBody (value : Certificate) : List Nat :=
  [value.sourceIndex, value.argument, value.floor, value.exactStop,
    value.tailStart, value.tailCardinality, value.baseDenominator,
    value.lowerNumerator, value.upperNumerator, value.targetDenominator]

def decodeCertificate? : List Nat → Option Certificate
  | [sourceIndex, argument, floor, exactStop, tailStart, tailCardinality,
      denominator, lowerNumerator, upperNumerator, targetDenominator] =>
      some
        { sourceIndex, argument, floor, exactStop, tailStart, tailCardinality,
          baseDenominator := denominator, lowerNumerator, upperNumerator,
          targetDenominator }
  | _ => none

def alphaNumerator : Nat := 10 ^ 16 + 193571378
def alphaDenominator : Nat := 10 ^ 16

def Valid (value : Certificate) : Prop :=
  value.sourceIndex ≤ 10 ∧
    sourceRecord? value.sourceIndex =
      some ⟨value.argument, value.floor, value.lowerNumerator,
        value.upperNumerator, value.targetDenominator⟩ ∧
    value.exactStop = min value.floor 63 ∧
    value.tailStart = value.exactStop + 1 ∧
    value.tailCardinality + value.exactStop = value.floor ∧
    value.baseDenominator = baseDenominator ∧
    0 < value.targetDenominator ∧
    value.lowerNumerator * (alphaDenominator * sumDenominator value) ≤
      alphaNumerator * lowerSumNumerator value * value.targetDenominator ∧
    alphaNumerator * upperSumNumerator value * value.targetDenominator ≤
      value.upperNumerator * (alphaDenominator * sumDenominator value)

instance (value : Certificate) : Decidable (Valid value) := by
  unfold Valid
  infer_instance

def validCertificate (value : Certificate) : Bool := decide (Valid value)

/-- Retained work account: one power per explicit lower and upper table cell,
plus the high-row tail base. This is a bounded-fixture charge, not a big-integer
bit-complexity model. -/
def arithmeticWork (value : Certificate) : Nat :=
  value.argument *
    (2 * (value.exactStop - 3) + if value.tailCardinality = 0 then 0 else 1)

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }
def foldKey : OpKey := { name := "pnt-bklnw.exp-fold" }
def foldRuleKey : RuleKey := { name := "pnt-bklnw.checked-exp-fold" }
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
                .success [{ node := target, fact := .window, payload }] []
                  { arithmeticWork := arithmeticWork value
                    estimatedProofNodes := 48 }
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
    maxDiagnosticValue := arithmeticWork value
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
    maxBodyCells := 10
    maxDrafts := 1
    maxDraftCells := 10
    maxAtom := 1000000000000
    maxSchema := 1
    maxUses := 1 }

def limitsFor (value : Certificate) : PolicySession.Limits :=
  { engine := engineLimitsFor value, policy := policyLimits, arena := arenaLimits }

def start (value : Certificate) :
    Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program (packagesFor value) #[.all]
    (limitsFor value)

end Hex.Interval.Experiment.PntBKLNWExp
