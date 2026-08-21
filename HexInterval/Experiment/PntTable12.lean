/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Mathlib-free PNT+ Table 12 batch probe

This package is the executable half of a coordinate-aware acceptance probe for
the 130 numerical cells checked by PNT+'s `BKLNW.table_12_check`.  The current
bounded fixture covers the five columns of the ordinary row `b = 25` in one
provider action.  One authenticated row payload therefore shares the row
constants and four exponential point enclosures across all five cell facts.

The paper's original value at coordinate `(25, 5)` is represented by a
specific mutated payload.  Planning rejects it with that coordinate encoded in
the diagnostic; it is not treated as a request for more precision.
-/

namespace Hex.Interval.Experiment.PntTable12

open Propagator PayloadArena

/-- The five ordered upper cuts used by the row-25 fixture. -/
inductive Bound where
  | all
  | row25k1
  | row25k2
  | row25k3
  | row25k4
  | row25k5
  | empty
  deriving DecidableEq, Repr

namespace Bound

/-- Semantic intersection of the row-25 upper cuts.  The five rational cuts
are strictly ordered from `row25k1` (tightest) through `row25k5` (loosest), so
the intersection of two cuts is the one with the smaller column index. -/
def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .row25k1, _ | _, .row25k1 => .row25k1
  | .row25k2, _ | _, .row25k2 => .row25k2
  | .row25k3, _ | _, .row25k3 => .row25k3
  | .row25k4, _ | _, .row25k4 => .row25k4
  | .row25k5, .row25k5 => .row25k5

/-- Small exposed tag used by proof replay to authenticate the runtime result
without relying on a derived equality instance across a module boundary. -/
def code : Bound → Nat
  | .all => 0
  | .row25k1 => 1
  | .row25k2 => 2
  | .row25k3 => 3
  | .row25k4 => 4
  | .row25k5 => 5
  | .empty => 6

end Bound

/-- Source coordinates are stable diagnostics, independent of node indices. -/
structure Coordinate where
  row : Nat
  column : Nat
  deriving DecidableEq, Repr

def paperCell : Coordinate := { row := 25, column := 5 }

/-- Inject a coordinate into the engine's numeric diagnostic channel.  The
radix `8` makes this map injective whenever the column is strictly below `8`;
the current fixture uses columns `1` through `5`. -/
def coordinateCode (coordinate : Coordinate) : Nat :=
  coordinate.row * 8 + coordinate.column

/-- Recognize the one historical paper cell represented by this bounded
fixture.  This is deliberately not a decoder for the two logarithmic rows. -/
def paperCellForCode? (code : Nat) : Option Coordinate :=
  if code == coordinateCode paperCell then some paperCell else none

/-- Fixed row recipe.  The payload carries the nine source-tuple fields
(including the source-only `M`), `c₀`, four rational upper enclosures for
`exp (-1/2)`, `exp (-2/3)`, `exp (-3/4)`, and `exp (-4/5)`, and all five
tabulated upper bounds. -/
structure RowCertificate where
  row : Nat
  columns : Nat
  cNumerator : Nat
  cDenominator : Nat
  capitalNumerator : Nat
  capitalDenominator : Nat
  cZeroNumerator : Nat
  cZeroDenominator : Nat
  pointDenominator : Nat
  halfNumerator : Nat
  twoThirdsNumerator : Nat
  threeQuartersNumerator : Nat
  fourFifthsNumerator : Nat
  cell1Mantissa : Nat
  cell1Scale : Nat
  cell2Mantissa : Nat
  cell2Scale : Nat
  cell3Mantissa : Nat
  cell3Scale : Nat
  cell4Mantissa : Nat
  cell4Scale : Nat
  cell5Mantissa : Nat
  cell5Scale : Nat
  mMantissa : Nat
  mExponent : Nat
  deriving DecidableEq, Repr

def rowCertificate : RowCertificate :=
  { row := 25
    columns := 5
    cNumerator := 88
    cDenominator := 100
    capitalNumerator := 86
    capitalDenominator := 100
    cZeroNumerator := 103883
    cZeroDenominator := 100000
    pointDenominator := 1000000000
    halfNumerator := 606530660
    twoThirdsNumerator := 513417120
    threeQuartersNumerator := 472366553
    fourFifthsNumerator := 449328965
    cell1Mantissa := 1750020
    cell1Scale := 10
    cell2Mantissa := 4375050
    cell2Scale := 9
    cell3Mantissa := 1093770
    cell3Scale := 7
    cell4Mantissa := 2734410
    cell4Scale := 6
    cell5Mantissa := 6836010
    cell5Scale := 5
    mMantissa := 32
    mExponent := 12 }

def rowBody : List Nat :=
  [rowCertificate.row, rowCertificate.columns,
    rowCertificate.cNumerator, rowCertificate.cDenominator,
    rowCertificate.capitalNumerator, rowCertificate.capitalDenominator,
    rowCertificate.cZeroNumerator, rowCertificate.cZeroDenominator,
    rowCertificate.pointDenominator, rowCertificate.halfNumerator,
    rowCertificate.twoThirdsNumerator, rowCertificate.threeQuartersNumerator,
    rowCertificate.fourFifthsNumerator,
    rowCertificate.cell1Mantissa, rowCertificate.cell1Scale,
    rowCertificate.cell2Mantissa, rowCertificate.cell2Scale,
    rowCertificate.cell3Mantissa, rowCertificate.cell3Scale,
    rowCertificate.cell4Mantissa, rowCertificate.cell4Scale,
    rowCertificate.cell5Mantissa, rowCertificate.cell5Scale,
    rowCertificate.mMantissa, rowCertificate.mExponent]

/-- The exact paper mutation changes only the fifth tabulated mantissa from
`68.36010` to `66.5350`; the remaining row recipe stays authenticated. -/
def paperBody : List Nat :=
  [25, 5, 88, 100, 86, 100, 103883, 100000, 1000000000,
    606530660, 513417120, 472366553, 449328965,
    1750020, 10, 4375050, 9, 1093770, 7, 2734410, 6, 6653500, 5,
    32, 12]

def decodeCertificate? : List Nat → Option RowCertificate
  | [25, 5, 88, 100, 86, 100, 103883, 100000, 1000000000,
      606530660, 513417120, 472366553, 449328965,
      1750020, 10, 4375050, 9, 1093770, 7, 2734410, 6, 6836010, 5,
      32, 12] =>
      some rowCertificate
  | _ => none

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "pnt-table12.source" }
def rowKey : OpKey := { name := "pnt-table12.row" }
def batchRuleKey : RuleKey := { name := "pnt-table12.checked-row" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def rowOperation : Operation :=
  { key := rowKey
    inputs := [real, real, real, real, real]
    output := real }

def operations : Array Operation := #[sourceOperation, rowOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }

def rowInstruction : Node :=
  { domain := real
    op := { index := 1 }
    args := [node 0, node 1, node 2, node 3, node 4] }

/-- Five cell nodes are arguments to one row anchor, allowing one rule action
to emit the five-coordinate batch.  The anchor's result is only a row token;
the payload and its proof theorem, not a separate sum node, share the numerical
row computation. -/
def program : Program :=
  { operations
    nodes := #[sourceInstruction, sourceInstruction, sourceInstruction,
      sourceInstruction, sourceInstruction, rowInstruction] }

def batchRule : Registration :=
  { key := batchRuleKey
    head := rowKey
    kind := .forward
    watches := []
    writes := [.argument 0, .argument 1, .argument 2, .argument 3, .argument 4] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body => decodeCertificate? body == some rowCertificate }

def correctCandidates (writes : List NodeId) : Option (List (Candidate Bound)) :=
  match writes with
  | [cell1, cell2, cell3, cell4, cell5] =>
      some
        [{ node := cell1, fact := .row25k1, payload := payload 0 },
          { node := cell2, fact := .row25k2, payload := payload 0 },
          { node := cell3, fact := .row25k3, payload := payload 0 },
          { node := cell4, fact := .row25k4, payload := payload 0 },
          { node := cell5, fact := .row25k5, payload := payload 0 }]
  | _ => none

/-- Plan one authenticated row batch.  The known false paper cell gets a
coordinate diagnostic; malformed payloads get the generic diagnostic `1`.
Neither case is a retry or precision escalation. -/
def planForBody (body : List Nat) (request : RuleRequest Bound) : Plan Bound :=
  if body == paperBody then
    { outcome := .failed (coordinateCode paperCell), drafts := [] }
  else
    match decodeCertificate? body, request.inputs, correctCandidates request.writes with
    | some _, [], some candidates =>
        { outcome :=
            .success candidates []
              { arithmeticWork := 9, estimatedProofNodes := 18 }
          drafts :=
            [{ label := payload 0, role := .fact, schema := 1, body }] }
    | _, _, _ => { outcome := .failed 1, drafts := [] }

def batchPlan : RuleRequest Bound → Plan Bound :=
  planForBody rowBody

def sourcePackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation]
    handlers := #[] }

def rowPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[rowOperation]
    handlers := #[Handler.statelessPlanned batchRule batchPlan #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, rowPackage]

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 2
    maxNodes := 6
    maxRules := 1
    maxRegistryEntries := 8
    maxReplayFormats := 2
    maxArity := 5
    maxScopeNodes := 1
    maxApplications := 1
    maxQueueEntries := 8
    maxActions := 2
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 5
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 32
    maxDiagnosticValue := 256
    maxOutcomeCandidates := 5
    maxOutcomeSuggestions := 0
    maxProposalItems := 5
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 4
    maxTraversal := 16
    maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 5
    maxBodyCells := 32
    maxDrafts := 5
    maxDraftCells := 32
    maxAtom := 1000000000
    maxSchema := 1
    maxUses := 8 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages
    #[.all, .all, .all, .all, .all, .all] limits

end Hex.Interval.Experiment.PntTable12
