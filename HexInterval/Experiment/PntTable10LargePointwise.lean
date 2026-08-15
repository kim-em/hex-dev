/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntTable10Shard

@[expose] public section

/-!
# Source-pinned BKLNW Table 10 large-decimal pointwise row

This package checks all five coordinates in pinned source row `13800.7464`.
The late-range pointwise reduction needs only one shared exponential tail,
the integer upper endpoint, and the exact row coefficients.
-/

namespace Hex.Interval.Experiment.PntTable10LargePointwise

open Propagator PayloadArena
open PntTable10Shard

structure RowCertificate where
  row : Decimal
  nextRow : Nat
  a1 : Decimal
  a2 : Decimal
  epsilon : Decimal
  tail : Decimal
  cell1 : Cell
  cell2 : Cell
  cell3 : Cell
  cell4 : Cell
  cell5 : Cell
  deriving DecidableEq, Repr

/-- Fixed-point tag for the exact source row `13800.7464`. -/
def rowCode : Nat := 138007464

def sourceCell (column mantissa scale : Nat) : Cell :=
  { coordinate := { row := rowCode, column }
    listed := decimal mantissa scale
    target := corrected (decimal mantissa scale) }

def certificate : RowCertificate :=
  { row := decimal 138007464 4
    nextRow := 14000
    a1 := decimal 2 0
    a2 := decimal 19913 0
    epsilon := decimal 25423 39
    tail := decimal 1 100
    cell1 := sourceCell 1 35592 35
    cell2 := sourceCell 2 49829 31
    cell3 := sourceCell 3 69761 27
    cell4 := sourceCell 4 97665 23
    cell5 := sourceCell 5 13673 18 }

def RowCertificate.cells (value : RowCertificate) : List Cell :=
  [value.cell1, value.cell2, value.cell3, value.cell4, value.cell5]

def cells : List Cell := certificate.cells

def endpoint (value : RowCertificate) (cell : Cell) : Decimal :=
  (Decimal.powNat value.nextRow cell.coordinate.column).mul
    ((value.a1.mul value.tail).add ((value.a2.mul value.tail).add value.epsilon))

def checkCell (value : RowCertificate) (cell : Cell) : Bool :=
  cell.coordinate.row == rowCode &&
    decide (1 ≤ cell.coordinate.column ∧ cell.coordinate.column ≤ 5) &&
    cell.target.le (corrected cell.listed) &&
    (endpoint value cell).le cell.target

def failureCode (cell : Cell) : Nat := 800 + cell.coordinate.column

def firstFailure? (value : RowCertificate) : Option Nat :=
  value.cells.findSome? fun cell =>
    if checkCell value cell then none else some (failureCode cell)

def validCertificate (value : RowCertificate) : Bool :=
  value == certificate && value.cells.all (checkCell value)

def encodeCertificate (value : RowCertificate) : List Nat :=
  encodeDecimal value.row ++ [value.nextRow] ++ encodeDecimal value.a1 ++
    encodeDecimal value.a2 ++ encodeDecimal value.epsilon ++ encodeDecimal value.tail ++
    encodeCell value.cell1 ++ encodeCell value.cell2 ++ encodeCell value.cell3 ++
    encodeCell value.cell4 ++ encodeCell value.cell5

def decodeCertificate? (body : List Nat) : Option RowCertificate := do
  let (row, rest) ← decodeDecimal? body
  let nextRow :: rest := rest | none
  let (a1, rest) ← decodeDecimal? rest
  let (a2, rest) ← decodeDecimal? rest
  let (epsilon, rest) ← decodeDecimal? rest
  let (tail, rest) ← decodeDecimal? rest
  let (cell1, rest) ← decodeCell? rest
  let (cell2, rest) ← decodeCell? rest
  let (cell3, rest) ← decodeCell? rest
  let (cell4, rest) ← decodeCell? rest
  let (cell5, rest) ← decodeCell? rest
  if rest.isEmpty then
    some ⟨row, nextRow, a1, a2, epsilon, tail, cell1, cell2, cell3, cell4, cell5⟩
  else none

def body : List Nat := encodeCertificate certificate

def decodeBatch? (payload : List Nat) : Option Unit := do
  let decoded ← decodeCertificate? payload
  if validCertificate decoded then some () else none

def sourceKey : OpKey := { name := "pnt-table10-large-pointwise.source" }
def batchKey : OpKey := { name := "pnt-table10-large-pointwise.batch" }
def ruleKey : RuleKey := { name := "pnt-table10-large-pointwise.checked" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def batchOperation : Operation :=
  { key := batchKey, inputs := List.replicate 5 real, output := real }

def operations : Array Operation := #[sourceOperation, batchOperation]
def node (index : Nat) : NodeId := { index }
def cellNodes : List NodeId := (List.range 5).map node
def batchNode : NodeId := node 5
def payload : PayloadId := { index := 0 }

def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def batchInstruction : Node := { domain := real, op := { index := 1 }, args := cellNodes }
def program : Program :=
  { operations, nodes := (List.replicate 5 sourceInstruction ++ [batchInstruction]).toArray }

def candidates : List NodeId → List Cell → List (Candidate Bound)
  | target :: targets, cell :: remaining =>
      { node := target, fact := .upper cell, payload } :: candidates targets remaining
  | _, _ => []

def expectedCandidates : List (Candidate Bound) := candidates cellNodes cells

def batchRule : Registration :=
  { key := ruleKey
    head := batchKey
    kind := .forward
    watches := []
    writes := (List.range 5).map Slot.argument }

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun payload => (decodeBatch? payload).isSome }

def planForBody (payloadBody : List Nat) (request : RuleRequest Bound) : Plan Bound :=
  match decodeCertificate? payloadBody with
  | some value =>
      match firstFailure? value with
      | some coordinate => { outcome := .failed coordinate, drafts := [] }
      | none =>
          if validCertificate value then
            if request.inputs.isEmpty then
              if request.writes == cellNodes then
                { outcome := .success (candidates cellNodes value.cells) []
                    { arithmeticWork := 15, estimatedProofNodes := 45 }
                  drafts := [{ label := payload, role := .fact, schema := 1, body := payloadBody }] }
              else { outcome := .failed 2, drafts := [] }
            else { outcome := .failed 3, drafts := [] }
          else { outcome := .failed 1, drafts := [] }
  | none => { outcome := .failed 1, drafts := [] }

def batchPlan : RuleRequest Bound → Plan Bound := planForBody body

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }

def batchPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[batchOperation]
    handlers := #[Handler.statelessPlanned batchRule batchPlan #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, batchPackage]

def engineLimits : Propagator.Limits :=
  { maxOperations := 2
    maxNodes := 6
    maxRules := 1
    maxRegistryEntries := 8
    maxReplayFormats := 2
    maxArity := 5
    maxScopeNodes := 1
    maxApplications := 1
    maxQueueEntries := 16
    maxActions := 2
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 5
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 2048
    maxDiagnosticValue := 2048
    maxOutcomeCandidates := 5
    maxOutcomeSuggestions := 0
    maxProposalItems := 5
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit := { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 4, maxTraversal := 24, maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 5
    maxBodyCells := 41
    maxDrafts := 5
    maxDraftCells := 41
    maxAtom := 1002001 * 97665
    maxSchema := 1
    maxUses := 5 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound := Array.replicate 6 .all

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

end Hex.Interval.Experiment.PntTable10LargePointwise
