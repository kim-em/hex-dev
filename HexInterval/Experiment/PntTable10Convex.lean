/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntTable10Shard

@[expose] public section

/-!
# Source-pinned BKLNW Table 10 convex-row batch

This package checks the thirty coordinates in the six consecutive integer
rows `60, 65, 70, 75, 80, 85` of pinned PNT+ Table 10.  These rows share one
convex endpoint reduction.  Their exact row bounds, coefficients, endpoints,
listed cells, corrected targets, and row order are authenticated together.
-/

namespace Hex.Interval.Experiment.PntTable10Convex

open Propagator PayloadArena
open PntTable10Shard

structure RowCertificate where
  row : Nat
  nextRow : Nat
  a2 : Decimal
  epsilon : Decimal
  cell1 : Cell
  cell2 : Cell
  cell3 : Cell
  cell4 : Cell
  cell5 : Cell
  deriving DecidableEq, Repr

def a1 : Decimal := decimal 100000002 8
def halfBase : Decimal := decimal 606530660 9
def twoThirdBase : Decimal := decimal 513417120 9

def decimalPow (value : Decimal) (power : Nat) : Decimal :=
  decimal (value.mantissa ^ power) (value.scale * power)

def sourceCell (row column mantissa scale : Nat) : Cell :=
  { coordinate := { row, column }
    listed := decimal mantissa scale
    target := corrected (decimal mantissa scale) }

def rowCertificate (row nextRow a2Mantissa a2Scale epsilonMantissa epsilonScale : Nat)
    (cells : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    RowCertificate :=
  { row, nextRow
    a2 := decimal a2Mantissa a2Scale
    epsilon := decimal epsilonMantissa epsilonScale
    cell1 := sourceCell row 1 cells.1 cells.2.1
    cell2 := sourceCell row 2 cells.2.2.1 cells.2.2.2.1
    cell3 := sourceCell row 3 cells.2.2.2.2.1 cells.2.2.2.2.2.1
    cell4 := sourceCell row 4 cells.2.2.2.2.2.2.1 cells.2.2.2.2.2.2.2.1
    cell5 := sourceCell row 5 cells.2.2.2.2.2.2.2.2.1 cells.2.2.2.2.2.2.2.2.2 }

def row60 : RowCertificate :=
  rowCertificate 60 65 89 0 12216 15
    (79446, 14, 51640, 12, 33566, 10, 21818, 8, 14182, 6)

def row65 : RowCertificate :=
  rowCertificate 65 70 96 0 35713 16
    (25003, 14, 17502, 12, 12252, 10, 85761, 9, 60033, 7)

def row70 : RowCertificate :=
  rowCertificate 70 75 103 0 27924 16
    (20943, 14, 15707, 12, 11780, 10, 88353, 9, 66265, 7)

def row75 : RowCertificate :=
  rowCertificate 75 80 111 0 27037 16
    (21629, 14, 17303, 12, 13842, 10, 11074, 8, 88591, 7)

def row80 : RowCertificate :=
  rowCertificate 80 85 118 0 26109 16
    (22192, 14, 18863, 12, 16034, 10, 13629, 8, 11584, 6)

def row85 : RowCertificate :=
  rowCertificate 85 90 125 0 25693 16
    (23123, 14, 20811, 12, 18730, 10, 16857, 8, 15171, 6)

def rows : List RowCertificate := [row60, row65, row70, row75, row80, row85]

def RowCertificate.cells (value : RowCertificate) : List Cell :=
  [value.cell1, value.cell2, value.cell3, value.cell4, value.cell5]

def cells : List Cell := rows.flatMap RowCertificate.cells

def endpoint (value : RowCertificate) (cell : Cell) (point : Nat) : Decimal :=
  (Decimal.powNat point cell.coordinate.column).mul
    ((a1.mul (decimalPow halfBase point)).add
      ((value.a2.mul (decimalPow twoThirdBase point)).add value.epsilon))

def checkCell (value : RowCertificate) (cell : Cell) : Bool :=
  cell.coordinate.row == value.row &&
    decide (1 ≤ cell.coordinate.column ∧ cell.coordinate.column ≤ 5) &&
    cell.target.le (corrected cell.listed) &&
    (endpoint value cell value.row).le cell.target &&
    (endpoint value cell value.nextRow).le cell.target

def firstFailure? (values : List RowCertificate) : Option Nat :=
  values.findSome? fun value =>
    value.cells.findSome? fun cell =>
      if checkCell value cell then none else some (coordinateCode cell.coordinate)

def validRows (values : List RowCertificate) : Bool :=
  values == rows && values.all fun value => value.cells.all (checkCell value)

def encodeRow (value : RowCertificate) : List Nat :=
  [value.row, value.nextRow] ++ encodeDecimal value.a2 ++ encodeDecimal value.epsilon ++
    encodeCell value.cell1 ++ encodeCell value.cell2 ++ encodeCell value.cell3 ++
    encodeCell value.cell4 ++ encodeCell value.cell5

def decodeRow? : List Nat → Option (RowCertificate × List Nat)
  | row :: nextRow :: rest => do
      let (a2, rest) ← decodeDecimal? rest
      let (epsilon, rest) ← decodeDecimal? rest
      let (cell1, rest) ← decodeCell? rest
      let (cell2, rest) ← decodeCell? rest
      let (cell3, rest) ← decodeCell? rest
      let (cell4, rest) ← decodeCell? rest
      let (cell5, rest) ← decodeCell? rest
      some (⟨row, nextRow, a2, epsilon, cell1, cell2, cell3, cell4, cell5⟩, rest)
  | _ => none

def decodeRows? (body : List Nat) : Option (List RowCertificate) := do
  let (row1, rest) ← decodeRow? body
  let (row2, rest) ← decodeRow? rest
  let (row3, rest) ← decodeRow? rest
  let (row4, rest) ← decodeRow? rest
  let (row5, rest) ← decodeRow? rest
  let (row6, rest) ← decodeRow? rest
  if rest.isEmpty then some [row1, row2, row3, row4, row5, row6] else none

def body : List Nat := rows.flatMap encodeRow

def decodeBatch? (payload : List Nat) : Option Unit := do
  let decoded ← decodeRows? payload
  if validRows decoded then some () else none

def sourceKey : OpKey := { name := "pnt-table10-convex.source" }
def batchKey : OpKey := { name := "pnt-table10-convex.batch" }
def ruleKey : RuleKey := { name := "pnt-table10-convex.checked" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def batchOperation : Operation :=
  { key := batchKey, inputs := List.replicate 30 real, output := real }

def operations : Array Operation := #[sourceOperation, batchOperation]
def node (index : Nat) : NodeId := { index }
def cellNodes : List NodeId := (List.range 30).map node
def batchNode : NodeId := node 30
def payload : PayloadId := { index := 0 }

def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def batchInstruction : Node := { domain := real, op := { index := 1 }, args := cellNodes }
def program : Program :=
  { operations, nodes := (List.replicate 30 sourceInstruction ++ [batchInstruction]).toArray }

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
    writes := (List.range 30).map Slot.argument }

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun payload => (decodeBatch? payload).isSome }

def planForBody (payloadBody : List Nat) (request : RuleRequest Bound) : Plan Bound :=
  match decodeRows? payloadBody with
  | some values =>
      match firstFailure? values with
      | some coordinate => { outcome := .failed coordinate, drafts := [] }
      | none =>
          if validRows values then
            if request.inputs.isEmpty then
              if request.writes == cellNodes then
                { outcome := .success (candidates cellNodes (values.flatMap RowCertificate.cells)) []
                    { arithmeticWork := 60, estimatedProofNodes := 180 }
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
    maxNodes := 31
    maxRules := 1
    maxRegistryEntries := 32
    maxReplayFormats := 2
    maxArity := 30
    maxScopeNodes := 1
    maxApplications := 1
    maxQueueEntries := 64
    maxActions := 2
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 30
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 2048
    maxDiagnosticValue := 2048
    maxOutcomeCandidates := 30
    maxOutcomeSuggestions := 0
    maxProposalItems := 30
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit := { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 4, maxTraversal := 128, maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 30
    maxBodyCells := 216
    maxDrafts := 30
    maxDraftCells := 216
    maxAtom := 1002001 * 88591
    maxSchema := 1
    maxUses := 30 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound := Array.replicate 31 .all

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

end Hex.Interval.Experiment.PntTable10Convex
