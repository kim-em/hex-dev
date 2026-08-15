/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntTable10Shard

@[expose] public section

/-!
# Source-pinned BKLNW Table 10 pointwise-row batch

This package checks the ten coordinates in rows `90` and `95` of pinned
PNT+ Table 10.  These rows share the late-range pointwise reduction: the
upper row endpoint bounds the power, while the lower endpoint bounds both
decreasing exponential terms.  Exact coefficients, endpoints, listed cells,
corrected targets, and row order are authenticated together.
-/

namespace Hex.Interval.Experiment.PntTable10Pointwise

open Propagator PayloadArena
open PntTable10Shard

structure RowCertificate where
  row : Nat
  nextRow : Nat
  a1 : Decimal
  a2 : Decimal
  epsilon : Decimal
  cell1 : Cell
  cell2 : Cell
  cell3 : Cell
  cell4 : Cell
  cell5 : Cell
  deriving DecidableEq, Repr

def halfBase : Decimal := decimal 606530660 9
def twoThirdBase : Decimal := decimal 513417120 9

def decimalPow (value : Decimal) (power : Nat) : Decimal :=
  decimal (value.mantissa ^ power) (value.scale * power)

def sourceCell (row column mantissa scale : Nat) : Cell :=
  { coordinate := { row, column }
    listed := decimal mantissa scale
    target := corrected (decimal mantissa scale) }

def rowCertificate (row nextRow a1 a2 epsilonMantissa epsilonScale : Nat)
    (cells : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    RowCertificate :=
  { row, nextRow
    a1 := decimal a1 0
    a2 := decimal a2 0
    epsilon := decimal epsilonMantissa epsilonScale
    cell1 := sourceCell row 1 cells.1 cells.2.1
    cell2 := sourceCell row 2 cells.2.2.1 cells.2.2.2.1
    cell3 := sourceCell row 3 cells.2.2.2.2.1 cells.2.2.2.2.2.1
    cell4 := sourceCell row 4 cells.2.2.2.2.2.2.1 cells.2.2.2.2.2.2.2.1
    cell5 := sourceCell row 5 cells.2.2.2.2.2.2.2.2.1 cells.2.2.2.2.2.2.2.2.2 }

def row90 : RowCertificate :=
  rowCertificate 90 95 2 132 25214 16
    (23952, 14, 22755, 12, 21617, 10, 20536, 8, 19509, 6)

def row95 : RowCertificate :=
  rowCertificate 95 100 2 140 24920 16
    (24919, 14, 24919, 12, 24919, 10, 24919, 8, 24919, 6)

def rows : List RowCertificate := [row90, row95]

def RowCertificate.cells (value : RowCertificate) : List Cell :=
  [value.cell1, value.cell2, value.cell3, value.cell4, value.cell5]

def cells : List Cell := rows.flatMap RowCertificate.cells

/-- Exact-rational upper bound for the single pointwise premise used by the
pinned source.  The upper row endpoint bounds `y^k`; the lower endpoint is
used for both exponential powers. -/
def endpoint (value : RowCertificate) (cell : Cell) : Decimal :=
  (Decimal.powNat value.nextRow cell.coordinate.column).mul
    ((value.a1.mul (decimalPow halfBase value.row)).add
      ((value.a2.mul (decimalPow twoThirdBase value.row)).add value.epsilon))

def checkCell (value : RowCertificate) (cell : Cell) : Bool :=
  cell.coordinate.row == value.row &&
    decide (1 ≤ cell.coordinate.column ∧ cell.coordinate.column ≤ 5) &&
    cell.target.le (corrected cell.listed) &&
    (endpoint value cell).le cell.target

def firstFailure? (values : List RowCertificate) : Option Nat :=
  values.findSome? fun value =>
    value.cells.findSome? fun cell =>
      if checkCell value cell then none else some (coordinateCode cell.coordinate)

def validRows (values : List RowCertificate) : Bool :=
  values == rows && values.all fun value => value.cells.all (checkCell value)

def encodeRow (value : RowCertificate) : List Nat :=
  [value.row, value.nextRow] ++ encodeDecimal value.a1 ++ encodeDecimal value.a2 ++
    encodeDecimal value.epsilon ++ encodeCell value.cell1 ++ encodeCell value.cell2 ++
    encodeCell value.cell3 ++ encodeCell value.cell4 ++ encodeCell value.cell5

def decodeRow? : List Nat → Option (RowCertificate × List Nat)
  | row :: nextRow :: rest => do
      let (a1, rest) ← decodeDecimal? rest
      let (a2, rest) ← decodeDecimal? rest
      let (epsilon, rest) ← decodeDecimal? rest
      let (cell1, rest) ← decodeCell? rest
      let (cell2, rest) ← decodeCell? rest
      let (cell3, rest) ← decodeCell? rest
      let (cell4, rest) ← decodeCell? rest
      let (cell5, rest) ← decodeCell? rest
      some (⟨row, nextRow, a1, a2, epsilon, cell1, cell2, cell3, cell4, cell5⟩, rest)
  | _ => none

def decodeRows? (body : List Nat) : Option (List RowCertificate) := do
  let (row1, rest) ← decodeRow? body
  let (row2, rest) ← decodeRow? rest
  if rest.isEmpty then some [row1, row2] else none

def body : List Nat := rows.flatMap encodeRow

def decodeBatch? (payload : List Nat) : Option Unit := do
  let decoded ← decodeRows? payload
  if validRows decoded then some () else none

def sourceKey : OpKey := { name := "pnt-table10-pointwise.source" }
def batchKey : OpKey := { name := "pnt-table10-pointwise.batch" }
def ruleKey : RuleKey := { name := "pnt-table10-pointwise.checked" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def batchOperation : Operation :=
  { key := batchKey, inputs := List.replicate 10 real, output := real }

def operations : Array Operation := #[sourceOperation, batchOperation]
def node (index : Nat) : NodeId := { index }
def cellNodes : List NodeId := (List.range 10).map node
def batchNode : NodeId := node 10
def payload : PayloadId := { index := 0 }

def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def batchInstruction : Node := { domain := real, op := { index := 1 }, args := cellNodes }
def program : Program :=
  { operations, nodes := (List.replicate 10 sourceInstruction ++ [batchInstruction]).toArray }

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
    writes := (List.range 10).map Slot.argument }

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
                    { arithmeticWork := 30, estimatedProofNodes := 80 }
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
    maxNodes := 11
    maxRules := 1
    maxRegistryEntries := 12
    maxReplayFormats := 2
    maxArity := 10
    maxScopeNodes := 1
    maxApplications := 1
    maxQueueEntries := 24
    maxActions := 2
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 10
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 2048
    maxDiagnosticValue := 2048
    maxOutcomeCandidates := 10
    maxOutcomeSuggestions := 0
    maxProposalItems := 10
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit := { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 4, maxTraversal := 48, maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 10
    maxBodyCells := 76
    maxDrafts := 10
    maxDraftCells := 76
    maxAtom := 1002001 * 24919
    maxSchema := 1
    maxUses := 10 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound := Array.replicate 11 .all

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

end Hex.Interval.Experiment.PntTable10Pointwise
