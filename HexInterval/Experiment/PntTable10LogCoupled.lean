/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PntTable10Shard

@[expose] public section

/-!
# Source-pinned BKLNW Table 10 logarithmic transition

This bounded package authenticates the ten numeric coordinates on the two
consecutive pinned Table 10 rows `43` and `19 * log 10`.  A shared rational
certificate records the exponential bases, the upper approximation to the
logarithmic endpoint, and both exponential-tail bounds.  The two rows and
their chronology are authenticated as one payload.
-/

namespace Hex.Interval.Experiment.PntTable10LogCoupled

open Propagator PayloadArena
open PntTable10Shard

def logRowCode : Nat := 19010

structure RowCertificate where
  rowCode : Nat
  a1 : Decimal
  a2 : Decimal
  epsilon : Decimal
  cell1 : Cell
  cell2 : Cell
  cell3 : Cell
  cell4 : Cell
  cell5 : Cell
  deriving DecidableEq, Repr

structure Certificate where
  halfBase : Decimal
  twoThirdBase : Decimal
  logUpper : Decimal
  halfTail : Decimal
  twoThirdTail : Decimal
  row43 : RowCertificate
  rowLog : RowCertificate
  deriving DecidableEq, Repr

def decimalPow (value : Decimal) (power : Nat) : Decimal :=
  decimal (value.mantissa ^ power) (value.scale * power)

def sourceCell (row column mantissa scale : Nat) : Cell :=
  { coordinate := { row, column }
    listed := decimal mantissa scale
    target := corrected (decimal mantissa scale) }

def rowCertificate (rowCode a2Mantissa a2Scale : Nat)
    (cells : Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat × Nat) :
    RowCertificate :=
  { rowCode
    a1 := decimal 100000002 8
    a2 := decimal a2Mantissa a2Scale
    epsilon := decimal 19339 12
    cell1 := sourceCell rowCode 1 cells.1 cells.2.1
    cell2 := sourceCell rowCode 2 cells.2.2.1 cells.2.2.2.1
    cell3 := sourceCell rowCode 3 cells.2.2.2.2.1 cells.2.2.2.2.2.1
    cell4 := sourceCell rowCode 4 cells.2.2.2.2.2.2.1 cells.2.2.2.2.2.2.2.1
    cell5 := sourceCell rowCode 5 cells.2.2.2.2.2.2.2.2.1
      cells.2.2.2.2.2.2.2.2.2 }

def row43 : RowCertificate :=
  rowCertificate 43 1054 3
    (85986, 11, 37618, 9, 16458, 7, 72000, 6, 31500, 4)

def rowLog : RowCertificate :=
  rowCertificate logRowCode 66 0
    (86315, 11, 37978, 9, 16711, 7, 73526, 6, 32352, 4)

def certificate : Certificate :=
  { halfBase := decimal 606530660 9
    twoThirdBase := decimal 513417120 9
    logUpper := decimal 4375 2
    halfTail := decimal 317 12
    twoThirdTail := decimal 216 15
    row43, rowLog }

def RowCertificate.cells (value : RowCertificate) : List Cell :=
  [value.cell1, value.cell2, value.cell3, value.cell4, value.cell5]

def rows (value : Certificate) : List RowCertificate := [value.row43, value.rowLog]
def cells (value : Certificate) : List Cell := (rows value).flatMap RowCertificate.cells

def integerEndpoint (value : Certificate) (row : RowCertificate) (cell : Cell)
    (point : Nat) : Decimal :=
  (Decimal.powNat point cell.coordinate.column).mul
    ((row.a1.mul (decimalPow value.halfBase point)).add
      ((row.a2.mul (decimalPow value.twoThirdBase point)).add row.epsilon))

def logEndpoint (value : Certificate) (row : RowCertificate) (cell : Cell) : Decimal :=
  (decimalPow value.logUpper cell.coordinate.column).mul
    ((row.a1.mul value.halfTail).add
      ((row.a2.mul value.twoThirdTail).add row.epsilon))

def leftEndpoint (value : Certificate) (row : RowCertificate) (cell : Cell) : Decimal :=
  if row.rowCode == 43 then integerEndpoint value row cell 43
  else logEndpoint value row cell

def rightEndpoint (value : Certificate) (row : RowCertificate) (cell : Cell) : Decimal :=
  if row.rowCode == 43 then logEndpoint value row cell
  else integerEndpoint value row cell 44

def checkCell (value : Certificate) (row : RowCertificate) (cell : Cell) : Bool :=
  cell.coordinate.row == row.rowCode &&
    decide (1 ≤ cell.coordinate.column ∧ cell.coordinate.column ≤ 5) &&
    cell.target.le (corrected cell.listed) &&
    (leftEndpoint value row cell).le cell.target &&
    (rightEndpoint value row cell).le cell.target

def firstFailure? (value : Certificate) : Option Nat :=
  (rows value).findSome? fun row =>
    row.cells.findSome? fun cell =>
      if checkCell value row cell then none else some (coordinateCode cell.coordinate)

def validCertificate (value : Certificate) : Bool :=
  value == certificate && (rows value).all fun row => row.cells.all (checkCell value row)

def encodeRow (value : RowCertificate) : List Nat :=
  [value.rowCode] ++ encodeDecimal value.a1 ++ encodeDecimal value.a2 ++
    encodeDecimal value.epsilon ++ encodeCell value.cell1 ++ encodeCell value.cell2 ++
    encodeCell value.cell3 ++ encodeCell value.cell4 ++ encodeCell value.cell5

def decodeRow? : List Nat → Option (RowCertificate × List Nat)
  | rowCode :: rest => do
      let (a1, rest) ← decodeDecimal? rest
      let (a2, rest) ← decodeDecimal? rest
      let (epsilon, rest) ← decodeDecimal? rest
      let (cell1, rest) ← decodeCell? rest
      let (cell2, rest) ← decodeCell? rest
      let (cell3, rest) ← decodeCell? rest
      let (cell4, rest) ← decodeCell? rest
      let (cell5, rest) ← decodeCell? rest
      some (⟨rowCode, a1, a2, epsilon, cell1, cell2, cell3, cell4, cell5⟩, rest)
  | _ => none

def encodeCertificate (value : Certificate) : List Nat :=
  encodeDecimal value.halfBase ++ encodeDecimal value.twoThirdBase ++
    encodeDecimal value.logUpper ++ encodeDecimal value.halfTail ++
    encodeDecimal value.twoThirdTail ++ encodeRow value.row43 ++ encodeRow value.rowLog

def decodeCertificate? (body : List Nat) : Option Certificate := do
  let (halfBase, rest) ← decodeDecimal? body
  let (twoThirdBase, rest) ← decodeDecimal? rest
  let (logUpper, rest) ← decodeDecimal? rest
  let (halfTail, rest) ← decodeDecimal? rest
  let (twoThirdTail, rest) ← decodeDecimal? rest
  let (row43, rest) ← decodeRow? rest
  let (rowLog, rest) ← decodeRow? rest
  if rest.isEmpty then
    some { halfBase, twoThirdBase, logUpper, halfTail, twoThirdTail, row43, rowLog }
  else none

def body : List Nat := encodeCertificate certificate

def decodeBatch? (payload : List Nat) : Option Unit := do
  let decoded ← decodeCertificate? payload
  if validCertificate decoded then some () else none

def sourceKey : OpKey := { name := "pnt-table10-log-coupled.source" }
def batchKey : OpKey := { name := "pnt-table10-log-coupled.batch" }
def ruleKey : RuleKey := { name := "pnt-table10-log-coupled.checked" }

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

def expectedCandidates : List (Candidate Bound) := candidates cellNodes (cells certificate)

def batchRule : Registration :=
  { key := ruleKey
    head := batchKey
    kind := .forward
    watches := []
    writes := (List.range 10).map Slot.argument }

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
                { outcome := .success (candidates cellNodes (cells value)) []
                    { arithmeticWork := 20, estimatedProofNodes := 60 }
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
    maxObservationValue := 20000
    maxDiagnosticValue := 20000
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
    maxBodyCells := 96
    maxDrafts := 10
    maxDraftCells := 96
    maxAtom := 1002001 * 86315
    maxSchema := 1
    maxUses := 10 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound := Array.replicate 11 .all

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

end Hex.Interval.Experiment.PntTable10LogCoupled
