/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Source-pinned BKLNW Table 10 row shard

This bounded package checks all five coordinates of the pinned Table 10 row
`b = 25`.  The payload authenticates the row and next-row coordinates, the
three coefficient bounds, four exponential endpoint windows, the five printed
table cells, and their safety-margined targets.  A malformed coordinate or a
numerically false target fails before any payload is retained.
-/

namespace Hex.Interval.Experiment.PntTable10Shard

open Propagator PayloadArena

/-- A nonnegative decimal represented exactly as `mantissa / 10^scale`. -/
structure Decimal where
  mantissa : Nat
  scale : Nat
  deriving DecidableEq, Repr

def decimal (mantissa scale : Nat) : Decimal := { mantissa, scale }

def Decimal.mul (left right : Decimal) : Decimal :=
  decimal (left.mantissa * right.mantissa) (left.scale + right.scale)

def Decimal.add (left right : Decimal) : Decimal :=
  decimal
    (left.mantissa * 10 ^ right.scale + right.mantissa * 10 ^ left.scale)
    (left.scale + right.scale)

def Decimal.powNat (base : Nat) (power : Nat) : Decimal :=
  decimal (base ^ power) 0

def Decimal.le (left right : Decimal) : Bool :=
  decide (left.mantissa * 10 ^ right.scale ≤
    right.mantissa * 10 ^ left.scale)

structure Coordinate where
  row : Nat
  column : Nat
  deriving DecidableEq, Repr

def coordinateCode (coordinate : Coordinate) : Nat :=
  coordinate.row * 8 + coordinate.column

structure Cell where
  coordinate : Coordinate
  listed : Decimal
  target : Decimal
  deriving DecidableEq, Repr

structure Certificate where
  row : Nat
  nextRow : Nat
  a1 : Decimal
  a2 : Decimal
  epsilon : Decimal
  halfLeft : Decimal
  twoThirdLeft : Decimal
  halfRight : Decimal
  twoThirdRight : Decimal
  cell1 : Cell
  cell2 : Cell
  cell3 : Cell
  cell4 : Cell
  cell5 : Cell
  deriving DecidableEq, Repr

def margin : Decimal := decimal 1002001 6

def corrected (listed : Decimal) : Decimal := listed.mul margin

def sourceCell (column mantissa scale : Nat) : Cell :=
  { coordinate := { row := 25, column }
    listed := decimal mantissa scale
    target := corrected (decimal mantissa scale) }

def certificate : Certificate :=
  { row := 25
    nextRow := 26
    a1 := decimal 100000002 8
    a2 := decimal 12196 4
    epsilon := decimal 35032 10
    halfLeft := decimal 3728 9
    twoThirdLeft := decimal 5779 11
    halfRight := decimal 2262 9
    twoThirdRight := decimal 2968 11
    cell1 := sourceCell 1 18251 8
    cell2 := sourceCell 2 45626 7
    cell3 := sourceCell 3 11407 5
    cell4 := sourceCell 4 28516 4
    cell5 := sourceCell 5 71291 3 }

def Certificate.cells (value : Certificate) : List Cell :=
  [value.cell1, value.cell2, value.cell3, value.cell4, value.cell5]

def endpoint (value : Certificate) (cell : Cell)
    (half twoThird : Decimal) (point : Nat) : Decimal :=
  (Decimal.powNat point cell.coordinate.column).mul
    ((value.a1.mul half).add ((value.a2.mul twoThird).add value.epsilon))

def checkCell (value : Certificate) (cell : Cell) : Bool :=
  cell.coordinate.row == value.row &&
    decide (1 ≤ cell.coordinate.column ∧ cell.coordinate.column ≤ 5) &&
    cell.target.le (corrected cell.listed) &&
    (endpoint value cell value.halfLeft value.twoThirdLeft value.row).le cell.target &&
    (endpoint value cell value.halfRight value.twoThirdRight value.nextRow).le cell.target

def sourceHeader (value : Certificate) : Bool :=
  value.row == 25 && value.nextRow == 26 &&
    value.a1 == decimal 100000002 8 &&
    value.a2 == decimal 12196 4 &&
    value.epsilon == decimal 35032 10 &&
    value.halfLeft == decimal 3728 9 &&
    value.twoThirdLeft == decimal 5779 11 &&
    value.halfRight == decimal 2262 9 &&
    value.twoThirdRight == decimal 2968 11

def sameSourceCell (observed expected : Cell) : Bool :=
  observed == expected

def sourceCells (value : Certificate) : Bool :=
  sameSourceCell value.cell1 (sourceCell 1 18251 8) &&
    sameSourceCell value.cell2 (sourceCell 2 45626 7) &&
    sameSourceCell value.cell3 (sourceCell 3 11407 5) &&
    sameSourceCell value.cell4 (sourceCell 4 28516 4) &&
    sameSourceCell value.cell5 (sourceCell 5 71291 3)

def firstFailure? (value : Certificate) : Option Nat :=
  value.cells.findSome? fun cell =>
    if checkCell value cell then none else some (coordinateCode cell.coordinate)

def validCertificate (value : Certificate) : Bool :=
  sourceHeader value && sourceCells value && value.cells.all (checkCell value)

def encodeDecimal (value : Decimal) : List Nat := [value.mantissa, value.scale]

def encodeCell (cell : Cell) : List Nat :=
  [cell.coordinate.row, cell.coordinate.column] ++
    encodeDecimal cell.listed ++ encodeDecimal cell.target

def certificateBody (value : Certificate) : List Nat :=
  [value.row, value.nextRow] ++ encodeDecimal value.a1 ++
    encodeDecimal value.a2 ++ encodeDecimal value.epsilon ++
    encodeDecimal value.halfLeft ++ encodeDecimal value.twoThirdLeft ++
    encodeDecimal value.halfRight ++ encodeDecimal value.twoThirdRight ++
    encodeCell value.cell1 ++ encodeCell value.cell2 ++ encodeCell value.cell3 ++
    encodeCell value.cell4 ++ encodeCell value.cell5

def decodeDecimal? : List Nat → Option (Decimal × List Nat)
  | mantissa :: scale :: rest => some (decimal mantissa scale, rest)
  | _ => none

def decodeCell? : List Nat → Option (Cell × List Nat)
  | row :: column :: rest => do
      let (listed, rest) ← decodeDecimal? rest
      let (target, rest) ← decodeDecimal? rest
      some (⟨⟨row, column⟩, listed, target⟩, rest)
  | _ => none

def decodeCertificate? (cells : List Nat) : Option Certificate := do
  let row :: nextRow :: rest := cells | none
  let (a1, rest) ← decodeDecimal? rest
  let (a2, rest) ← decodeDecimal? rest
  let (epsilon, rest) ← decodeDecimal? rest
  let (halfLeft, rest) ← decodeDecimal? rest
  let (twoThirdLeft, rest) ← decodeDecimal? rest
  let (halfRight, rest) ← decodeDecimal? rest
  let (twoThirdRight, rest) ← decodeDecimal? rest
  let (cell1, rest) ← decodeCell? rest
  let (cell2, rest) ← decodeCell? rest
  let (cell3, rest) ← decodeCell? rest
  let (cell4, rest) ← decodeCell? rest
  let (cell5, rest) ← decodeCell? rest
  if rest.isEmpty then
    some
      { row := row
        nextRow := nextRow
        a1 := a1
        a2 := a2
        epsilon := epsilon
        halfLeft := halfLeft
        twoThirdLeft := twoThirdLeft
        halfRight := halfRight
        twoThirdRight := twoThirdRight
        cell1 := cell1
        cell2 := cell2
        cell3 := cell3
        cell4 := cell4
        cell5 := cell5 }
  else none

def body : List Nat := certificateBody certificate

def decodeBatch? (cells : List Nat) : Option Unit :=
  if cells == body then some () else none

inductive Bound where
  | all
  | upper (cell : Cell)
  | empty
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .upper left, .upper right =>
      if left.target.le right.target then .upper left else .upper right

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "pnt-table10.source" }
def batchKey : OpKey := { name := "pnt-table10.row-batch" }
def ruleKey : RuleKey := { name := "pnt-table10.checked-row" }

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
  | target :: targets, cell :: cells =>
      { node := target, fact := .upper cell, payload } :: candidates targets cells
  | _, _ => []

def expectedCandidates : List (Candidate Bound) :=
  candidates cellNodes certificate.cells

def batchRule : Registration :=
  { key := ruleKey
    head := batchKey
    kind := .forward
    watches := []
    writes := (List.range 5).map Slot.argument }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun cells => (decodeBatch? cells).isSome }

def planForBody (cells : List Nat) (request : RuleRequest Bound) : Plan Bound :=
  match decodeCertificate? cells with
  | some value =>
      match firstFailure? value with
      | some coordinate => { outcome := .failed coordinate, drafts := [] }
      | none =>
          if validCertificate value then
            if request.inputs.isEmpty && request.writes == cellNodes then
              { outcome := .success (candidates cellNodes value.cells) []
                  { arithmeticWork := 10, estimatedProofNodes := 30 }
                drafts := [{ label := payload, role := .fact, schema := 1, body := cells }] }
            else { outcome := .failed 1, drafts := [] }
          else { outcome := .failed 1, drafts := [] }
  | none => { outcome := .failed 1, drafts := [] }

def batchPlan : RuleRequest Bound → Plan Bound := planForBody body

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }

def batchPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[batchOperation]
    handlers := #[Handler.statelessPlanned batchRule batchPlan #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, batchPackage]

def engineLimits : State.Limits :=
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
    maxObservationValue := 512
    maxDiagnosticValue := 512
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
  { maxDecisions := 4, maxTraversal := 64, maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 5
    maxBodyCells := 46
    maxDrafts := 5
    maxDraftCells := 46
    maxAtom := 1002001 * 71291
    maxSchema := 1
    maxUses := 5 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound := Array.replicate 6 .all

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

end Hex.Interval.Experiment.PntTable10Shard
