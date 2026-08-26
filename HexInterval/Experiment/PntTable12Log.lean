/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession
public import HexInterval.Experiment.PntTable12Ordinary

@[expose] public section

/-!
# PNT+ Table 12 logarithmic rows

Two checked logarithm-window actions feed two five-cell row actions.  A row
action is unavailable until its own window fact is installed, so the runtime
chronology records the numerical dependency used by the proof companion.
-/

namespace Hex.Interval.Experiment.PntTable12Log

open Propagator PayloadArena
open PntTable12Ordinary (Decimal decimal)

inductive LogRow where
  | fiveE10
  | thirtyTwoE12
  deriving DecidableEq, Repr

structure Coordinate where
  row : LogRow
  column : Nat
  deriving DecidableEq, Repr

/-- Stable diagnostic codes occupy a range disjoint from ordinary `b * 8 + k`
codes. -/
def coordinateCode (coordinate : Coordinate) : Nat :=
  400 + (match coordinate.row with | .fiveE10 => 0 | .thirtyTwoE12 => 1) * 8 +
    coordinate.column

structure CellCertificate where
  coordinate : Coordinate
  cut : Decimal
  deriving DecidableEq, Repr

structure RowCertificate where
  row : LogRow
  floor : Nat
  input : Decimal
  lower : Decimal
  upper : Decimal
  cell1 : Decimal
  cell2 : Decimal
  cell3 : Decimal
  cell4 : Decimal
  cell5 : Decimal
  c : Decimal
  capital : Decimal
  mMantissa : Nat
  mExponent : Nat
  deriving DecidableEq, Repr

def RowCertificate.cells (certificate : RowCertificate) : List CellCertificate :=
  [{ coordinate := { row := certificate.row, column := 1 }, cut := certificate.cell1 },
    { coordinate := { row := certificate.row, column := 2 }, cut := certificate.cell2 },
    { coordinate := { row := certificate.row, column := 3 }, cut := certificate.cell3 },
    { coordinate := { row := certificate.row, column := 4 }, cut := certificate.cell4 },
    { coordinate := { row := certificate.row, column := 5 }, cut := certificate.cell5 }]

def fiveRow : RowCertificate :=
  { row := .fiveE10
    floor := 24
    input := decimal 50000000000 0
    lower := decimal 246352888 7
    upper := decimal 246352889 7
    cell1 := decimal 2070820 10
    cell2 := decimal 5101530 9
    cell3 := decimal 1256780 7
    cell4 := decimal 3096110 6
    cell5 := decimal 7627340 5
    c := decimal 88 2
    capital := decimal 86 2
    mMantissa := 32
    mExponent := 12 }

def thirtyTwoRow : RowCertificate :=
  { row := .thirtyTwoE12
    floor := 31
    input := decimal 32000000000000 0
    lower := decimal 310967570 7
    upper := decimal 310967571 7
    cell1 := decimal 1069930 11
    cell2 := decimal 3327130 10
    cell3 := decimal 1034630 8
    cell4 := decimal 3217360 7
    cell5 := decimal 1000500 5
    c := decimal 94 2
    capital := decimal 94 2
    mMantissa := 1
    mExponent := 19 }

def logRows : List RowCertificate := [fiveRow, thirtyTwoRow]
def logCells : List CellCertificate := logRows.flatMap RowCertificate.cells

def decimalLe (left right : Decimal) : Bool :=
  decide (left.mantissa * 10 ^ right.scale ≤ right.mantissa * 10 ^ left.scale)

def decimalMax (left right : Decimal) : Decimal :=
  if decimalLe left right then right else left

def decimalMin (left right : Decimal) : Decimal :=
  if decimalLe left right then left else right

structure Range where
  lower : Option Decimal
  upper : Option Decimal
  deriving DecidableEq, Repr

namespace Range

def lowerMax : Option Decimal → Option Decimal → Option Decimal
  | none, right | right, none => right
  | some left, some right => some (decimalMax left right)

def upperMin : Option Decimal → Option Decimal → Option Decimal
  | none, right | right, none => right
  | some left, some right => some (decimalMin left right)

def intersect (left right : Range) : Range :=
  { lower := lowerMax left.lower right.lower
    upper := upperMin left.upper right.upper }

end Range

inductive Bound where
  | all
  | range (value : Range)
  | empty
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .range left, .range right => .range (left.intersect right)

def point (value : Decimal) : Bound := .range { lower := some value, upper := some value }
def window (lower upper : Decimal) : Bound := .range { lower := some lower, upper := some upper }
def upper (value : Decimal) : Bound := .range { lower := none, upper := some value }

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "pnt-table12-log.source" }
def logKey : OpKey := { name := "pnt-table12-log.log" }
def fiveBatchKey : OpKey := { name := "pnt-table12-log.five-batch" }
def thirtyTwoBatchKey : OpKey := { name := "pnt-table12-log.thirty-two-batch" }
def logRuleKey : RuleKey := { name := "pnt-table12-log.checked-window" }
def fiveRuleKey : RuleKey := { name := "pnt-table12-log.five-row" }
def thirtyTwoRuleKey : RuleKey := { name := "pnt-table12-log.thirty-two-row" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def logOperation : Operation := { key := logKey, inputs := [real], output := real }
def fiveBatchOperation : Operation :=
  { key := fiveBatchKey, inputs := List.replicate 6 real, output := real }
def thirtyTwoBatchOperation : Operation :=
  { key := thirtyTwoBatchKey, inputs := List.replicate 6 real, output := real }

def operations : Array Operation :=
  #[sourceOperation, logOperation, fiveBatchOperation, thirtyTwoBatchOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def logInstruction (input : NodeId) : Node :=
  { domain := real, op := { index := 1 }, args := [input] }

def fiveCellNodes : List NodeId := (List.range 5).map fun index => node (index + 4)
def thirtyTwoCellNodes : List NodeId := (List.range 5).map fun index => node (index + 9)
def cellNodes : List NodeId := fiveCellNodes ++ thirtyTwoCellNodes

def batchInstruction (operation : Nat) (input : NodeId) (cells : List NodeId) : Node :=
  { domain := real, op := { index := operation }, args := input :: cells }

def program : Program :=
  { operations
    nodes := #[sourceInstruction, logInstruction (node 0), sourceInstruction,
      logInstruction (node 2), sourceInstruction, sourceInstruction, sourceInstruction,
      sourceInstruction, sourceInstruction, sourceInstruction, sourceInstruction,
      sourceInstruction, sourceInstruction, sourceInstruction,
      batchInstruction 2 (node 1) fiveCellNodes,
      batchInstruction 3 (node 3) thirtyTwoCellNodes] }

def encodeDecimal (value : Decimal) : List Nat := [value.mantissa, value.scale]
def encodeCell (cell : CellCertificate) : List Nat :=
  [coordinateCode cell.coordinate] ++ encodeDecimal cell.cut

def windowBody (certificate : RowCertificate) : List Nat :=
  [(match certificate.row with | .fiveE10 => 0 | .thirtyTwoE12 => 1),
    certificate.floor] ++
    encodeDecimal certificate.input ++ encodeDecimal certificate.lower ++
    encodeDecimal certificate.upper

def rowBody (certificate : RowCertificate) : List Nat :=
  windowBody certificate ++ certificate.cells.flatMap encodeCell ++
    encodeDecimal certificate.c ++ encodeDecimal certificate.capital ++
    [certificate.mMantissa, certificate.mExponent]

/-- Synthetic zero-cut mutation of the pinned row, used to ensure a false cell
is diagnosed at its paper coordinate instead of retried at higher precision. -/
def falseFiveRow : RowCertificate := { fiveRow with cell1 := decimal 0 0 }
def falseFiveBody : List Nat := rowBody falseFiveRow
def falseFiveCoordinate : Coordinate := { row := .fiveE10, column := 1 }

def mutationCoordinate? (body : List Nat) : Option Coordinate :=
  if body == falseFiveBody then some falseFiveCoordinate else none

def decodeWindow? (body : List Nat) : Option LogRow :=
  if body == windowBody fiveRow then some .fiveE10
  else if body == windowBody thirtyTwoRow then some .thirtyTwoE12
  else none

def decodeRow? (body : List Nat) : Option LogRow :=
  if body == rowBody fiveRow then some .fiveE10
  else if body == rowBody thirtyTwoRow then some .thirtyTwoE12
  else none

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1,
    validateBody := fun body => (decodeWindow? body).isSome || (decodeRow? body).isSome }

def logRule : Registration :=
  { key := logRuleKey, head := logKey, kind := .forward,
    watches := [.argument 0], writes := [.result] }

def rowRule (key : RuleKey) (head : OpKey) : Registration :=
  { key, head, kind := .forward, watches := [.argument 0],
    writes := (List.range 5).map fun index => .argument (index + 1) }

def fiveRule : Registration := rowRule fiveRuleKey fiveBatchKey
def thirtyTwoRule : Registration := rowRule thirtyTwoRuleKey thirtyTwoBatchKey

def logPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      let certificate? :=
        if input.fact == Bound.point fiveRow.input then some fiveRow
        else if input.fact == Bound.point thirtyTwoRow.input then some thirtyTwoRow
        else none
      match certificate? with
      | some certificate =>
          { outcome := .success
              [{ node := target, fact := .window certificate.lower certificate.upper,
                 payload := payload 0 }] []
              { arithmeticWork := 2, estimatedProofNodes := 8 }
            drafts :=
              [{ label := payload 0
                 role := .fact
                 schema := 1
                 body := windowBody certificate }] }
      | none => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def rowPlanForBody (certificate : RowCertificate) (body : List Nat)
    (request : RuleRequest Bound) : Plan Bound :=
  if body != rowBody certificate then
    match mutationCoordinate? body with
    | some coordinate => { outcome := .failed (coordinateCode coordinate), drafts := [] }
    | none => { outcome := .failed 1, drafts := [] }
  else
  match request.inputs, request.writes with
  | [input], writes =>
      if input.fact == Bound.window certificate.lower certificate.upper &&
          writes == (match certificate.row with
            | .fiveE10 => fiveCellNodes | .thirtyTwoE12 => thirtyTwoCellNodes) then
        { outcome := .success
            (List.zipWith (fun target cell =>
              { node := target, fact := Bound.upper cell.cut, payload := payload 1 })
              writes certificate.cells) []
            { arithmeticWork := 12, estimatedProofNodes := 50 }
          drafts :=
            [{ label := payload 1
               role := .fact
               schema := 1
               body := rowBody certificate }] }
      else { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def rowPlan (certificate : RowCertificate) (request : RuleRequest Bound) : Plan Bound :=
  rowPlanForBody certificate (rowBody certificate) request

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }

def logPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[logOperation],
    handlers := #[Handler.statelessPlanned logRule logPlan #[factFormat]] }

def rowPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[fiveBatchOperation, thirtyTwoBatchOperation],
    handlers := #[Handler.statelessPlanned fiveRule (rowPlan fiveRow) #[factFormat],
      Handler.statelessPlanned thirtyTwoRule (rowPlan thirtyTwoRow) #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, logPackage, rowPackage]

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 4, maxNodes := 16, maxRules := 3, maxRegistryEntries := 12,
    maxReplayFormats := 4, maxArity := 6, maxScopeNodes := 1, maxApplications := 4,
    maxQueueEntries := 40, maxActions := 8, maxMatcherVisits := 8, matcherBatchSize := 4,
    maxAcceptedFacts := 12, maxRetainedSuggestions := 0, maxEffort := 0,
    maxObservationValue := 512, maxDiagnosticValue := 512, maxOutcomeCandidates := 5,
    maxOutcomeSuggestions := 0, maxProposalItems := 5, maxInstances := 0,
    maxGeneration := 0, maxNodeDepth := 2, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 12, maxTraversal := 64, maxLiveOffers := 12 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 16, maxBodyCells := 100, maxDrafts := 8, maxDraftCells := 100,
    maxAtom := 32000000000000, maxSchema := 1, maxUses := 16 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound :=
  #[Bound.point fiveRow.input, .all, Bound.point thirtyTwoRow.input, .all,
    .all, .all, .all, .all, .all, .all, .all, .all, .all, .all, .all, .all]

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

def coordinateForNode? (target : NodeId) : Option Coordinate :=
  if target.index < 4 then none
  else (logCells[target.index - 4]?).map CellCertificate.coordinate

end Hex.Interval.Experiment.PntTable12Log
