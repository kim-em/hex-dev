/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Generated ordinary-row PNT+ Table 12 batch

This package extends the retained row-25 fixture with the other 23 ordinary
rows of PNT+'s `BKLNW.table_12_check`.  One bounded action installs all 115
coordinate-bearing upper cuts from one source-pinned table payload.  The
single action is deliberately an acceptance fixture, not the production
chunk-size policy.
-/

namespace Hex.Interval.Experiment.PntTable12Ordinary

open Propagator PayloadArena

structure Coordinate where
  row : Nat
  column : Nat
  deriving DecidableEq, Repr

def coordinateCode (coordinate : Coordinate) : Nat :=
  coordinate.row * 8 + coordinate.column

/-- A nonnegative decimal represented exactly as `mantissa / 10^scale`. -/
structure Decimal where
  mantissa : Nat
  scale : Nat
  deriving DecidableEq, Repr

def decimal (mantissa scale : Nat) : Decimal := { mantissa, scale }

structure CellCertificate where
  coordinate : Coordinate
  cut : Decimal
  deriving DecidableEq, Repr

structure RowCertificate where
  row : Nat
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

def row (b : Nat) (cell1 cell2 cell3 cell4 cell5 c capital : Decimal)
    (mMantissa mExponent : Nat) : RowCertificate :=
  { row := b, cell1, cell2, cell3, cell4, cell5, c, capital,
    mMantissa, mExponent }

def RowCertificate.cells (certificate : RowCertificate) : List CellCertificate :=
  [{ coordinate := { row := certificate.row, column := 1 }, cut := certificate.cell1 },
    { coordinate := { row := certificate.row, column := 2 }, cut := certificate.cell2 },
    { coordinate := { row := certificate.row, column := 3 }, cut := certificate.cell3 },
    { coordinate := { row := certificate.row, column := 4 }, cut := certificate.cell4 },
    { coordinate := { row := certificate.row, column := 5 }, cut := certificate.cell5 }]

/-- The 23 source rows not already covered by `PntTable12.rowCertificate`.
The two rows whose first component is a logarithm are intentionally absent. -/
def ordinaryRows : List RowCertificate := [
  row 20 (decimal 168440 8) (decimal 336880 7) (decimal 673750 6)
    (decimal 134750 4) (decimal 269500 3) (decimal 8 1) (decimal 81 2) 5 10,
  row 21 (decimal 106840 8) (decimal 224350 7) (decimal 471140 6)
    (decimal 989390 5) (decimal 207780 3) (decimal 8 1) (decimal 81 2) 5 10,
  row 22 (decimal 676540 9) (decimal 148840 7) (decimal 327450 6)
    (decimal 720380 5) (decimal 158490 3) (decimal 8 1) (decimal 81 2) 5 10,
  row 23 (decimal 427800 9) (decimal 983920 8) (decimal 226310 6)
    (decimal 520500 5) (decimal 119720 3) (decimal 8 1) (decimal 81 2) 5 10,
  row 24 (decimal 270120 9) (decimal 648290 8) (decimal 155590 6)
    (decimal 373410 5) (decimal 896190 4) (decimal 8 1) (decimal 81 2) 5 10,
  row 26 (decimal 110220 9) (decimal 286560 8) (decimal 745050 7)
    (decimal 193720 5) (decimal 503650 4) (decimal 88 2) (decimal 86 2) 32 12,
  row 27 (decimal 693270 10) (decimal 187190 8) (decimal 505400 7)
    (decimal 136460 5) (decimal 368430 4) (decimal 88 2) (decimal 86 2) 32 12,
  row 28 (decimal 435580 10) (decimal 121970 8) (decimal 341500 7)
    (decimal 956180 6) (decimal 267730 4) (decimal 88 2) (decimal 86 2) 32 12,
  row 29 (decimal 273380 10) (decimal 792780 9) (decimal 229910 7)
    (decimal 666730 6) (decimal 193360 4) (decimal 88 2) (decimal 86 2) 32 12,
  row 30 (decimal 171400 10) (decimal 514180 9) (decimal 154260 7)
    (decimal 462760 6) (decimal 138830 4) (decimal 88 2) (decimal 86 2) 32 12,
  row 31 (decimal 107350 10) (decimal 332790 9) (decimal 1034630 8)
    (decimal 3217360 7) (decimal 1000500 5) (decimal 88 2) (decimal 86 2) 32 12,
  row 32 (decimal 7005640 12) (decimal 2241810 10) (decimal 7173770 9)
    (decimal 2295610 7) (decimal 7345940 6) (decimal 94 2) (decimal 94 2) 1 19,
  row 33 (decimal 438000 11) (decimal 144540 9) (decimal 476990 8)
    (decimal 157410 6) (decimal 519440 5) (decimal 94 2) (decimal 94 2) 1 19,
  row 34 (decimal 273610 11) (decimal 930270 10) (decimal 316300 8)
    (decimal 107540 6) (decimal 365640 5) (decimal 94 2) (decimal 94 2) 1 19,
  row 35 (decimal 170780 11) (decimal 597730 10) (decimal 209210 8)
    (decimal 732220 7) (decimal 256280 5) (decimal 94 2) (decimal 94 2) 1 19,
  row 36 (decimal 106520 11) (decimal 383460 10) (decimal 138050 8)
    (decimal 496960 7) (decimal 178910 5) (decimal 94 2) (decimal 94 2) 1 19,
  row 37 (decimal 663850 12) (decimal 245630 10) (decimal 908810 9)
    (decimal 336260 7) (decimal 124420 5) (decimal 94 2) (decimal 94 2) 1 19,
  row 38 (decimal 413450 12) (decimal 157120 10) (decimal 597020 9)
    (decimal 226870 7) (decimal 862100 6) (decimal 94 2) (decimal 94 2) 1 19,
  row 39 (decimal 257330 12) (decimal 100360 10) (decimal 391400 9)
    (decimal 152650 7) (decimal 595320 6) (decimal 94 2) (decimal 94 2) 1 19,
  row 40 (decimal 160060 12) (decimal 640240 11) (decimal 256100 9)
    (decimal 102440 7) (decimal 409750 6) (decimal 94 2) (decimal 94 2) 1 19,
  row 41 (decimal 994970 13) (decimal 407940 11) (decimal 167260 9)
    (decimal 685740 8) (decimal 281160 6) (decimal 94 2) (decimal 94 2) 1 19,
  row 42 (decimal 618140 13) (decimal 259620 11) (decimal 109040 9)
    (decimal 457970 8) (decimal 192350 6) (decimal 94 2) (decimal 94 2) 1 19,
  row 43 (decimal 383820 13) (decimal 165050 11) (decimal 709680 10)
    (decimal 305170 8) (decimal 131220 6) (decimal 94 2) (decimal 94 2) 1 19]

def ordinaryCells : List CellCertificate :=
  ordinaryRows.flatMap RowCertificate.cells

inductive Bound where
  | all
  | upper (cell : CellCertificate)
  deriving DecidableEq, Repr

namespace Bound

def cutLe (left right : CellCertificate) : Bool :=
  decide (left.cut.mantissa * 10 ^ right.cut.scale ≤
    right.cut.mantissa * 10 ^ left.cut.scale)

/-- Total semantic intersection of nonnegative rational upper cuts. -/
def meet : Bound → Bound → Bound
  | .all, right => right
  | left, .all => left
  | .upper left, .upper right =>
      if cutLe left right then .upper left else .upper right

/-- Whether two bounds denote the same rational upper cut. Coordinates are
diagnostic provenance, so equal cuts do not count as a semantic improvement. -/
def sameCut : Bound → Bound → Bool
  | .all, .all => true
  | .upper left, .upper right => cutLe left right && cutLe right left
  | _, _ => false

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed.sameCut current then .noChange else .improved installed

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "pnt-table12-ordinary.source" }
def batchKey : OpKey := { name := "pnt-table12-ordinary.batch" }
def batchRuleKey : RuleKey := { name := "pnt-table12-ordinary.checked-batch" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def batchOperation : Operation :=
  { key := batchKey
    inputs := List.replicate ordinaryCells.length real
    output := real }

def operations : Array Operation := #[sourceOperation, batchOperation]

def node (index : Nat) : NodeId := { index }
def payload : PayloadId := { index := 0 }

def cellNodes : List NodeId := (List.range ordinaryCells.length).map node

def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def batchInstruction : Node :=
  { domain := real, op := { index := 1 }, args := cellNodes }

def program : Program :=
  { operations
    nodes := (List.replicate ordinaryCells.length sourceInstruction ++
      [batchInstruction]).toArray }

def encodeDecimal (value : Decimal) : List Nat := [value.mantissa, value.scale]

def encodeRow (certificate : RowCertificate) : List Nat :=
  [certificate.row] ++ encodeDecimal certificate.cell1 ++
    encodeDecimal certificate.cell2 ++ encodeDecimal certificate.cell3 ++
    encodeDecimal certificate.cell4 ++ encodeDecimal certificate.cell5 ++
    encodeDecimal certificate.c ++ encodeDecimal certificate.capital ++
    [certificate.mMantissa, certificate.mExponent]

def batchBody : List Nat := ordinaryRows.flatMap encodeRow

def decodeBatch? (body : List Nat) : Option Unit :=
  if body == batchBody then some () else none

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1,
    validateBody := fun body => (decodeBatch? body).isSome }

def candidates : List NodeId → List CellCertificate → List (Candidate Bound)
  | target :: targets, cell :: cells =>
      { node := target, fact := .upper cell, payload } :: candidates targets cells
  | _, _ => []

def expectedCandidates : List (Candidate Bound) := candidates cellNodes ordinaryCells

def batchRule : Registration :=
  { key := batchRuleKey
    head := batchKey
    kind := .forward
    watches := []
    writes := (List.range ordinaryCells.length).map Slot.argument }

def planForBody (body : List Nat) (request : RuleRequest Bound) : Plan Bound :=
  match decodeBatch? body with
  | some () =>
      match request.inputs with
      | [] =>
          if request.writes == cellNodes then
            { outcome := .success expectedCandidates []
                { arithmeticWork := 92, estimatedProofNodes := 460 }
              drafts := [{ label := payload, role := .fact, schema := 1, body }] }
          else { outcome := .failed 1, drafts := [] }
      | _ => { outcome := .failed 1, drafts := [] }
  | none => { outcome := .failed 1, drafts := [] }

def batchPlan : RuleRequest Bound → Plan Bound := planForBody batchBody

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }

def batchPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[batchOperation]
    handlers := #[Handler.statelessPlanned batchRule batchPlan #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, batchPackage]

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 2
    maxNodes := 116
    maxRules := 1
    maxRegistryEntries := 8
    maxReplayFormats := 2
    maxArity := 115
    maxScopeNodes := 1
    maxApplications := 1
    maxQueueEntries := 256
    maxActions := 2
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 115
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 512
    maxDiagnosticValue := 512
    maxOutcomeCandidates := 115
    maxOutcomeSuggestions := 0
    maxProposalItems := 115
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 4, maxTraversal := 256, maxLiveOffers := 4 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 128
    maxBodyCells := 400
    maxDrafts := 128
    maxDraftCells := 400
    maxAtom := 10000000000000000000
    maxSchema := 1
    maxUses := 128 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound := Array.replicate 116 .all

def finalCell : CellCertificate :=
  { coordinate := { row := 43, column := 5 }, cut := decimal 131220 6 }

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

def coordinateForNode? (target : NodeId) : Option Coordinate :=
  (ordinaryCells[target.index]?).map CellCertificate.coordinate

end Hex.Interval.Experiment.PntTable12Ordinary
