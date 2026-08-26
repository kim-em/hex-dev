/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession
public import HexInterval.Experiment.PntFks2ShardData

@[expose] public section

/-!
# PNT+ FKS2 extended-Table-4 shard probe

This is the executable half of a production-scale batching probe. It carries
all 1,000 source cells of pinned shard 11 (`b = 11010` through `b' = 12050`)
and checks them in fifty independently scheduled chunks of twenty. The
numeric check uses exact Core rationals and a 128-way exponential split; its
Mathlib companion proves the shared Taylor remainder and transport once.
-/

namespace Hex.Interval.Experiment.PntFks2Shard

open Propagator PayloadArena

def qadd : Q → Q → Q := Rational.add
def qmul : Q → Q → Q := Rational.mul

def qpow (value : Q) : Nat → Q
  | 0 => 1
  | n + 1 => qmul (qpow value n) value

/-- Seven squarings, avoiding 128 linear rational normalizations per cell. -/
def qpow128 (value : Q) : Q :=
  let p2 := qmul value value
  let p4 := qmul p2 p2
  let p8 := qmul p4 p4
  let p16 := qmul p8 p8
  let p32 := qmul p16 p16
  let p64 := qmul p32 p32
  qmul p64 p64

def qLe (left right : Q) : Bool :=
  decide (left.num * (right.den : Int) ≤ right.num * (left.den : Int))

def qLt (left right : Q) : Bool :=
  decide (left.num * (right.den : Int) < right.num * (left.den : Int))

def factorial : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial n

def term (value : Q) (degree : Nat) : Q :=
  qmul (qpow value degree) (Rat.divInt 1 (factorial degree))

def sumTerms (value : Q) : Nat → Q
  | 0 => 0
  | n + 1 => qadd (sumTerms value n) (term value n)

/-- The degree-11 Taylor polynomial plus Mathlib's explicit degree-12
remainder majorant on `[0,1]`. -/
def taylorUpper (value : Q) : Q :=
  qadd (sumTerms value 12)
    (qmul (qpow value 12) (Rat.divInt 13 (factorial 12 * 12)))

def aq : Q := 92211 / 10000
def cq128 : Q := 2119 / 320000

/-- Exact rational checker behind the 128-way exponential split. -/
def checkCell (cell : Cell) : Bool :=
  qLt 0 cell.eps && qLe 0 cell.slo && qLe cell.slo cell.shi &&
    qLe (qmul cell.slo cell.slo) cell.b &&
    qLe cell.b' (qmul cell.shi cell.shi) &&
    let reduced := qmul cq128 cell.shi
    qLe reduced 1 &&
      qLe (qmul cell.eps (qpow128 (taylorUpper reduced)))
        (qmul aq (qpow cell.slo 3))

def chunkSize : Nat := 20
def chunkCount : Nat := 50

def chunk (index : Nat) : List Cell :=
  cellChunk index

def coordinateCode (cell : Cell) : Nat := cell.b

def firstFailure? : List Cell → Option Nat
  | [] => none
  | cell :: cells => if checkCell cell then firstFailure? cells else some cell.b

inductive Bound where
  | all
  | nonnegative
  deriving DecidableEq, Repr

namespace Bound

def meet : Bound → Bound → Bound
  | .all, right => right
  | left, .all => left
  | .nonnegative, .nonnegative => .nonnegative

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange else .improved installed

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "pnt-fks2-shard.source" }
def batchKey : OpKey := { name := "pnt-fks2-shard.batch" }
def ruleKey (index : Nat) : RuleKey := { name := "pnt-fks2-shard.chunk." ++ toString index }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def batchOperation : Operation :=
  { key := batchKey, inputs := List.replicate cells11.length real, output := real }

def operations : Array Operation := #[sourceOperation, batchOperation]
def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }
def cellNodes : List NodeId := (List.range cells11.length).map node
def batchNode : NodeId := node cells11.length

def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def batchInstruction : Node := { domain := real, op := { index := 1 }, args := cellNodes }
def program : Program :=
  { operations
    nodes := (List.replicate cells11.length sourceInstruction ++ [batchInstruction]).toArray }

def chunkNodes (index : Nat) : List NodeId :=
  (cellNodes.drop (index * chunkSize)).take chunkSize

def encodeQ (value : Q) : List Nat :=
  [value.num.natAbs, value.den]

def encodeCell (cell : Cell) : List Nat :=
  [cell.b, cell.b'] ++ encodeQ cell.eps ++ encodeQ cell.slo ++ encodeQ cell.shi

def chunkBody (index : Nat) : List Nat := (chunk index).flatMap encodeCell

def decodeChunk? (index : Nat) (body : List Nat) : Option Unit :=
  if body == chunkBody index then some () else none

def factFormat (index : Nat) : ReplayFormat :=
  { role := .fact, schema := 1,
    validateBody := fun body => (decodeChunk? index body).isSome }

def candidates : List NodeId → List (Candidate Bound)
  | [] => []
  | target :: targets =>
      { node := target, fact := .nonnegative, payload := payload 0 } :: candidates targets

def batchRule (index : Nat) : Registration :=
  { key := ruleKey index
    head := batchKey
    kind := .forward
    watches := []
    writes := (List.range chunkSize).map fun offset => Slot.argument (index * chunkSize + offset) }

def planCells (index : Nat) (candidateCells : List Cell)
    (request : RuleRequest Bound) : Plan Bound :=
  match firstFailure? candidateCells with
  | some coordinate => { outcome := .failed coordinate, drafts := [] }
  | none =>
      match request.inputs with
      | [] =>
          if candidateCells == chunk index && request.writes == chunkNodes index then
            { outcome := .success (candidates (chunkNodes index)) []
                { arithmeticWork := candidateCells.length * 12,
                  estimatedProofNodes := candidateCells.length * 8 }
              drafts :=
                [{ label := payload 0
                   role := .fact
                   schema := 1
                   body := candidateCells.flatMap encodeCell }] }
          else { outcome := .failed 1, drafts := [] }
      | _ => { outcome := .failed 1, drafts := [] }

def batchPlan (index : Nat) (request : RuleRequest Bound) : Plan Bound :=
  planCells index (chunk index) request

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }

def batchPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[batchOperation]
    handlers := (Array.range chunkCount).map fun index =>
      Handler.statelessPlanned (batchRule index) (batchPlan index) #[factFormat index] }

def packages : Array (Package Bound) := #[sourcePackage, batchPackage]

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 2
    maxNodes := 1001
    maxRules := 50
    maxRegistryEntries := 128
    maxReplayFormats := 64
    maxArity := 1000
    maxScopeNodes := 1
    maxApplications := 50
    maxQueueEntries := 128
    maxActions := 50
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 1000
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 2048
    maxDiagnosticValue := 20000
    maxOutcomeCandidates := 20
    maxOutcomeSuggestions := 0
    maxProposalItems := 20
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit := { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 64, maxTraversal := 65536, maxLiveOffers := 64 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 64
    maxBodyCells := 8192
    maxDrafts := 64
    maxDraftCells := 8192
    maxAtom := 100000000000000000000000000000000000000
    maxSchema := 1
    maxUses := 128 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound := Array.replicate 1001 .all

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

end Hex.Interval.Experiment.PntFks2Shard
