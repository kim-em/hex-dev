/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module


public import HexInterval.Experiment.PntFks2Shard
public import HexInterval.Experiment.PntFks2FamilyData

@[expose] public section

/-!
# Full pinned PNT+ FKS2 family runtime

The 13,590 cells are scheduled in 680 bounded actions.  Every action carries
one source shard identifier plus at most twenty eight-field cell encodings;
the final action carries ten cells.  This is the local/release scale profile,
separate from the shard-11 merge-gating fixture.
-/

namespace Hex.Interval.Experiment.PntFks2Family

open Propagator PayloadArena
open PntFks2Shard (Bound Cell checkCell encodeCell factDomain real sourceOperation
  sourceInstruction sourcePackage candidates)

/-- Stable diagnostic radix: source coordinates are below 20,000. -/
def coordinateRadix : Nat := 100000

def coordinateCode (shard : Nat) (cell : Cell) : Nat :=
  shard * coordinateRadix + cell.b

def decodeCoordinate (code : Nat) : Nat × Nat :=
  (code / coordinateRadix, code % coordinateRadix)

def firstFailure? (shard : Nat) : List Cell → Option Nat
  | [] => none
  | cell :: cells =>
      if checkCell cell then firstFailure? shard cells
      else some (coordinateCode shard cell)

def batchKey : OpKey := { name := "pnt-fks2-family.batch" }
def ruleKey (index : Nat) : RuleKey :=
  { name := "pnt-fks2-family.chunk." ++ toString index }

def batchOperation : Operation :=
  { key := batchKey, inputs := List.replicate allCells.length real, output := real }

def operations : Array Operation := #[sourceOperation, batchOperation]
def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }
def cellNodes : List NodeId := (List.range allCells.length).map node
def batchNode : NodeId := node allCells.length

def batchInstruction : Node :=
  { domain := real, op := { index := 1 }, args := cellNodes }

def program : Program :=
  { operations
    nodes := (List.replicate allCells.length sourceInstruction ++
      [batchInstruction]).toArray }

def chunkOffset (index : Nat) : Nat := index * runtimeChunkSize

def chunkNodes (index : Nat) : List NodeId :=
  (cellNodes.drop (chunkOffset index)).take (familyChunk index).length

/-- One shard atom plus eight exact atoms for every cell. -/
def chunkBody (index : Nat) : List Nat :=
  chunkShard index :: (familyChunk index).flatMap encodeCell

def decodeChunk? (index : Nat) (body : List Nat) : Option Unit :=
  if body == chunkBody index then some () else none

def factFormat (index : Nat) : ReplayFormat :=
  { role := .fact, schema := 1,
    validateBody := fun body => (decodeChunk? index body).isSome }

def batchRule (index : Nat) : Registration :=
  { key := ruleKey index
    head := batchKey
    kind := .forward
    watches := []
    writes := (List.range (familyChunk index).length).map fun offset =>
      Slot.argument (chunkOffset index + offset) }

def planCells (index : Nat) (candidateCells : List Cell)
    (request : RuleRequest Bound) : Plan Bound :=
  match firstFailure? (chunkShard index) candidateCells with
  | some coordinate => { outcome := .failed coordinate, drafts := [] }
  | none =>
      match request.inputs with
      | [] =>
          if candidateCells == familyChunk index && request.writes == chunkNodes index then
            { outcome := .success (candidates (chunkNodes index)) []
                { arithmeticWork := candidateCells.length * 12,
                  estimatedProofNodes := candidateCells.length * 8 }
              drafts :=
                [{ label := payload 0
                   role := .fact
                   schema := 1
                   body := chunkShard index :: candidateCells.flatMap encodeCell }] }
          else { outcome := .failed 1, drafts := [] }
      | _ => { outcome := .failed 1, drafts := [] }

def batchPlan (index : Nat) (request : RuleRequest Bound) : Plan Bound :=
  planCells index (familyChunk index) request

def batchPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[batchOperation]
    handlers := (Array.range familyChunkCount).map fun index =>
      Handler.statelessPlanned (batchRule index) (batchPlan index) #[factFormat index] }

def packages : Array (Package Bound) := #[sourcePackage, batchPackage]

/-- Explicit global and per-action resource envelope for the local profile. -/
def engineLimits : Propagator.Limits :=
  { maxOperations := 2
    maxNodes := 14000
    maxRules := 700
    maxRegistryEntries := 2048
    maxReplayFormats := 1024
    maxArity := 14000
    maxScopeNodes := 1
    maxApplications := 700
    maxQueueEntries := 1024
    maxActions := 700
    maxMatcherVisits := 1
    matcherBatchSize := 1
    maxAcceptedFacts := 14000
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 2048
    maxDiagnosticValue := 2000000
    maxOutcomeCandidates := 20
    maxOutcomeSuggestions := 0
    maxProposalItems := 20
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 1
    maxEqualities := 0
    splitEndpointLimit := { maxEndpointHeight := 16, maxAlignmentShift := 8 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 1024, maxTraversal := 20000000, maxLiveOffers := 1024 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 700
    maxBodyCells := 110000
    maxDrafts := 20
    maxDraftCells := 161
    maxAtom := 10000000000000000000000000000000000000000000000000
    maxSchema := 1
    maxUses := 20 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def initialFacts : Array Bound := Array.replicate (allCells.length + 1) .all

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages initialFacts limits

end Hex.Interval.Experiment.PntFks2Family
