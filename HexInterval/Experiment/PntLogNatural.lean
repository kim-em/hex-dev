/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession
public import HexInterval.Experiment.SemanticReplay

@[expose] public section

/-!
# Source-pinned natural logarithm table

This bounded package authenticates the twelve remaining two-sided
natural-number entries in PNT+'s `LogTables.lean`.  Each row records a dyadic
range reduction and an eight-term atanh certificate; real logarithm semantics
live in the Mathlib companion.
-/

namespace Hex.Interval.Experiment.PntLogNatural

open Propagator PayloadArena

structure Window where
  input : Nat
  lower : Nat
  upper : Nat
  scale : Nat
  deriving DecidableEq, Repr

inductive Bound where
  | all
  | exact (value : Nat)
  | window (value : Window)
  | empty
  deriving DecidableEq, Repr

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    if current == proposed then .noChange
    else match current, proposed with
      | _, .all => .noChange
      | .all, proposed => .improved proposed
      | _, _ => .malformed 1

structure Certificate where
  input : Nat
  shift : Nat
  xNum : Nat
  xDen : Nat
  terms : Nat
  lower : Nat
  upper : Nat
  scale : Nat
  deriving DecidableEq, Repr

def Certificate.window (row : Certificate) : Window :=
  { input := row.input, lower := row.lower, upper := row.upper, scale := row.scale }

def Certificate.valid (row : Certificate) : Bool :=
  let power := 2 ^ row.shift
  row.input ≥ power &&
    row.xNum * (row.input + power) == row.xDen * (row.input - power) &&
    row.xNum < row.xDen &&
    row.terms == 8 && row.scale == 6 && row.lower < row.upper

def row (input shift xNum xDen lower upper : Nat) : Certificate :=
  { input, shift, xNum, xDen, terms := 8, lower, upper, scale := 6 }

def row3 : Certificate := row 3 1 1 5 1098612 1098613
def row5 : Certificate := row 5 2 1 9 1609437 1609438
def row7 : Certificate := row 7 2 3 11 1945910 1945911
def row10 : Certificate := row 10 3 1 9 2302585 2302586
def row11 : Certificate := row 11 3 3 19 2397895 2397896
def row13 : Certificate := row 13 3 5 21 2564949 2564950
def row17 : Certificate := row 17 4 1 33 2833213 2833214
def row19 : Certificate := row 19 4 3 35 2944438 2944439
def row23 : Certificate := row 23 4 7 39 3135494 3135495
def row29 : Certificate := row 29 4 13 45 3367295 3367296
def row30 : Certificate := row 30 4 7 23 3401197 3401198
def row32 : Certificate := row 32 5 0 64 3465735 3465736

def rows : List Certificate :=
  [row3, row5, row7, row10, row11, row13, row17, row19, row23, row29,
   row30, row32]

def rowFor? (input : Nat) : Option Certificate :=
  rows.find? fun row => row.input == input

def encode (row : Certificate) : List Nat :=
  [row.input, row.shift, row.xNum, row.xDen, row.terms,
    row.lower, row.upper, row.scale]

def decode? : List Nat → Option Certificate
  | [input, shift, xNum, xDen, terms, lower, upper, scale] =>
      let row := { input, shift, xNum, xDen, terms, lower, upper, scale }
      if row.valid then some row else none
  | _ => none

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "pnt-log-natural.source" }
def logKey : OpKey := { name := "pnt-log-natural.log" }
def ruleKey : RuleKey := { name := "pnt-log-natural.atanh" }

def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def logOperation : Operation := { key := logKey, inputs := [real], output := real }
def operations : Array Operation := #[sourceOperation, logOperation]
def node (index : Nat) : NodeId := { index }
def payload : PayloadId := { index := 0 }
def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def logInstruction : Node := { domain := real, op := { index := 1 }, args := [node 0] }
def program : Program := { operations, nodes := #[sourceInstruction, logInstruction] }

def registration : Registration :=
  { key := ruleKey, head := logKey, kind := .forward,
    watches := [.argument 0], writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun body => (decode? body).isSome }

def plan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      match input.fact with
      | .exact value =>
          match rowFor? value with
          | some row =>
              let outcome := .success
                  [{ node := target, fact := .window row.window, payload }] []
                  { arithmeticWork := row.terms, estimatedProofNodes := row.terms + 4 }
              { outcome := outcome
                drafts := [{ label := payload, role := .fact, schema := 1, body := encode row }] }
          | none => { outcome := .noChange {}, drafts := [] }
      | _ => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }
def logPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[logOperation],
    handlers := #[Handler.statelessPlanned registration plan #[factFormat]] }
def packages : Array (Package Bound) := #[sourcePackage, logPackage]

def checkerInput (row : Certificate) : SemanticReplay.CheckerInput Bound :=
  { baseProgram := program, initialFacts := #[.exact row.input, .all],
    target := { node := node 1, fact := .window row.window } }

def representativeInput : SemanticReplay.CheckerInput Bound := checkerInput row29

def engineLimits : Propagator.Limits :=
  { maxOperations := 2, maxNodes := 2, maxRules := 1, maxRegistryEntries := 8,
    maxReplayFormats := 2, maxArity := 1, maxScopeNodes := 1, maxApplications := 2,
    maxQueueEntries := 8, maxActions := 4, maxMatcherVisits := 2, matcherBatchSize := 2,
    maxAcceptedFacts := 2, maxRetainedSuggestions := 0, maxEffort := 0,
    maxObservationValue := 64, maxDiagnosticValue := 512, maxOutcomeCandidates := 1,
    maxOutcomeSuggestions := 0, maxProposalItems := 1, maxInstances := 0,
    maxGeneration := 0, maxNodeDepth := 2, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 4 } }
def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8, maxTraversal := 32, maxLiveOffers := 8 }
def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4, maxBodyCells := 16, maxDrafts := 2, maxDraftCells := 16,
    maxAtom := 4000000, maxSchema := 1, maxUses := 2 }
def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.PntLogNatural
