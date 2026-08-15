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
# Source-pinned PNT+ rational logarithm table

This bounded Mathlib-free package authenticates the fifteen distinct rational
inputs behind seventeen remaining direct logarithm declarations in PNT+
`IEANTN/LogTables.lean`. Each row records an exact dyadic range reduction and
eight-term atanh enclosure. Real logarithm semantics live in the Mathlib
companion.
-/

namespace Hex.Interval.Experiment.PntLogRational

open Propagator PayloadArena

structure Input where
  sourceIndex : Nat
  numerator : Nat
  denominator : Nat
  deriving DecidableEq, Repr

structure Window where
  sourceIndex : Nat
  lower : Nat
  upper : Nat
  scale : Nat
  deriving DecidableEq, Repr

inductive Bound where
  | all
  | exact (value : Input)
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
  sourceIndex : Nat
  inputNumerator : Nat
  inputDenominator : Nat
  shift : Nat
  xNumerator : Nat
  xDenominator : Nat
  terms : Nat
  lower : Nat
  upper : Nat
  scale : Nat
  deriving DecidableEq, Repr

def row (sourceIndex inputNumerator inputDenominator shift xNumerator
    xDenominator lower upper scale : Nat) : Certificate :=
  { sourceIndex, inputNumerator, inputDenominator, shift, xNumerator,
    xDenominator, terms := 8, lower, upper, scale }

def row2353 : Certificate := row 0 2353 1000 1 353 4353 855 856 3
def row32 : Certificate := row 1 16 5 1 3 13 1163 1164 3
def row658 : Certificate := row 2 329 50 2 129 529 1884034 1884035 6
def row11723 : Certificate := row 3 11723 1 13 3531 19915 936 937 2
def row5e10 : Certificate :=
  row 4 50000000000 1 35 15273693 82382557 246352888 246352889 7
def row32e12 : Certificate :=
  row 5 32000000000000 1 44 109922897 378358353 310967570 310967571 7
def row130 : Certificate := row 6 130 1 7 1 129 0 4868 3
def row155 : Certificate := row 7 155 1 7 27 283 0 5044 3
def row200 : Certificate := row 8 200 1 7 9 41 0 5299 3
def row300 : Certificate := row 9 300 1 8 11 139 0 5704 3
def row550 : Certificate := row 10 550 1 9 19 531 0 6310 3
def row1500 : Certificate := row 11 1500 1 10 119 631 0 7314 3
def row10000 : Certificate := row 12 10000 1 13 113 1137 0 9211 3
def row1e8 : Certificate := row 13 100000000 1 26 128481 652769 0 18421 3
def row3e10 : Certificate :=
  row 14 30000000000 1 34 12519659 46074091 0 24125 3

def rows : List Certificate :=
  [row2353, row32, row658, row11723, row5e10, row32e12, row130, row155,
   row200, row300, row550, row1500, row10000, row1e8, row3e10]

def rowFor? (sourceIndex : Nat) : Option Certificate :=
  rows.find? fun value => value.sourceIndex == sourceIndex

def Certificate.input (value : Certificate) : Input :=
  { sourceIndex := value.sourceIndex, numerator := value.inputNumerator,
    denominator := value.inputDenominator }

def Certificate.window (value : Certificate) : Window :=
  { sourceIndex := value.sourceIndex, lower := value.lower, upper := value.upper,
    scale := value.scale }

def Certificate.valid (value : Certificate) : Bool :=
  let power := 2 ^ value.shift
  rowFor? value.sourceIndex == some value &&
    decide (0 < value.inputDenominator) &&
    decide (value.inputDenominator * power ≤ value.inputNumerator) &&
    value.xNumerator * (value.inputNumerator + value.inputDenominator * power) ==
      value.xDenominator * (value.inputNumerator - value.inputDenominator * power) &&
    value.xNumerator < value.xDenominator && value.terms == 8 &&
    value.lower < value.upper

def encode (value : Certificate) : List Nat :=
  [value.sourceIndex, value.inputNumerator, value.inputDenominator, value.shift,
    value.xNumerator, value.xDenominator, value.terms, value.lower, value.upper,
    value.scale]

def decode? : List Nat → Option Certificate
  | [sourceIndex, inputNumerator, inputDenominator, shift, xNumerator,
      xDenominator, terms, lower, upper, scale] =>
      let value : Certificate :=
        { sourceIndex, inputNumerator, inputDenominator, shift, xNumerator,
          xDenominator, terms, lower, upper, scale }
      if value.valid then some value else none
  | _ => none

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "pnt-log-rational.source" }
def logKey : OpKey := { name := "pnt-log-rational.log" }
def ruleKey : RuleKey := { name := "pnt-log-rational.atanh" }
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
      | .exact source =>
          match rowFor? source.sourceIndex with
          | some value =>
              if value.input == source then
                let outcome :=
                  .success [{ node := target, fact := .window value.window, payload }] []
                    { arithmeticWork := value.terms,
                      estimatedProofNodes := value.terms + 5 }
                { outcome := outcome,
                  drafts :=
                    [{ label := payload, role := .fact, schema := 1,
                       body := encode value }] }
              else { outcome := .noChange {}, drafts := [] }
          | none => { outcome := .noChange {}, drafts := [] }
      | _ => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }
def logPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[logOperation],
    handlers := #[Handler.statelessPlanned registration plan #[factFormat]] }
def packages : Array (Package Bound) := #[sourcePackage, logPackage]

def checkerInput (value : Certificate) : SemanticReplay.CheckerInput Bound :=
  { baseProgram := program, initialFacts := #[.exact value.input, .all],
    target := { node := node 1, fact := .window value.window } }

def representativeInput : SemanticReplay.CheckerInput Bound := checkerInput row32e12

def engineLimits : Propagator.Limits :=
  { maxOperations := 2, maxNodes := 2, maxRules := 1, maxRegistryEntries := 8,
    maxReplayFormats := 2, maxArity := 1, maxScopeNodes := 1, maxApplications := 2,
    maxQueueEntries := 8, maxActions := 4, maxMatcherVisits := 2,
    matcherBatchSize := 2, maxAcceptedFacts := 2, maxRetainedSuggestions := 0,
    maxEffort := 0, maxObservationValue := 64, maxDiagnosticValue := 512,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0, maxProposalItems := 1,
    maxInstances := 0, maxGeneration := 0, maxNodeDepth := 2, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 4 } }
def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8, maxTraversal := 32, maxLiveOffers := 8 }
def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4, maxBodyCells := 16, maxDrafts := 2, maxDraftCells := 16,
    maxAtom := 32000000000000, maxSchema := 1, maxUses := 2 }
def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.PntLogRational
