/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Mathlib-free PNT+ logarithm-table probe

This package is a deliberately small acceptance vertical for the first two
entries of PNT+'s pinned `LogTables.lean`: the lower and upper bounds on
`log 2`.  The executable side knows neither real logarithms nor decimal
semantics.  It only propagates a package-owned finite fact from an exact-input
fact.  `HexIntervalMathlib` supplies and checks the mathematical meaning.

The finite fact domain is intentionally local to the probe.  It demonstrates
the generic watched-input planning and replay boundary without pretending to
be the eventual arbitrary-precision dyadic logarithm package.
-/

namespace Hex.Interval.Experiment.PntLogTable

open Propagator PayloadArena

/-- Facts needed by the source-pinned `log 2` acceptance probe. -/
inductive Bound where
  | all
  | two
  | logTwoWindow
  | empty
  deriving DecidableEq, Repr

namespace Bound

/-- Exact intersection for the probe's finite fact lattice. -/
def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .two, .two => .two
  | .logTwoWindow, .logTwoWindow => .logTwoWindow
  | .two, .logTwoWindow | .logTwoWindow, .two => .empty

def code : Bound → Nat
  | .all => 0
  | .two => 1
  | .logTwoWindow => 2
  | .empty => 3

def ofCode? : Nat → Option Bound
  | 0 => some .all
  | 1 => some .two
  | 2 => some .logTwoWindow
  | 3 => some .empty
  | _ => none

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    let installed := current.meet proposed
    if installed == current then .noChange
    else if installed == .empty then .contradiction installed
    else .improved installed

def real : DomainId := { index := 0 }

def sourceKey : OpKey := { name := "pnt-log-table.source" }
def logKey : OpKey := { name := "pnt-log-table.log" }
def logRuleKey : RuleKey := { name := "pnt-log-table.log-two" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def logOperation : Operation :=
  { key := logKey, inputs := [real], output := real }

def operations : Array Operation := #[sourceOperation, logOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }

def logInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

/-- Caller graph for the closed expression `Real.log 2`. -/
def program : Program :=
  { operations, nodes := #[sourceInstruction, logInstruction] }

def logRule : Registration :=
  { key := logRuleKey
    head := logKey
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body =>
      match body with
      | [code] => Bound.ofCode? code == some .logTwoWindow
      | _ => false }

/-- The source-pinned table entry applies only when the watched input is
known to be exactly two. -/
def logPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      if input.fact == .two then
        { outcome :=
            .success
              [{ node := target, fact := .logTwoWindow, payload := payload 0 }]
              [] { arithmeticWork := 1, estimatedProofNodes := 1 }
          drafts :=
            [{ label := payload 0
               role := .fact
               schema := 1
               body := [Bound.logTwoWindow.code] }] }
      else
        { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation]
    handlers := #[] }

def logPackage : Package Bound :=
  { Cache := Unit
    cache := ()
    operations := #[logOperation]
    handlers := #[Handler.statelessPlanned logRule logPlan #[factFormat]] }

def packages : Array (Package Bound) := #[sourcePackage, logPackage]

def engineLimits : Propagator.Limits :=
  { maxOperations := 2
    maxNodes := 3
    maxRules := 1
    maxRegistryEntries := 8
    maxReplayFormats := 2
    maxArity := 1
    maxScopeNodes := 1
    maxApplications := 2
    maxQueueEntries := 8
    maxActions := 4
    maxMatcherVisits := 2
    matcherBatchSize := 2
    maxAcceptedFacts := 2
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 8
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 1
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 2
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 8, maxAlignmentShift := 4 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 8
    maxTraversal := 32
    maxLiveOffers := 8 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4
    maxBodyCells := 4
    maxDrafts := 2
    maxDraftCells := 2
    maxAtom := 8
    maxSchema := 1
    maxUses := 2 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages #[.two, .all] limits

end Hex.Interval.Experiment.PntLogTable
