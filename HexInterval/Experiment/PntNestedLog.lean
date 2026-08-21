/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.PolicySession

@[expose] public section

/-!
# Mathlib-free nested-logarithm replay probe

This package is a source-pinned acceptance vertical for PNT+'s
`LogTables.log_log_6_58_gt`.  One logarithm handler is registered over a
three-node `log (log 6.58)` graph.  It first turns the exact rational input
fact into a strict positive inner enclosure and then consumes that enclosure
to produce the outer lower bound.

The facts remain a finite package-owned table.  In particular this probe does
not claim an arbitrary-rational logarithm algorithm; it isolates repeated
planning, dependency capture, domain rejection, and chronological replay.
-/

namespace Hex.Interval.Experiment.PntNestedLog

open Propagator PayloadArena

/-- The finite closure of intervals needed by the nested-logarithm probe.
`positiveSlice` exists so `meet` remains an exact intersection for the
zero-touching domain mutation. -/
inductive Bound where
  | all
  | six58
  | innerWindow
  | zeroTouchingInner
  | nestedLower
  | positiveSlice
  | empty
  deriving DecidableEq, Repr

namespace Bound

/-- Exact intersection for the probe's finite real-set lattice. -/
def meet : Bound → Bound → Bound
  | .empty, _ | _, .empty => .empty
  | .all, right => right
  | left, .all => left
  | .six58, .six58 | .six58, .nestedLower |
      .nestedLower, .six58 => .six58
  | .six58, _ | _, .six58 => .empty
  | .innerWindow, .innerWindow | .innerWindow, .zeroTouchingInner |
      .zeroTouchingInner, .innerWindow | .innerWindow, .nestedLower |
      .nestedLower, .innerWindow | .innerWindow, .positiveSlice |
      .positiveSlice, .innerWindow => .innerWindow
  | .zeroTouchingInner, .zeroTouchingInner => .zeroTouchingInner
  | .zeroTouchingInner, .nestedLower | .nestedLower, .zeroTouchingInner |
      .zeroTouchingInner, .positiveSlice | .positiveSlice, .zeroTouchingInner |
      .nestedLower, .positiveSlice | .positiveSlice, .nestedLower |
      .positiveSlice, .positiveSlice => .positiveSlice
  | .nestedLower, .nestedLower => .nestedLower

def code : Bound → Nat
  | .all => 0
  | .six58 => 1
  | .innerWindow => 2
  | .zeroTouchingInner => 3
  | .nestedLower => 4
  | .positiveSlice => 5
  | .empty => 6

def ofCode? : Nat → Option Bound
  | 0 => some .all
  | 1 => some .six58
  | 2 => some .innerWindow
  | 3 => some .zeroTouchingInner
  | 4 => some .nestedLower
  | 5 => some .positiveSlice
  | 6 => some .empty
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

def sourceKey : OpKey := { name := "pnt-nested-log.source" }
def logKey : OpKey := { name := "pnt-nested-log.log" }
def logRuleKey : RuleKey := { name := "pnt-nested-log.table" }

def sourceOperation : Operation :=
  { key := sourceKey, inputs := [], output := real }

def logOperation : Operation :=
  { key := logKey, inputs := [real], output := real }

def operations : Array Operation := #[sourceOperation, logOperation]

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def sourceInstruction : Node :=
  { domain := real, op := { index := 0 }, args := [] }

def innerInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 0] }

def outerInstruction : Node :=
  { domain := real, op := { index := 1 }, args := [node 1] }

/-- Caller graph for `Real.log (Real.log 6.58)`. -/
def program : Program :=
  { operations, nodes := #[sourceInstruction, innerInstruction, outerInstruction] }

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
      | [code] =>
          Bound.ofCode? code == some .innerWindow ||
            Bound.ofCode? code == some .nestedLower
      | _ => false }

/-- The same handler performs both table steps.  The outer step deliberately
requires the strict positive inner fact; an enclosure containing zero is
domain-unknown and produces no proposal. -/
def logPlan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      let output? :=
        match input.fact with
        | .six58 => some .innerWindow
        | .innerWindow => some .nestedLower
        | _ => none
      match output? with
      | some output =>
          { outcome :=
              .success
                [{ node := target, fact := output, payload := payload 0 }]
                [] { arithmeticWork := 1, estimatedProofNodes := 1 }
            drafts :=
              [{ label := payload 0
                 role := .fact
                 schema := 1
                 body := [output.code] }] }
      | none => { outcome := .noChange {}, drafts := [] }
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

def engineLimits : Hex.Interval.State.Limits :=
  { maxOperations := 2
    maxNodes := 4
    maxRules := 1
    maxRegistryEntries := 8
    maxReplayFormats := 2
    maxArity := 1
    maxScopeNodes := 1
    maxApplications := 3
    maxQueueEntries := 12
    maxActions := 8
    maxMatcherVisits := 4
    matcherBatchSize := 2
    maxAcceptedFacts := 4
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 8
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 1
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := 3
    maxEqualities := 0
    splitEndpointLimit :=
      { maxEndpointHeight := 8, maxAlignmentShift := 4 } }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 12
    maxTraversal := 48
    maxLiveOffers := 12 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4
    maxBodyCells := 4
    maxDrafts := 2
    maxDraftCells := 2
    maxAtom := 8
    maxSchema := 1
    maxUses := 4 }

def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

def start : Except PolicySession.StartError (PolicySession.Session Bound) :=
  PolicySession.Session.start factDomain program packages
    #[.six58, .all, .all] limits

end Hex.Interval.Experiment.PntNestedLog
