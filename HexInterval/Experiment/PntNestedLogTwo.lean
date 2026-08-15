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
# Source-pinned two-sided `log (log 2)` replay

The single log handler runs twice. It first converts the exact source fact for
`2` into a strict positive enclosure for `log 2`, then consumes precisely that
enclosure to produce the two-sided outer window.
-/

namespace Hex.Interval.Experiment.PntNestedLogTwo

open Propagator PayloadArena

inductive Bound where
  | all
  | two
  | innerWindow
  | zeroTouchingInner
  | outerWindow
  | empty
  deriving DecidableEq, Repr

namespace Bound

def code : Bound → Nat
  | .all => 0
  | .two => 1
  | .innerWindow => 2
  | .zeroTouchingInner => 3
  | .outerWindow => 4
  | .empty => 5

def ofCode? : Nat → Option Bound
  | 0 => some .all
  | 1 => some .two
  | 2 => some .innerWindow
  | 3 => some .zeroTouchingInner
  | 4 => some .outerWindow
  | 5 => some .empty
  | _ => none

end Bound

def factDomain : FactDomain Bound where
  top _ := .all
  narrow _ current proposed :=
    if current == proposed then .noChange
    else match current, proposed with
      | _, .all => .noChange
      | .all, proposed => .improved proposed
      | _, _ => .malformed 1

def real : DomainId := { index := 0 }
def sourceKey : OpKey := { name := "pnt-nested-log-two.source" }
def logKey : OpKey := { name := "pnt-nested-log-two.log" }
def ruleKey : RuleKey := { name := "pnt-nested-log-two.table" }
def sourceOperation : Operation := { key := sourceKey, inputs := [], output := real }
def logOperation : Operation := { key := logKey, inputs := [real], output := real }
def operations : Array Operation := #[sourceOperation, logOperation]
def node (index : Nat) : NodeId := { index }
def payload : PayloadId := { index := 0 }
def sourceInstruction : Node := { domain := real, op := { index := 0 }, args := [] }
def innerInstruction : Node := { domain := real, op := { index := 1 }, args := [node 0] }
def outerInstruction : Node := { domain := real, op := { index := 1 }, args := [node 1] }
def program : Program :=
  { operations, nodes := #[sourceInstruction, innerInstruction, outerInstruction] }

def registration : Registration :=
  { key := ruleKey, head := logKey, kind := .forward,
    watches := [.argument 0], writes := [.result] }

def factFormat : ReplayFormat :=
  { role := .fact, schema := 1, validateBody := fun body =>
      body == [Bound.innerWindow.code] || body == [Bound.outerWindow.code] }

def plan (request : RuleRequest Bound) : Plan Bound :=
  match request.inputs, request.writes with
  | [input], [target] =>
      let output? := match input.fact with
        | .two => some .innerWindow
        | .innerWindow => some .outerWindow
        | _ => none
      match output? with
      | some output =>
          { outcome :=
              .success [{ node := target, fact := output, payload }] []
                { arithmeticWork := 14, estimatedProofNodes := 20 },
            drafts :=
              [{ label := payload, role := .fact, schema := 1,
                 body := [output.code] }] }
      | none => { outcome := .noChange {}, drafts := [] }
  | _, _ => { outcome := .failed 1, drafts := [] }

def sourcePackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[sourceOperation], handlers := #[] }
def logPackage : Package Bound :=
  { Cache := Unit, cache := (), operations := #[logOperation],
    handlers := #[Handler.statelessPlanned registration plan #[factFormat]] }
def packages : Array (Package Bound) := #[sourcePackage, logPackage]

def checkerInput : SemanticReplay.CheckerInput Bound :=
  { baseProgram := program, initialFacts := #[.two, .all, .all],
    target := { node := node 2, fact := .outerWindow } }

def engineLimits : Propagator.Limits :=
  { maxOperations := 2, maxNodes := 4, maxRules := 1, maxRegistryEntries := 8,
    maxReplayFormats := 2, maxArity := 1, maxScopeNodes := 1, maxApplications := 3,
    maxQueueEntries := 12, maxActions := 8, maxMatcherVisits := 4,
    matcherBatchSize := 2, maxAcceptedFacts := 4, maxRetainedSuggestions := 0,
    maxEffort := 0, maxObservationValue := 20, maxDiagnosticValue := 300,
    maxOutcomeCandidates := 1, maxOutcomeSuggestions := 0, maxProposalItems := 1,
    maxInstances := 0, maxGeneration := 0, maxNodeDepth := 3, maxEqualities := 0,
    splitEndpointLimit := { maxEndpointHeight := 8, maxAlignmentShift := 4 } }
def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 12, maxTraversal := 48, maxLiveOffers := 12 }
def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4, maxBodyCells := 4, maxDrafts := 2, maxDraftCells := 2,
    maxAtom := 8, maxSchema := 1, maxUses := 4 }
def limits : PolicySession.Limits :=
  { engine := engineLimits, policy := policyLimits, arena := arenaLimits }

end Hex.Interval.Experiment.PntNestedLogTwo
