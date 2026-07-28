/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PayloadSession

/-!
Focused checks for package invocation, payload freezing, and engine admission
under one private session boundary.
-/

namespace Hex.Interval.PayloadSessionConformance

open Experiment Propagator PayloadArena PayloadSession

def real : DomainId := { index := 0 }
def sourceOp : OpKey := { name := "payload-session.source" }
def mysteryOp : OpKey := { name := "payload-session.mystery" }

def goodKey : RuleKey := { name := "payload-session.mystery.good" }
def badReplyKey : RuleKey := { name := "payload-session.mystery.bad-reply" }
def badPayloadKey : RuleKey := { name := "payload-session.mystery.bad-payload" }
def bareKey : RuleKey := { name := "payload-session.mystery.bare" }
def negativeKey : RuleKey := { name := "payload-session.mystery.negative" }
def failedKey : RuleKey := { name := "payload-session.mystery.failed" }
def retryKey : RuleKey := { name := "payload-session.mystery.retry" }

def sourceOperation : Operation :=
  { key := sourceOp, inputs := [], output := real }

def mysteryOperation : Operation :=
  { key := mysteryOp, inputs := [real], output := real }

def node (index : Nat) : NodeId := { index }
def payload (index : Nat) : PayloadId := { index }

def instruction (operation : Nat) (args : List NodeId := []) : Node :=
  { domain := real, op := { index := operation }, args }

/-- Two applications intentionally reuse the same package-local payload label. -/
def program : Program :=
  { operations := #[sourceOperation, mysteryOperation]
    nodes :=
      #[instruction 0,
        instruction 1 [node 0],
        instruction 1 [node 0]] }

def registration (key : RuleKey) : Registration :=
  { key
    head := mysteryOp
    kind := .forward
    watches := [.argument 0]
    writes := [.result] }

def factDomain : FactDomain Nat where
  top _ := 0
  narrow _ current proposed :=
    if current < proposed then .improved proposed else .noChange

def limits : Propagator.Limits :=
  { maxOperations := 4
    maxNodes := 4
    maxRules := 2
    maxArity := 2
    maxApplications := 4
    maxQueueEntries := 8
    maxActions := 8
    maxAcceptedFacts := 4
    maxRetainedSuggestions := 2
    maxEffort := 2
    maxObservationValue := 8
    maxDiagnosticValue := 300
    maxOutcomeCandidates := 2
    maxOutcomeSuggestions := 2
    maxProposalItems := 2
    maxInstances := 2
    maxGeneration := 2
    maxEqualities := 2
    splitEndpointLimit :=
      { maxEndpointHeight := 8
        maxAlignmentShift := 8 } }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 4
    maxBodyCells := 8
    maxAtom := 100
    maxSchema := 10
    maxUses := 4 }

def goodPlan (request : RuleRequest Nat) : Plan Nat :=
  match request.writes with
  | [target] =>
      { outcome :=
          .success
            [{ node := target, fact := 7, payload := payload 700 }]
            [] { estimatedProofNodes := 1 }
        drafts :=
          [{ label := payload 700
             role := .fact
             schema := 1
             body := [request.action.node.index, 99] }] }
  | _ => { outcome := .failed 1, drafts := [] }

def goodPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration goodKey) goodPlan] }

def badReplyPlan (_request : RuleRequest Nat) : Plan Nat :=
  { outcome :=
      .success
        [{ node := node 0, fact := 9, payload := payload 700 }]
        [] {}
    drafts := [{ label := payload 700, role := .fact, schema := 1, body := [1] }] }

def badReplyPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration badReplyKey) badReplyPlan] }

def badPayloadPlan (request : RuleRequest Nat) : Plan Nat :=
  match request.writes with
  | [target] =>
      { outcome :=
          .success
            [{ node := target, fact := 7, payload := payload 700 }]
            [] {}
        drafts := [{ label := payload 701, role := .fact, schema := 1, body := [1] }] }
  | _ => { outcome := .failed 2, drafts := [] }

def badPayloadPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration badPayloadKey) badPayloadPlan] }

def barePackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.stateless (registration bareKey) fun request =>
          match request.writes with
          | [target] =>
              .success
                [{ node := target, fact := 7, payload := payload 700 }]
                [] {}
          | _ => .failed 3] }

def negativePackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.stateless (registration negativeKey) fun _ => .noChange {}] }

def failedPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.stateless (registration failedKey) fun _ => .failed 4] }

def retryPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.stateless (registration retryKey) fun _ =>
          .success [] [.retry 1] {}] }

def start (package : Package Nat)
    (payloadLimits : PayloadArena.Limits := arenaLimits) :
    Except PayloadSession.StartError (PayloadSession.Session Nat) :=
  PayloadSession.Session.start factDomain program #[package] #[3, 0, 0]
    limits payloadLimits

def goodRun? : Option (PayloadSession.Run Nat) :=
  match start goodPackage with
  | .ok session => some (session.drive 8)
  | .error _ => none

-- Separate replies may use the same local label; the session commits distinct
-- arena entries and only relocated global identifiers reach provenance.
#guard
  match goodRun? with
  | some run =>
      run.stop == .saturated &&
        run.session.live && !run.session.incomplete &&
        run.session.arena.entries.size == 2 &&
        run.session.arena.bodyCells == 4 &&
        run.session.engine.history.size == 2 &&
        match run.session.engine.history[0]?, run.session.engine.history[1]?,
            run.session.arena.entry? (payload 0) .fact,
            run.session.arena.entry? (payload 1) .fact with
        | some first, some second, some firstEntry, some secondEntry =>
            first.node == node 1 && second.node == node 2 &&
              firstEntry.origin.key == goodKey && secondEntry.origin.key == goodKey &&
              firstEntry.origin.node == node 1 && secondEntry.origin.node == node 2 &&
              firstEntry.schema == 1 && secondEntry.schema == 1 &&
              firstEntry.body == [1, 99] && secondEntry.body == [2, 99] &&
              match first.cause, second.cause with
              | .rule _ proposed firstPayload, .rule _ proposed' secondPayload =>
                  proposed == 7 && proposed' == 7 &&
                    firstPayload == payload 0 && secondPayload == payload 1
              | _, _ => false
        | _, _, _, _ => false
  | none => false

-- A fully frozen prospective arena is discarded when engine admission rejects
-- an undeclared write.
#guard
  match start badReplyPackage with
  | .ok session =>
      match session.advance with
      | .invalidReply (.undeclaredWrite target) next =>
          target == node 0 && next.arena.entries.isEmpty &&
            next.engine.history.isEmpty && next.engine.pending.isNone &&
            !next.live &&
            (next.registry.packages[0]?).any fun package =>
              package.invocations == 1 &&
                match next.advance with
                | .invalidEngine stopped => !stopped.live
                | _ => false
      | _ => false
  | .error _ => false

-- Malformed reply-local evidence clears the request latch but changes no
-- semantic state.
#guard
  match start badPayloadPackage with
  | .ok session =>
      match session.advance with
      | .invalidPayload (.danglingReference label) next =>
          label == payload 700 && next.arena.entries.isEmpty &&
            next.engine.history.isEmpty && next.engine.pending.isNone &&
            !next.live &&
            (next.registry.packages[0]?).any fun package =>
              package.invocations == 1
      | _ => false
  | .error _ => false

-- Arena exhaustion is typed, prospective, and atomic.
#guard
  match start goodPackage { arenaLimits with maxEntries := 0 } with
  | .ok session =>
      match session.advance with
      | .payloadResource .entries next =>
          next.arena.entries.isEmpty && next.engine.history.isEmpty &&
            next.engine.pending.isNone && !next.live
      | _ => false
  | .error _ => false

-- Compatibility handlers are safe for negative observations. A positive
-- outcome carrying an unfrozen identifier is rejected rather than retained.
#guard
  match start negativePackage with
  | .ok session =>
      let run := session.drive 8
      run.stop == .saturated && run.session.arena.entries.isEmpty &&
        run.session.engine.history.isEmpty && !run.session.incomplete
  | .error _ => false

#guard
  match start barePackage with
  | .ok session =>
      match session.advance with
      | .invalidPayload (.danglingReference label) next =>
          label == payload 700 && next.arena.entries.isEmpty &&
            next.engine.history.isEmpty
      | _ => false
  | .error _ => false

-- A package failure and an unprocessed narrowing suggestion can never be
-- laundered into a complete propagation fixed point.
#guard
  match start failedPackage with
  | .ok session =>
      let run := session.drive 8
      run.stop == .incomplete && run.session.incomplete &&
        run.session.arena.entries.isEmpty
  | .error _ => false

#guard
  match start retryPackage with
  | .ok session =>
      let run := session.drive 8
      run.stop == .incomplete && !run.session.incomplete &&
        run.session.engine.suggestions.size == 2
  | .error _ => false

end Hex.Interval.PayloadSessionConformance
