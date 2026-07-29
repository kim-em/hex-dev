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
def longCandidatesKey : RuleKey := { name := "payload-session.mystery.long-candidates" }
def longSuggestionsKey : RuleKey := { name := "payload-session.mystery.long-suggestions" }
def nestedKey : RuleKey := { name := "payload-session.mystery.nested-instance" }
def nestedUsesKey : RuleKey := { name := "payload-session.mystery.nested-uses" }
def atomKey : RuleKey := { name := "payload-session.mystery.atom" }
def schemaKey : RuleKey := { name := "payload-session.mystery.schema" }
def draftsKey : RuleKey := { name := "payload-session.mystery.drafts" }
def bodyKey : RuleKey := { name := "payload-session.mystery.body" }
def overflowKey : RuleKey := { name := "payload-session.mystery.overflow" }
def recoverKey : RuleKey := { name := "payload-session.mystery.recover" }
def lateExtraKey : RuleKey := { name := "payload-session.mystery.late-extra" }

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

def contradictionDomain : FactDomain Nat where
  top _ := 0
  narrow _ _ proposed := .contradiction proposed

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
    maxNodeDepth := 16
    maxEqualities := 2
    splitEndpointLimit :=
      { maxEndpointHeight := 8
        maxAlignmentShift := 8 } }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 8
    maxBodyCells := 16
    maxDrafts := 8
    maxDraftCells := 8
    maxAtom := 100
    maxSchema := 10
    maxUses := 8 }

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

def lateExtraPlan (request : RuleRequest Nat) : Plan Nat :=
  if request.action.node == node 1 then
    goodPlan request
  else
    match request.writes with
    | [target] =>
        { outcome :=
            .success
              [{ node := target, fact := 7, payload := payload 700 }]
              [] {}
          drafts :=
            [{ label := payload 700
               role := .fact
               schema := 1
               body := [request.action.node.index, 99] },
             { label := payload 701
               role := .fact
               schema := 1
               body := [4, 5] }] }
    | _ => { outcome := .failed 1, drafts := [] }

def lateExtraPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration lateExtraKey) lateExtraPlan] }

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
      #[Handler.statelessDroppingDrafts (registration bareKey) fun request =>
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
      #[Handler.statelessDroppingDrafts (registration negativeKey) fun _ => .noChange {}] }

def failedPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessDroppingDrafts (registration failedKey) fun _ => .failed 4] }

def retryPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessDroppingDrafts (registration retryKey) fun _ =>
          .success [] [.retry 1] {}] }

def longCandidatesPlan (request : RuleRequest Nat) : Plan Nat :=
  match request.writes with
  | [target] =>
      { outcome :=
          .success
            [{ node := target, fact := 4, payload := payload 1 },
              { node := target, fact := 5, payload := payload 1 },
              { node := target, fact := 6, payload := payload 1 }]
            [] {}
        -- This deliberately malformed evidence must never be traversed:
        -- engine list pre-screening rejects the outcome first.
        drafts := [] }
  | _ => { outcome := .failed 5, drafts := [] }

def longCandidatesPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration longCandidatesKey) longCandidatesPlan] }

def longSuggestionsPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration longSuggestionsKey) fun _ =>
          { outcome := .success [] [.retry 0, .retry 1, .retry 2] {}
            drafts := [] }] }

def nestedPlan (request : RuleRequest Nat) : Plan Nat :=
  { outcome :=
      .success []
        [.instantiate
          { key := 44
            nodes :=
              [{ domain := real
                 op := { index := 1 }
                 args := [.existing request.action.node] }]
            equalities :=
              [{ left := .existing (node 0)
                 right := .proposed 0
                 payload := payload 702 }]
            payload := payload 701 }]
        {}
    drafts :=
      [{ label := payload 702, role := .equality, schema := 3, body := [12] },
        { label := payload 701, role := .instance, schema := 2, body := [11] }] }

def nestedPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration nestedKey) nestedPlan] }

def nestedUsesPlan (request : RuleRequest Nat) : Plan Nat :=
  { outcome :=
      .success []
        [.instantiate
          { key := 45
            nodes := []
            equalities :=
              [{ left := .existing (node 0)
                 right := .existing request.action.node
                 payload := payload 702 },
               { left := .existing (node 0)
                 right := .existing request.action.node
                 payload := payload 703 }]
            payload := payload 701 }]
        {}
    drafts :=
      [{ label := payload 702, role := .equality, schema := 3, body := [12] },
       { label := payload 703, role := .equality, schema := 3, body := [13] },
       { label := payload 701, role := .instance, schema := 2, body := [11] }] }

def nestedUsesPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration nestedUsesKey) nestedUsesPlan] }

def draftPlan (schema : Nat) (body : List Nat)
    (request : RuleRequest Nat) : Plan Nat :=
  match request.writes with
  | [target] =>
      { outcome :=
          .success
            [{ node := target, fact := 7, payload := payload 700 }]
            [] {}
        drafts := [{ label := payload 700, role := .fact, schema, body }] }
  | _ => { outcome := .failed 6, drafts := [] }

def atomPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration atomKey) (draftPlan 1 [101])] }

def schemaPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration schemaKey) (draftPlan 11 [1])] }

def bodyPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration bodyKey)
          (draftPlan 1 [1, 1, 1, 1, 1, 1, 1, 1, 1])] }

def recoverPlan (request : RuleRequest Nat) : Plan Nat :=
  if request.action.node == node 1 then
    draftPlan 11 [1] request
  else
    goodPlan request

def recoverPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration recoverKey) recoverPlan] }

def excessDrafts : List PayloadArena.Draft :=
  [{ label := payload 0, role := .fact, schema := 1, body := [] },
   { label := payload 1, role := .fact, schema := 1, body := [] },
   { label := payload 2, role := .fact, schema := 1, body := [] },
   { label := payload 3, role := .fact, schema := 1, body := [] },
   { label := payload 4, role := .fact, schema := 1, body := [] },
   { label := payload 5, role := .fact, schema := 1, body := [] },
   { label := payload 6, role := .fact, schema := 1, body := [] },
   { label := payload 7, role := .fact, schema := 1, body := [] },
   { label := payload 8, role := .fact, schema := 1, body := [] }]

def draftsPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration draftsKey) fun _ =>
          { outcome := .noChange {}, drafts := excessDrafts }] }

def overflowPlan (request : RuleRequest Nat) : Plan Nat :=
  { outcome :=
      .success []
        [.split { node := request.action.node, point := 0, reason := .midpoint },
         .split { node := request.action.node, point := 1, reason := .midpoint },
         .retry 1] {}
    drafts := [] }

def overflowPackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration overflowKey) overflowPlan] }

def arenaAwarePackage : Package Nat :=
  { Cache := Unit
    cache := ()
    operations := #[sourceOperation, mysteryOperation]
    handlers :=
      #[Handler.statelessPlanned (registration goodKey) goodPlan]
    acceptsLimits := fun _ _ payloadLimits =>
      4 ≤ payloadLimits.maxEntries && 8 ≤ payloadLimits.maxUses &&
        8 ≤ payloadLimits.maxDraftCells }

def start (package : Package Nat)
    (payloadLimits : PayloadArena.Limits := arenaLimits) :
    Except PayloadSession.StartError (PayloadSession.Session Nat) :=
  PayloadSession.Session.start factDomain program #[package] #[3, 0, 0]
    limits payloadLimits

def startWithin (package : Package Nat) (engineLimits : Propagator.Limits)
    (payloadLimits : PayloadArena.Limits) :
    Except PayloadSession.StartError (PayloadSession.Session Nat) :=
  PayloadSession.Session.start factDomain program #[package] #[3, 0, 0]
    engineLimits payloadLimits

def oneReplyLimits : Propagator.Limits :=
  { limits with
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 0 }

def twoUseLimits : Propagator.Limits :=
  { oneReplyLimits with maxOutcomeCandidates := 2 }

def lateExtraArena : PayloadArena.Limits :=
  { arenaLimits with
    maxEntries := 2
    maxBodyCells := 4
    maxDrafts := 2
    maxDraftCells := 4
    maxUses := 2 }

def nestedUsesLimits : Propagator.Limits :=
  { limits with
    maxOutcomeCandidates := 0
    maxOutcomeSuggestions := 1
    maxProposalItems := 1 }

def nestedUsesArena : PayloadArena.Limits :=
  { arenaLimits with
    maxDrafts := PayloadSession.requiredUses nestedUsesLimits
    maxUses := PayloadSession.requiredUses nestedUsesLimits }

def overflowLimits : Propagator.Limits :=
  { limits with maxOutcomeSuggestions := 3 }

def overflowArenaLimits : PayloadArena.Limits :=
  let required := PayloadSession.requiredUses overflowLimits
  { arenaLimits with
    maxEntries := required
    maxDrafts := required
    maxUses := required }

def oversizedProgram : Program :=
  { program with
    nodes := program.nodes.push (instruction 1 [node 0]) |>.push (instruction 1 [node 0]) }

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
        run.session.live && !run.session.droppedWork && run.session.complete &&
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
-- semantic state. It becomes an ordinary failed rule transition: the session
-- remains live, remembers dropped work, and the bounded driver continues.
#guard
  match start badPayloadPackage with
  | .ok session =>
      match session.advance with
      | .invalidPayload (.danglingReference label) next =>
          label == payload 700 && next.arena.entries.isEmpty &&
            next.engine.history.isEmpty && next.engine.pending.isNone &&
            next.live && next.droppedWork && !next.complete &&
            next.engine.metrics.ruleFailures == 1 &&
            (next.registry.packages[0]?).any fun package =>
              package.invocations == 1 &&
                let run := next.drive 8
                run.stop == .incomplete && run.session.live &&
                  run.session.droppedWork && !run.session.complete &&
                  run.session.engine.metrics.ruleFailures == 2
      | _ => false
  | .error _ => false

-- Per-reply encoding excess is a package failure, not exhaustion of the
-- whole run. The prospective arena is discarded, the request is consumed,
-- and independent work can continue, but completeness is permanently lost.
#guard
  match start atomPackage
      { arenaLimits with maxBodyCells := 0, maxDraftCells := 0 } with
  | .ok session =>
      match session.advance with
      | .rejectedPayload .atom next =>
          next.arena.entries.isEmpty && next.engine.history.isEmpty &&
            next.engine.pending.isNone && next.live && next.droppedWork &&
            !next.complete && next.engine.metrics.ruleFailures == 1 &&
            let run := next.drive 8
            run.stop == .incomplete && run.session.live &&
              run.session.engine.metrics.ruleFailures == 2
      | _ => false
  | .error _ => false

#guard
  match start schemaPackage with
  | .ok session =>
      match session.advance with
      | .rejectedPayload .schema next =>
          next.arena.entries.isEmpty && next.engine.history.isEmpty &&
            next.engine.pending.isNone && next.live && next.droppedWork &&
            !next.complete && next.engine.metrics.ruleFailures == 1
      | _ => false
  | .error _ => false

#guard
  match start draftsPackage with
  | .ok session =>
      match session.advance with
      | .rejectedPayload .drafts next =>
          next.arena.entries.isEmpty && next.engine.history.isEmpty &&
            next.engine.pending.isNone && next.live && next.droppedWork &&
            !next.complete && next.engine.metrics.ruleFailures == 1
      | _ => false
  | .error _ => false

-- A nested equality beyond the engine-coherent proposal envelope is charged
-- as a payload use before engine admission. The failed reply is recoverable.
#guard
  match startWithin nestedUsesPackage nestedUsesLimits nestedUsesArena with
  | .ok session =>
      match session.advance with
      | .rejectedPayload .uses next =>
          next.arena.entries.isEmpty && next.engine.history.isEmpty &&
            next.engine.pending.isNone && next.live && next.droppedWork &&
            !next.complete && next.engine.metrics.ruleFailures == 1
      | _ => false
  | .error _ => false

-- One oversized encoded body is a package-local failure rather than
-- exhaustion of the cumulative arena.
#guard
  match start bodyPackage with
  | .ok session =>
      match session.advance with
      | .rejectedPayload .draftCells next =>
          next.arena.entries.isEmpty && next.engine.history.isEmpty &&
            next.engine.pending.isNone && next.live && next.droppedWork &&
            !next.complete && next.engine.metrics.ruleFailures == 1
      | _ => false
  | .error _ => false

-- Rejection does not stop unrelated queued work, and the monotone
-- incompleteness flag survives a later successful arena and fact commit.
#guard
  match start recoverPackage with
  | .ok session =>
      match session.advance with
      | .rejectedPayload .schema rejected =>
          match rejected.advance with
          | .advanced next =>
              next.live && next.droppedWork && !next.complete &&
                next.engine.metrics.ruleFailures == 1 &&
                next.engine.history.size == 1 &&
                next.arena.entries.size == 1 && next.arena.bodyCells == 2 &&
                match next.engine.history[0]? with
                | some event =>
                    event.node == node 2 &&
                      let run := next.drive 8
                      run.stop == .incomplete && run.session.live &&
                        run.session.droppedWork && !run.session.complete &&
                        run.session.engine.history.size == 1
                | none => false
          | _ => false
      | _ => false
  | .error _ => false

-- Whole-run exhaustion is reserved for a bounded reply which would fit an
-- empty arena but not the capacity remaining after an earlier commit.
#guard
  match startWithin goodPackage oneReplyLimits
      { arenaLimits with maxEntries := 1, maxDrafts := 1, maxUses := 1 } with
  | .ok session =>
      match session.advance with
      | .advanced first =>
          first.arena.entries.size == 1 && first.engine.history.size == 1 &&
            match first.advance with
            | .payloadResource .entries stopped =>
                !stopped.live && !stopped.complete &&
                  stopped.engine.pending.isNone &&
                  stopped.arena.entries.size == 1 &&
                  stopped.engine.history.size == 1 &&
                  match stopped.advance with
                  | .invalidEngine inert =>
                      !inert.live && !inert.complete &&
                        inert.arena.entries.size == 1 &&
                        inert.engine.history.size == 1
                  | _ => false
            | _ => false
      | _ => false
  | .error _ => false

#guard
  match startWithin goodPackage oneReplyLimits
      { arenaLimits with
        maxEntries := 2
        maxBodyCells := 3
        maxDrafts := 1
        maxDraftCells := 2
        maxUses := 1 } with
  | .ok session =>
      match session.advance with
      | .advanced first =>
          first.arena.bodyCells == 2 && first.engine.history.size == 1 &&
            match first.advance with
            | .payloadResource .bodyCells stopped =>
                !stopped.live && !stopped.complete &&
                  stopped.engine.pending.isNone &&
                  stopped.arena.entries.size == 1 &&
                  stopped.arena.bodyCells == 2 &&
                  stopped.engine.history.size == 1 &&
                  match stopped.advance with
                  | .invalidEngine inert =>
                      !inert.live && !inert.complete &&
                        inert.arena.entries.size == 1 &&
                        inert.arena.bodyCells == 2 &&
                        inert.engine.history.size == 1
                  | _ => false
            | _ => false
      | _ => false
  | .error _ => false

-- After an earlier valid commit has partly filled both cumulative budgets, an
-- extra draft with a junk body is still malformed local evidence. Exact
-- coverage precedes remaining-capacity checks, so only this reply is rejected.
#guard
  match startWithin lateExtraPackage twoUseLimits lateExtraArena with
  | .ok session =>
      match session.advance with
      | .advanced first =>
          first.arena.entries.size == 1 && first.arena.bodyCells == 2 &&
            first.engine.history.size == 1 &&
            match first.advance with
            | .invalidPayload (.extraDraft label) rejected =>
                label.index == 701 && rejected.live && rejected.droppedWork &&
                  !rejected.complete && rejected.arena.entries.size == 1 &&
                  rejected.arena.bodyCells == 2 &&
                  rejected.engine.history.size == 1 &&
                  rejected.engine.metrics.ruleFailures == 1
            | _ => false
      | _ => false
  | .error _ => false

-- Completeness uses the engine's exact retained-prefix calculation. Here the
-- two harmless splits fit, while a closure-relevant retry is the one item
-- dropped by the cap.
#guard
  match PayloadSession.Session.start factDomain program #[overflowPackage]
      #[3, 0, 0] overflowLimits overflowArenaLimits with
  | .ok session =>
      match session.advance with
      | .advanced next =>
          next.engine.suggestions.size == 2 &&
            next.engine.metrics.droppedSuggestions == 1 &&
            next.droppedWork && !next.complete
      | _ => false
  | .error _ => false

-- Compatibility handlers are safe for negative observations. A positive
-- outcome carrying an unfrozen identifier is rejected rather than retained.
#guard
  match start negativePackage with
  | .ok session =>
      let run := session.drive 8
      run.stop == .saturated && run.session.arena.entries.isEmpty &&
        run.session.engine.history.isEmpty && !run.session.droppedWork &&
        run.session.complete
  | .error _ => false

#guard
  match start barePackage with
  | .ok session =>
      match session.advance with
      | .invalidPayload (.danglingReference label) next =>
          label == payload 700 && next.arena.entries.isEmpty &&
            next.engine.history.isEmpty && next.live && next.droppedWork &&
            !next.complete && next.engine.metrics.ruleFailures == 1
      | _ => false
  | .error _ => false

-- A package failure and an unprocessed narrowing suggestion can never be
-- laundered into a complete propagation fixed point.
#guard
  match start failedPackage with
  | .ok session =>
      let run := session.drive 8
      run.stop == .incomplete && run.session.droppedWork &&
        !run.session.complete && run.session.arena.entries.isEmpty
  | .error _ => false

#guard
  match start retryPackage with
  | .ok session =>
      let run := session.drive 8
      run.stop == .incomplete && !run.session.droppedWork &&
        !run.session.complete && run.session.engine.suggestions.size == 2
  | .error _ => false

-- Count coherence lets every engine-valid payload use own a distinct draft,
-- bounds malformed draft lists by the use envelope, and fits either local cap
-- in a fresh arena. `requiredUses ≤ maxUses` follows transitively rather than
-- appearing as a redundant condition. Packages may impose stronger bounds.
#guard
  PayloadSession.requiredUses limits == 8 &&
    PayloadSession.limitsCoherent limits arenaLimits

#guard
  match start goodPackage { arenaLimits with maxDrafts := 7 } with
  | .error .incoherentLimits => true
  | _ => false

-- This isolates `maxDrafts ≤ maxUses`: both still admit all eight required
-- uses, and the fresh entry budget admits all nine locally allowed drafts.
#guard
  match start goodPackage
      { arenaLimits with maxEntries := 9, maxDrafts := 9, maxUses := 8 } with
  | .error .incoherentLimits => true
  | _ => false

#guard
  match start goodPackage { arenaLimits with maxEntries := 7 } with
  | .error .incoherentLimits => true
  | _ => false

#guard
  match start goodPackage { arenaLimits with maxBodyCells := 7 } with
  | .error .incoherentLimits => true
  | _ => false

#guard
  match start arenaAwarePackage { arenaLimits with maxDraftCells := 7 } with
  | .error .limitsRejected => true
  | _ => false

-- Generic engine bounds precede package-specific scans of the program.
#guard
  match PayloadSession.Session.start factDomain oversizedProgram #[arenaAwarePackage]
      #[3, 0, 0, 0, 0] limits { arenaLimits with maxDraftCells := 7 } with
  | .error (.engine (.resourceLimit .nodes)) => true
  | _ => false

-- Oversized outer lists are rejected by the engine before malformed or
-- absent drafts can make the arena traverse the package plan.
#guard
  match start longCandidatesPackage with
  | .ok session =>
      match session.advance with
      | .invalidReply .tooManyCandidates next =>
          next.arena.entries.isEmpty && next.engine.pending.isNone && !next.live &&
            !next.complete &&
            (next.registry.packages[0]?).any fun package => package.invocations == 1
      | _ => false
  | .error _ => false

#guard
  match start longSuggestionsPackage with
  | .ok session =>
      match session.advance with
      | .invalidReply .tooManySuggestions next =>
          next.arena.entries.isEmpty && next.engine.pending.isNone && !next.live &&
            !next.complete
      | _ => false
  | .error _ => false

-- A fuel stop preserves the live, paired session and can be resumed without
-- reusing local labels or losing the first committed proof entry.
#guard
  match start goodPackage with
  | .ok session =>
      let first := session.drive 1
      first.stop == .driverFuel && first.session.live &&
        first.session.arena.entries.size == 1 &&
        first.session.engine.history.size == 1 &&
        let resumed := first.session.drive 8
        resumed.stop == .saturated && resumed.session.complete &&
          resumed.session.arena.entries.size == 2 &&
          resumed.session.engine.history.size == 2
  | .error _ => false

-- Contradiction is preserved as an ordinary accepted fact with frozen
-- evidence, rather than confused with an incomplete or resource stop.
#guard
  match PayloadSession.Session.start contradictionDomain program #[goodPackage]
      #[3, 0, 0] limits arenaLimits with
  | .ok session =>
      let run := session.drive 8
      run.stop == .contradiction && run.session.live &&
        run.session.complete && run.session.arena.entries.size == 1 &&
        run.session.engine.history.size == 1 &&
        run.session.engine.contradictory
  | .error _ => false

-- Nested instantiation and equality labels are both relocated before the
-- narrowing suggestion enters retained engine state.
#guard
  match start nestedPackage with
  | .ok session =>
      match session.advance with
      | .advanced next =>
          next.live && !next.droppedWork && !next.complete &&
            next.arena.entries.size == 2 && next.engine.suggestions.size == 1 &&
            match next.engine.suggestions[0]? with
            | some retained =>
                match retained.suggestion with
                | .instantiate request =>
                    request.payload == payload 1 &&
                      (next.arena.entry? request.payload .instance).any
                        (fun entry => entry.schema == 2 && entry.body == [11]) &&
                      match request.equalities with
                      | [equality] =>
                          equality.payload == payload 0 &&
                            (next.arena.entry? equality.payload .equality).any
                              (fun entry => entry.schema == 3 && entry.body == [12])
                      | _ => false
                | _ => false
            | none => false
      | _ => false
  | .error _ => false

end Hex.Interval.PayloadSessionConformance
