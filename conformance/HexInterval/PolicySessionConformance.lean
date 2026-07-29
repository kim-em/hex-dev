/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.DyadicRules
import HexInterval.Experiment.PolicySession

/-!
End-to-end conformance for the proof-producing policy session.  A scripted
external policy uses only session views and choices while arbitrary packages
introduce a centered expression, prove its equality to an existing product,
propagate its sharper bound, retry an unrelated function, dismiss remaining
narrowing work, and prepare a split.
-/

namespace Hex.Interval.PolicySessionConformance

open Experiment Propagator
open DyadicRules
open PolicySession

def d (value : Int) : Dyadic := Dyadic.ofInt value

def real : DomainId := { index := 0 }
def sourceOp : OpKey := { name := "policy-session.source" }

def endpointLimit : EndpointLimit where
  maxEndpointHeight := 128
  maxAlignmentShift := 64

def config : Config :=
  { endpointLimit
    reciprocalBasePrecision := 2
    maxReciprocalEffort := 4 }

def engineLimits : Propagator.Limits :=
  { maxOperations := 24
    maxNodes := 32
    maxRules := 16
    maxRegistryEntries := 96
    maxReplayFormats := 32
    maxArity := 4
    maxApplications := 64
    maxQueueEntries := 256
    maxActions := 128
    maxAcceptedFacts := 128
    maxRetainedSuggestions := 32
    maxEffort := 8
    maxObservationValue := 256
    maxDiagnosticValue := 256
    maxOutcomeCandidates := 4
    maxOutcomeSuggestions := 4
    maxProposalItems := 16
    maxInstances := 8
    maxGeneration := 4
    maxNodeDepth := 16
    maxEqualities := 8
    splitEndpointLimit := endpointLimit }

def policyLimits : Propagator.Policy.Limits :=
  { maxDecisions := 128
    maxTraversal := 16384
    maxLiveOffers := 512 }

def arenaLimits : PayloadArena.Limits :=
  { maxEntries := 72
    maxBodyCells := 0
    maxDrafts := 72
    maxDraftCells := 0
    maxAtom := 0
    maxSchema := 0
    maxUses := 72 }

def limits : PolicySession.Limits :=
  { engine := engineLimits
    policy := policyLimits
    arena := arenaLimits }

def operations : Array Operation :=
  ((arithmeticOperations real).append (centeredOperations real)).push
    { key := sourceOp, inputs := [], output := real }

def node (index : Nat) : NodeId := { index }

def instruction (operation : Nat) (args : List NodeId := []) : Node :=
  { domain := real, op := { index := operation }, args }

/-- Nodes are `x`, `1`, `1-x`, `x*(1-x)`, `3`, and `1/3`.  The centered
instance is appended at node six. -/
def program : Program :=
  { operations
    nodes :=
      #[instruction 7,
        instruction 0,
        instruction 2 [node 1, node 0],
        instruction 3 [node 0, node 2],
        instruction 7,
        instruction 5 [node 4]] }

def finite (lower upper : Int) : Raw :=
  .bounds (.finite (d lower) false) (.finite (d upper) false)

def whole : Raw := .bounds .unbounded .unbounded

def initialFacts? : Option (Array Fact) :=
  match DyadicInterval.importInitialFacts endpointLimit 0
      [finite 0 1, finite 1 1, whole, whole, finite 3 3, whole] with
  | .ok facts => some facts.toArray
  | .error _ => none

def start? : Option (PolicySession.Session Fact) :=
  match initialFacts? with
  | none => none
  | some facts =>
      match PolicySession.Session.start (DyadicInterval.factDomain endpointLimit)
          program #[arithmeticPackage config real, centeredPackage config real]
          facts limits with
      | .ok session => some session
      | .error _ => none

inductive Command
  | invoke (key : RuleKey)
  | instantiate (key : RuleKey)
  | retry (key : RuleKey) (effort : Nat)
  | equality
  | dismissRetry (key : RuleKey) (effort : Nat)
  | split (key : RuleKey)

def commandMatches : Command -> Propagator.Policy.OfferView -> Bool
  | .invoke key, { key := .invoke source, .. } => source.rule == key
  | .instantiate key, { key := .instantiate source _, .. } => source.rule == key
  | .retry key effort, { key := .retry source offered, .. } =>
      source.rule == key && offered == effort
  | .equality, { key := .equality _, .. } => true
  | .dismissRetry key effort, { key := .retry source offered, .. } =>
      source.rule == key && offered == effort
  | .split key, { key := .split source _ _ _, .. } => source.rule == key
  | _, _ => false

def selection? (session : PolicySession.Session Fact) (command : Command) :
    Option (Propagator.Policy.Selection × PolicySession.Session Fact) :=
  match session.view with
  | .ready view viewed =>
      match view.offers.toList.find? (commandMatches command) with
      | none => none
      | some offer =>
          some
            ({ scope := view.scope
               serial := view.serial
               programVersion := view.programVersion
               id := offer.id
               expected := offer.key },
             viewed)
  | .resource _ _ | .contradiction _ | .invalidSession _ => none

structure Run where
  session : PolicySession.Session Fact
  split : Option (Propagator.Policy.SplitPlan Fact)

def execute? (session : PolicySession.Session Fact) (command : Command) :
    Option Run := do
  let (selection, viewed) <- selection? session command
  match command with
  | .invoke _ =>
      match viewed.choose (.select selection) with
      | .rule _ _ next => some { session := next, split := none }
      | _ => none
  | .retry _ _ =>
      match viewed.choose (.select selection) with
      | .rule _ _ next => some { session := next, split := none }
      | _ => none
  | .instantiate _ =>
      match viewed.choose (.select selection) with
      | .instance _ (.instanceAdmitted [fresh]) next =>
          if fresh == node 6 then some { session := next, split := none } else none
      | _ => none
  | .equality =>
      match viewed.choose (.select selection) with
      | .equality _ observation next =>
          if observation.outcome == .improved then
            some { session := next, split := none }
          else
            none
      | _ => none
  | .dismissRetry _ _ =>
      match viewed.choose (.dismiss selection) with
      | .dismissed _ next => some { session := next, split := none }
      | _ => none
  | .split _ =>
      match viewed.choose (.select selection) with
      | .split _ plan next => some { session := next, split := some plan }
      | _ => none

def run : List Command -> PolicySession.Session Fact -> Option Run
  | [], session => some { session, split := none }
  | command :: commands, session => do
      let step <- execute? session command
      match commands, step.split with
      | [], _ => some step
      | _ :: _, some _ => none
      | _ :: _, none => run commands step.session

def commands : List Command :=
  [.invoke subForwardKey,
    .invoke mulForwardKey,
    .invoke centeredInstantiateKey,
    .instantiate centeredInstantiateKey,
    .invoke centeredSplitKey,
    .invoke centeredForwardKey,
    .equality,
    .invoke reciprocalForwardKey,
    .retry reciprocalForwardKey 1,
    .dismissRetry reciprocalForwardKey 2,
    .split centeredSplitKey]

def final? : Option Run := do
  let session <- start?
  run commands session

def exactFact (session : PolicySession.Session Fact) (index : Nat)
    (expected : Raw) : Bool :=
  (session.state.engine.facts[index]?).any fun fact => fact.view == expected

def factPayload? (session : PolicySession.Session Fact) (target : NodeId)
    (key : RuleKey) : Option PayloadId := do
  let event <- session.state.engine.history.toList.find? fun event =>
    event.node == target &&
      match event.cause with
      | .rule action _ _ => action.key == key
      | .transport _ _ => false
  match event.cause with
  | .rule _ _ payload => some payload
  | .transport _ _ => none

def ownsV0 (session : PolicySession.Session Fact) (payload : PayloadId)
    (role : PayloadArena.Role) (key : RuleKey) : Bool :=
  (session.arena.entry? payload role).any fun entry =>
    entry.origin.key == key && entry.schema == 0 && entry.body.isEmpty

/-! # Prospective arena rejection -/

def badProgram : Program :=
  { operations :=
      #[{ key := centeredOp, inputs := [real], output := real },
        { key := sourceOp, inputs := [], output := real }]
    nodes := #[instruction 1, instruction 0 [node 0]] }

def badPlan (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs with
  | [input] =>
      { outcome :=
          .success
            [{ node := node 0, fact := input.fact, payload := factLabel }]
            [] {}
        drafts := [emptyDraft factLabel .fact] }
  | _ => withoutPayloads (.failed 70)

def badPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward badPlan #[emptyFormat .fact]] }

def malformedFormat : ReplayFormat :=
  { role := .fact
    schema := 0
    validateBody := fun _ => false }

def malformedPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward badPlan #[malformedFormat]] }

def missingFormatPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers := #[Handler.statelessPlanned centeredForward badPlan] }

def oneCellPlan (atom : Nat) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs with
  | [input] =>
      { outcome :=
          .success
            [{ node := node 0, fact := input.fact, payload := factLabel }]
            [] {}
        drafts :=
          [{ label := factLabel, role := .fact, schema := 0, body := [atom] }] }
  | _ => withoutPayloads (.failed 70)

def oneCellFormat : ReplayFormat :=
  { role := .fact
    schema := 0
    validateBody := fun body =>
      match body with
      | [_] => true
      | _ => false }

def atomPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward (oneCellPlan 1) #[oneCellFormat]] }

def bodyPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward (oneCellPlan 0) #[oneCellFormat]] }

def schemaPlan (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs with
  | [input] =>
      { outcome :=
          .success
            [{ node := node 0, fact := input.fact, payload := factLabel }]
            [] {}
        drafts :=
          [{ label := factLabel, role := .fact, schema := 1, body := [] }] }
  | _ => withoutPayloads (.failed 70)

def schemaFormat : ReplayFormat :=
  { role := .fact
    schema := 1
    validateBody := fun body => body.isEmpty }

def schemaPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward schemaPlan #[schemaFormat]] }

def usesPlan (request : RuleRequest Fact) : Plan Fact :=
  let equality : ProposedEquality :=
    { left := .existing request.action.node
      right := .existing request.action.node
      payload := equalityLabel }
  { outcome :=
      .success []
        [.instantiate
          { key := 91
            triggers := [request.action.node]
            nodes := []
            equalities := List.replicate arenaLimits.maxUses equality
            payload := instanceLabel }]
        {}
    drafts := [] }

def usesPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward usesPlan #[emptyFormat .fact]] }

def draftsPlan (_request : RuleRequest Fact) : Plan Fact :=
  { outcome := .noChange {}
    drafts :=
      List.replicate (arenaLimits.maxDrafts + 1) (emptyDraft factLabel .fact) }

def draftsPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward draftsPlan #[emptyFormat .fact]] }

def badFacts? : Option (Array Fact) :=
  match DyadicInterval.importInitialFacts endpointLimit 0 [finite 0 1, whole] with
  | .ok facts => some facts.toArray
  | .error _ => none

def badStartWith? (package : Package Fact)
    (sessionLimits : PolicySession.Limits := limits) :
    Option (PolicySession.Session Fact) :=
  match badFacts? with
  | none => none
  | some facts =>
      match PolicySession.Session.start (DyadicInterval.factDomain endpointLimit)
          badProgram #[package] facts sessionLimits with
      | .ok session => some session
      | .error _ => none

def badStart? : Option (PolicySession.Session Fact) :=
  badStartWith? badPackage

def missingFormatStart? : Option (PolicySession.Session Fact) :=
  badStartWith? missingFormatPackage

def capacityProgram : Program :=
  { badProgram with
    nodes :=
      #[instruction 1,
        instruction 0 [node 0],
        instruction 0 [node 0]] }

def capacityPlan (body : List Nat) (request : RuleRequest Fact) : Plan Fact :=
  match request.inputs, request.writes with
  | [input], [target] =>
      { outcome :=
          .success
            [{ node := target, fact := input.fact, payload := factLabel }]
            [] {}
        drafts :=
          [{ label := factLabel, role := .fact, schema := 0, body }] }
  | _, _ => withoutPayloads (.failed 70)

def entryPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward (capacityPlan []) #[emptyFormat .fact]] }

def cellPackage : Package Fact :=
  { Cache := Unit
    cache := ()
    operations := centeredOperations real
    handlers :=
      #[Handler.statelessPlanned centeredForward (capacityPlan [0]) #[oneCellFormat]] }

def capacityFacts? : Option (Array Fact) :=
  match
      DyadicInterval.importInitialFacts endpointLimit 0
        [finite 0 1, whole, whole] with
  | .ok facts => some facts.toArray
  | .error _ => none

def capacityEngineLimits : Propagator.Limits :=
  { engineLimits with
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 0 }

def entryArena : PayloadArena.Limits :=
  { maxEntries := 1
    maxBodyCells := 0
    maxDrafts := 1
    maxDraftCells := 0
    maxAtom := 0
    maxSchema := 0
    maxUses := 1 }

def cellArena : PayloadArena.Limits :=
  { maxEntries := 2
    maxBodyCells := 1
    maxDrafts := 1
    maxDraftCells := 1
    maxAtom := 0
    maxSchema := 0
    maxUses := 1 }

def capacityLimits (arena : PayloadArena.Limits) : PolicySession.Limits :=
  { engine := capacityEngineLimits, policy := policyLimits, arena }

def capacityStartWith? (package : Package Fact)
    (arena : PayloadArena.Limits) : Option (PolicySession.Session Fact) :=
  match capacityFacts? with
  | none => none
  | some facts =>
      match PolicySession.Session.start (DyadicInterval.factDomain endpointLimit)
          capacityProgram #[package] facts (capacityLimits arena) with
      | .ok session => some session
      | .error _ => none

def incompleteView (session : PolicySession.Session Fact) : Bool :=
  match session.view with
  | .ready view next =>
      view.offers.isEmpty && view.incomplete && next.live && !next.complete
  | .resource _ _ | .contradiction _ | .invalidSession _ => false

#guard program.check
#guard capacityProgram.check
#guard
  PolicySession.requiredUses engineLimits == 72 &&
    PolicySession.limitsCoherent limits
#guard
  !PolicySession.limitsCoherent
    { limits with
      arena :=
        { arenaLimits with
          maxEntries := 73
          maxDrafts := 73
          maxUses := 72 } }
#guard PolicySession.limitsCoherent (capacityLimits entryArena)
#guard PolicySession.limitsCoherent (capacityLimits cellArena)

-- The policy never obtains a free-standing engine, registry, or arena.  The
-- single session route freezes all seven fact/instance/equality recipes,
-- admits the centered node and edge, and transports `[0,1/4]` back to the
-- dependency-losing product.  Dismissing retry effort two is remembered as
-- incomplete even though the later split is still selectable.
#guard
  match final? with
  | none => false
  | some result =>
      let session := result.session
      session.live && !session.droppedWork && session.state.incomplete &&
        !session.complete &&
        session.state.metrics.decisions == 11 &&
        session.state.metrics.selectedInvocations == 6 &&
        session.state.metrics.selectedRetries == 1 &&
        session.state.metrics.selectedInstances == 1 &&
        session.state.metrics.selectedEqualities == 1 &&
        session.state.metrics.selectedSplits == 1 &&
        session.state.metrics.dismissals == 1 &&
        session.state.engine.programVersion == 1 &&
        session.state.engine.program.nodes.size == 7 &&
        session.state.engine.equalities.size == 1 &&
        session.state.engine.instanceHistory.size == 1 &&
        session.arena.entries.size == 7 && session.arena.bodyCells == 0 &&
        session.arena.entries.toList.map (fun entry => entry.role) ==
          [.fact, .fact, .instance, .equality, .fact, .fact, .fact] &&
        exactFact session 3
          (.bounds (.finite 0 false) (.finite quarter false)) &&
        exactFact session 6
          (.bounds (.finite 0 false) (.finite quarter false)) &&
        match session.state.engine.instanceHistory[0]?,
            session.state.engine.equalities[0]?,
            factPayload? session (node 6) centeredForwardKey,
            result.split with
        | some instanceEvent, some equality, some factPayload, some split =>
            instanceEvent.payload.index == 2 && equality.payload.index == 3 &&
              factPayload.index == 4 &&
              ownsV0 session instanceEvent.payload .instance centeredInstantiateKey &&
              ownsV0 session equality.payload .equality centeredInstantiateKey &&
              ownsV0 session factPayload .fact centeredForwardKey &&
              equality.left == node 3 && equality.right == node 6 &&
              split.node == node 0 && split.point == half &&
              split.reason == .criticalPoint &&
              split.origin.key == centeredSplitKey
        | _, _, _, _ => false

-- Freezing an otherwise well-formed fact draft is prospective.  The package's
-- undeclared write is rejected by policy-state submission, and the returned
-- non-live session retains neither the new arena entry nor any fact history.
#guard
  match badStart? with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .invalidReply (.undeclaredWrite target) stopped =>
              target == node 0 && !stopped.live &&
                stopped.arena.entries.isEmpty &&
                stopped.arena.bodyCells == 0 &&
                stopped.state.engine.history.isEmpty &&
                stopped.state.engine.pending.isNone
          | _ => false

-- A declared format which rejects the bounded body takes the same atomic,
-- live-but-incomplete path. No partially frozen entry, fact, or history item
-- survives, and the empty next view is explicitly incomplete rather than a
-- false saturation claim.
#guard
  match badStartWith? malformedPackage with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .invalidPayload (.invalidBody key) next =>
              key.rule == centeredForwardKey && key.role == .fact &&
                key.schema == 0 && next.live && next.droppedWork &&
                next.state.incomplete && !next.complete &&
                next.arena.entries.isEmpty && next.arena.bodyCells == 0 &&
                next.state.engine.history.isEmpty &&
                next.state.engine.pending.isNone &&
                next.state.engine.metrics.ruleFailures == 1 &&
                incompleteView next
          | _ => false

-- The same plan without its handler-owned fact format fails before arena or
-- engine admission. The synthetic failed reply clears the latch and keeps the
-- session usable, while permanently preventing a completeness claim.
#guard
  match missingFormatStart? with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .invalidPayload (.undeclaredFormat key) next =>
              key.rule == centeredForwardKey && key.role == .fact &&
                key.schema == 0 && next.live && next.droppedWork &&
                next.state.incomplete && !next.complete &&
                next.arena.entries.isEmpty && next.arena.bodyCells == 0 &&
                next.state.engine.history.isEmpty &&
                next.state.engine.pending.isNone &&
                next.state.engine.metrics.ruleFailures == 1 &&
                incompleteView next &&
                (next.registry.packages[0]?).any fun package =>
                  package.invocations == 1
          | _ => false

-- Payload-use, draft-count, draft-cell, atom, and schema bounds are
-- package-local encoding failures. Each rejected plan consumes a bounded
-- failed reply, keeps the private owner live for later choices, rolls back the
-- prospective arena, and makes the now-empty policy frontier explicitly
-- incomplete.
#guard
  match badStartWith? usesPackage with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .rejectedPayload .uses next =>
              next.live && next.droppedWork && next.state.incomplete &&
                next.state.engine.pending.isNone &&
                next.state.engine.metrics.ruleFailures == 1 &&
                next.arena.entries.isEmpty &&
                next.state.engine.history.isEmpty && incompleteView next
          | _ => false

#guard
  match badStartWith? draftsPackage with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .rejectedPayload .drafts next =>
              next.live && next.droppedWork && next.state.incomplete &&
                next.state.engine.pending.isNone &&
                next.state.engine.metrics.ruleFailures == 1 &&
                next.arena.entries.isEmpty &&
                next.state.engine.history.isEmpty && incompleteView next
          | _ => false

#guard
  match badStartWith? atomPackage
      { limits with arena := { arenaLimits with maxBodyCells := 1 } } with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .rejectedPayload .atom next =>
              next.live && next.droppedWork && next.state.incomplete &&
                next.state.engine.pending.isNone &&
                next.state.engine.metrics.ruleFailures == 1 &&
                next.arena.entries.isEmpty &&
                next.state.engine.history.isEmpty && incompleteView next
          | _ => false

#guard
  match badStartWith? bodyPackage with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .rejectedPayload .draftCells next =>
              next.live && next.droppedWork && next.state.incomplete &&
                next.state.engine.pending.isNone &&
                next.state.engine.metrics.ruleFailures == 1 &&
                next.arena.entries.isEmpty &&
                next.state.engine.history.isEmpty && incompleteView next
          | _ => false

#guard
  match badStartWith? schemaPackage with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .rejectedPayload .schema next =>
              next.live && next.droppedWork && next.state.incomplete &&
                next.state.engine.pending.isNone &&
                next.state.engine.metrics.ruleFailures == 1 &&
                next.arena.entries.isEmpty &&
                next.state.engine.history.isEmpty && incompleteView next
          | _ => false

-- Entry and body-cell budgets become fatal only when an otherwise valid reply
-- no longer fits after a prior policy-selected commit. The earlier arena and
-- fact history remain intact, but the returned private snapshot cannot resume
-- or claim completeness.
#guard
  match capacityStartWith? entryPackage entryArena with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .rule _ _ first =>
              first.arena.entries.size == 1 &&
                first.state.engine.history.size == 1 &&
                match selection? first (.invoke centeredForwardKey) with
                | none => false
                | some (nextSelection, nextViewed) =>
                    match nextViewed.choose (.select nextSelection) with
                    | .payloadResource .entries stopped =>
                        !stopped.live && !stopped.complete &&
                          stopped.state.incomplete &&
                          stopped.state.engine.pending.isNone &&
                          stopped.arena.entries.size == 1 &&
                          stopped.state.engine.history.size == 1
                    | _ => false
          | _ => false

#guard
  match capacityStartWith? cellPackage cellArena with
  | none => false
  | some session =>
      match selection? session (.invoke centeredForwardKey) with
      | none => false
      | some (selection, viewed) =>
          match viewed.choose (.select selection) with
          | .rule _ _ first =>
              first.arena.entries.size == 1 && first.arena.bodyCells == 1 &&
                first.state.engine.history.size == 1 &&
                match selection? first (.invoke centeredForwardKey) with
                | none => false
                | some (nextSelection, nextViewed) =>
                    match nextViewed.choose (.select nextSelection) with
                    | .payloadResource .bodyCells stopped =>
                        !stopped.live && !stopped.complete &&
                          stopped.state.incomplete &&
                          stopped.state.engine.pending.isNone &&
                          stopped.arena.entries.size == 1 &&
                          stopped.arena.bodyCells == 1 &&
                          stopped.state.engine.history.size == 1
                    | _ => false
          | _ => false

end Hex.Interval.PolicySessionConformance
