/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Conformance

/-!
# Supported search-contract conformance

These guards discriminate exact policy/action binding, transactional callback
updates, independent resource stops, stable frontier order, parent restoration,
and diagnostic truncation from proof-state mutation.
-/

namespace Hex.Interval.SearchConformance

open Conformance.Contracts
open Search

private def searchLimits : Search.Limits :=
  { maxSteps := 4
    maxSplits := 2
    maxLeaves := 3
    maxFrontier := 3
    maxDepth := 2
    maxScopes := 5
    leafFuel := 4 }

private def traceLimits : Trace.Limit :=
  { maxEvents := 1, maxBytes := 1, maxWork := 1, maxCode := 8 }

private def envelope : Search.Envelope :=
  { state := stateLimits
    policy := policyLimits
    trace := traceLimits
    search := searchLimits }

private def offer : Search.Offer Nat Action :=
  { view := policyOffer, action := policyAction }

private def session? : Option (Search.Session Nat Nat Nat Action) := do
  let branch <- branch?
  (Search.Session.startWithin envelope policyMeasure branch #[localRule] #[]
    #[0] #[0] 0 { index := 5 } #[offer] policyBudget false).toOption

private def decision? : Option (Policy.Decision Nat Action) := do
  let session <- session?
  pure (Policy.select session.view offer.view)

private def outcome (updates : Array (State.Update Nat Nat) := #[firstUpdate])
    (diagnostic : Option Trace.Event := none) : Search.Outcome Nat Nat Nat Action :=
  { scope := { index := 5 }
    serial := 0
    programVersion := 0
    offer := offer.view
    action := policyAction
    updates
    diagnostic }

private def searchError (wanted : Search.Error)
    (result : Except Search.Error α) : Bool :=
  match result with
  | .error actual => decide (actual = wanted)
  | .ok _ => false

private def offerFor (action : Action) : Search.Offer Nat Action :=
  { view := { policyOffer with key := action }, action }

private def startActionError (action : Action)
    (limits : State.Limits := stateLimits) : Option Search.Error := do
  let branch <- branch?
  match Search.Session.startWithin { envelope with state := limits } policyMeasure branch
      #[localRule] #[] #[0] #[0] 0 { index := 5 } #[offerFor action]
      policyBudget false with
  | .error error => some error
  | .ok _ => none

private def scopedAction : Action :=
  { serial := 0
    programVersion := 0
    application := { index := 0 }
    rule := { index := 0 }
    key := scopedKey
    node := contractNode 1
    kind := .improve
    effort := 0
    generation := 0
    inputs := [{ node := contractNode 0, version := 0 }]
    writes := [contractNode 1] }

private def startScopedError (limits : State.Limits) : Option Search.Error := do
  let branch <- branch?
  match Search.Session.startWithin { envelope with state := limits } policyMeasure branch
      #[scopeRule] #[binding] #[0] #[0] 0 { index := 5 } #[offerFor scopedAction]
      policyBudget false with
  | .error error => some error
  | .ok _ => none

private def networkRule : Registration :=
  { key := { name := "search.network" }
    head := unaryKey
    kind := .instantiate
    watches := []
    writes := []
    binding := .global
    watchesProgram := true
    matchWatch := .network }

private def startNetworkError (limits : State.Limits) : Option Search.Error := do
  let branch <- branch?
  match Search.Session.startWithin { envelope with state := limits } policyMeasure branch
      #[networkRule] #[] #[] #[0] 0 { index := 5 } #[] policyBudget false with
  | .error error => some error
  | .ok _ => none

#guard match session? with
  | some session => session.check envelope policyMeasure
  | none => false

#guard startActionError policyAction == none
#guard startScopedError stateLimits == none
#guard startNetworkError stateLimits == none

#guard match branch? with
  | some branch =>
      searchError (.policy .offerLimit) <|
        Search.Session.startWithin
          { envelope with policy := { policyLimits with maxOffers := 0 } }
          policyMeasure branch #[localRule] #[] #[0] #[0] 0 { index := 5 }
          #[offer] policyBudget false
  | none => false

-- Every untrusted list and structural array is capped before semantic scans or
-- package measurements. The resource class identifies the governing State
-- limit rather than collapsing all oversized sessions to `invalidSession`.
#guard startActionError
  { policyAction with inputs := [
      { node := contractNode 0, version := 0 },
      { node := contractNode 1, version := 0 },
      { node := contractNode 0, version := 1 },
      { node := contractNode 1, version := 1 }] } ==
    some (.resource (.state .arity))

#guard startActionError
  { policyAction with writes := [contractNode 0, contractNode 1,
      contractNode 0, contractNode 1] } == some (.resource (.state .arity))

#guard startActionError
  { policyAction with structuralInputs := [
      { key := .node (contractNode 0), generation := 0 },
      { key := .node (contractNode 1), generation := 0 }] } ==
    some (.resource (.state .matcherVisits))

#guard startActionError policyAction { stateLimits with maxOperations := 1 } ==
  some (.resource (.state .operations))
#guard startActionError policyAction { stateLimits with maxNodes := 1 } ==
  some (.resource (.state .nodes))
#guard startActionError policyAction { stateLimits with maxRules := 0 } ==
  some (.resource (.state .rules))
#guard startActionError policyAction { stateLimits with maxArity := 0 } ==
  some (.resource (.state .arity))
#guard startActionError policyAction { stateLimits with maxNodeDepth := 0 } ==
  some (.resource (.state .nodeDepth))
#guard startActionError policyAction { stateLimits with maxEqualities := 0 } ==
  some (.resource (.state .equalities))
#guard startActionError { policyAction with effort := stateLimits.maxEffort + 1 } ==
  some (.resource (.state .effort))

-- Binding count and per-binding ports use independent limits. In particular,
-- one binding cannot slip through merely because `maxScopeNodes` is nonzero.
#guard startScopedError { stateLimits with maxApplications := 0 } ==
  some (.resource (.state .applications))
#guard startScopedError { stateLimits with maxScopeNodes := 0 } ==
  some (.resource (.state .scopes))
#guard startNetworkError { stateLimits with matcherBatchSize := 0 } ==
  some (.resource (.state .matcherVisits))

-- Search currently treats the compact application id as an opaque scheduler
-- handle: it authenticates its generation while independently checking the
-- rule, anchor, kind, and ports. No application table is claimed here.
#guard match branch? with
  | some branch =>
      match Search.Session.startWithin envelope policyMeasure branch #[localRule] #[]
          #[0, 0] #[0] 0 { index := 5 }
          #[offerFor { policyAction with application := { index := 1 } }]
          policyBudget false with
      | .ok _ => true
      | .error _ => false
  | none => false

-- A successful batch is bound to the exact selected action and commits one
-- versioned update atomically.
#guard match session?, decision? with
  | some session, some decision =>
      match Search.acceptWithin envelope policyMeasure session decision
          (.outcome (outcome)) with
      | .ok (.applied next) =>
            next.branch.snapshot.facts == #[13, 29] && next.branch.versions == #[0, 1] &&
            next.branch.history == #[firstUpdate] && next.serial == 1 &&
            next.offers.isEmpty && next.steps == 1
      | _ => false
  | _, _ => false

private def stepEnvelope : Search.Envelope :=
  { envelope with search := { searchLimits with maxSteps := 1, maxFrontier := 0 } }

private def atStepLimit? : Option (Search.Session Nat Nat Nat Action) := do
  let branch <- branch?
  let session <- (Search.Session.startWithin stepEnvelope policyMeasure branch #[localRule] #[]
    #[0] #[0] 0 { index := 5 } #[offer] policyBudget false).toOption
  let decision := Policy.select session.view offer.view
  let .applied session <-
    (Search.acceptWithin stepEnvelope policyMeasure session decision
      (.outcome outcome)).toOption | none
  let nextAction := { policyAction with serial := 1 }
  let nextOffer := offerFor nextAction
  Search.Session.refreshWithin stepEnvelope policyMeasure session #[nextOffer]
    policyBudget false |>.toOption

-- A session-only step budget is independent of branch-tree frontier capacity.
#guard atStepLimit?.any fun session => session.steps == 1

-- A resource stop cannot launder a malformed decision, while `invokeWithin`
-- refuses before evaluating a callback once the authenticated step budget is
-- exhausted.
#guard match atStepLimit?, decision? with
  | some session, some _decision =>
      match session.offers[0]? with
      | some current =>
          searchError (.policy .wrongScope) <|
            Search.acceptWithin stepEnvelope policyMeasure session
              { (Policy.select session.view current.view) with scope := { index := 4 } }
              (.failure 0)
      | none => false
  | _, _ => false

#guard match atStepLimit?, decision? with
  | some session, some _decision =>
      match session.offers[0]? with
      | some current =>
          match Search.invokeWithin stepEnvelope policyMeasure
              (fun _ => (.failure 9 : Search.Reply Nat Nat Nat Action))
              session (Policy.select session.view current.view) with
          | .ok (.stopped (.resource .steps) _) => true
          | _ => false
      | none => false
  | _, _ => false

-- Application generation is authenticated rather than inferred from a compact
-- count. A stale generation prevents construction of a sealed session.
#guard match branch? with
  | some branch =>
      searchError .invalidSession <|
        Search.Session.startWithin envelope policyMeasure branch #[localRule] #[]
          #[1] #[0] 0 { index := 5 } #[offer] policyBudget false
  | none => false

-- Scope, serial, program, semantic key, and every exposed offer field remain
-- load-bearing at the supported transition boundary.
#guard match session?, decision? with
  | some session, some decision =>
      searchError (.policy .wrongScope) <|
        Search.prepareWithin envelope policyMeasure session
          { decision with scope := { index := 4 } }
  | _, _ => false

#guard match session?, decision? with
  | some session, some decision =>
      searchError (.policy .staleSerial) <|
        Search.prepareWithin envelope policyMeasure session
          { decision with serial := 1 }
  | _, _ => false

#guard match session?, decision? with
  | some session, some decision =>
      searchError (.policy .staleProgram) <|
        Search.prepareWithin envelope policyMeasure session
          { decision with programVersion := 1 }
  | _, _ => false

#guard match session?, decision? with
  | some session, some decision =>
      searchError .staleReply <|
        Search.acceptWithin envelope policyMeasure session decision <|
          .outcome { outcome with action := { policyAction with serial := 1 } }
  | _, _ => false

#guard match session? with
  | some session =>
      let changed :=
        #[{ offer with action := { policyAction with key := { localKey with schema := 9 } } }]
      searchError .invalidSession <|
        Search.Session.refreshWithin envelope policyMeasure session changed policyBudget false
  | none => false

#guard match session?, decision? with
  | some session, some decision =>
      searchError .staleReply <|
        Search.acceptWithin envelope policyMeasure session decision <|
          .outcome { outcome with offer := { offer.view with age := 9 } }
  | _, _ => false

#guard match session?, decision? with
  | some session, some decision =>
      searchError .malformedOutcome <|
        Search.acceptWithin envelope policyMeasure session decision <|
          .outcome { outcome (#[]) with contradiction := true }
  | _, _ => false

-- Writes outside exact action authority and a stale second update reject the
-- whole batch. The caller still owns the unchanged original session.
#guard match session?, decision? with
  | some session, some decision =>
      let wrongNode : State.Update Nat Nat :=
        { firstUpdate with
          node := contractNode 0
          previous := { node := contractNode 0, version := 0 } }
      searchError (.unauthorizedWrite (contractNode 0)) <|
        Search.acceptWithin envelope policyMeasure session decision
          (.outcome (outcome #[wrongNode]))
  | _, _ => false

#guard match session?, decision? with
  | some session, some decision =>
      let staleSecond :=
        { secondUpdate with previous := { node := contractNode 1, version := 0 } }
      searchError (.state (.staleVersion (contractNode 1)))
          (Search.acceptWithin envelope policyMeasure session decision
            (.outcome (outcome #[firstUpdate, staleSecond]))) &&
        session.branch.snapshot.facts == #[13, 23] && session.branch.history.isEmpty
  | _, _ => false

#guard match session?, decision? with
  | some session, some decision =>
      searchError .outcomeLimit <|
        Search.acceptWithin
          { envelope with state := { stateLimits with maxOutcomeCandidates := 0 } }
          policyMeasure session decision (.outcome (outcome))
  | _, _ => false

#guard match session?, decision? with
  | some session, some decision =>
      searchError (.resource (.state .acceptedFacts)) <|
        Search.acceptWithin
          { envelope with state := { stateLimits with maxAcceptedFacts := 0 } }
          policyMeasure session decision (.outcome (outcome))
  | _, _ => false

-- A callback failure has an exact stop and cannot mutate branch facts,
-- versions, provenance, or contradiction state.
#guard match session?, decision? with
  | some session, some decision =>
      match Search.acceptWithin envelope policyMeasure session decision (.failure 3) with
      | .ok (.stopped (.callbackFailure 3) next) => next.branch == session.branch
      | _ => false
  | _, _ => false

-- Diagnostic truncation changes only the retained log. The accepted proof
-- state is byte-for-byte the same as the no-diagnostic run.
#guard match session?, decision? with
  | some session, some decision =>
      let plain := Search.acceptWithin envelope policyMeasure session decision
        (.outcome (outcome))
      let noisy := Search.acceptWithin envelope policyMeasure session decision
        (.outcome (outcome (diagnostic := some { code := 1, payload := #[1, 2] })))
      match plain, noisy with
      | .ok (.applied left), .ok (.applied right) =>
          left.branch == right.branch && !left.trace.truncated && right.trace.truncated
      | _, _ => false
  | _, _ => false

-- Stopping is conservative even with a nonempty frontier. A policy which
-- returns a mutated copy is rejected rather than authorized.
private def stopped : Policy.Interface Nat Bool Nat Action :=
  { choose := fun state _ => .stop state }

private def mutated : Policy.Interface Nat Bool Nat Action :=
  { choose := fun state _ => .select { offer.view with score := 0 } state }

#guard match session? with
  | some session =>
      match Search.chooseWithin envelope policyMeasure stopped false session with
      | .ok (.stopped (.policyStop 1) false) => true
      | _ => false
  | none => false

#guard match session? with
  | some session =>
      searchError (.policy .mutatedOffer) <|
        Search.chooseWithin envelope policyMeasure mutated false session
  | none => false

private def leaf (scope depth payload : Nat)
    (parent : Option (Search.Parent Nat Nat) := none) : Option (Search.Leaf Nat Nat Nat) := do
  let branch <- branch?
  pure { scope := { index := scope }, depth, branch, parent, payload }

private def nested? (order : Search.Order) :
    Option (Search.FrontierState (Search.Leaf Nat Nat Nat)) := do
  let root <- leaf 0 0 0
  let .ok state := Search.startFrontierWithin stateLimits searchLimits root | none
  let root <- state.head?
  let parent := root.asParent
  let left <- leaf 1 1 1 (some parent)
  let right <- leaf 2 1 2 (some parent)
  let .ok state := Search.splitWithin stateLimits searchLimits order state left right | none
  let left <- state.head?
  let parent := left.asParent
  let leftLeft <- leaf 3 2 3 (some parent)
  let leftRight <- leaf 4 2 4 (some parent)
  Search.splitWithin stateLimits searchLimits order state leftLeft leftRight |>.toOption

-- Both stable orders retain left-to-right sibling order and differ only in
-- where fresh work is placed relative to the old suffix.
#guard nested? .depthFirst |>.any fun result =>
  result.accounting.steps == 2 && result.accounting.splits == 2 &&
    result.accounting.leaves == 3 && result.accounting.scopes == 5 &&
    result.accounting.nextScope == 5 &&
    result.pending.map (fun leaf => leaf.scope.index) == [3, 4, 2]

#guard nested? .breadthFirst |>.any fun result =>
  result.accounting.steps == 2 && result.accounting.splits == 2 &&
    result.accounting.leaves == 3 && result.accounting.scopes == 5 &&
    result.accounting.nextScope == 5 &&
    result.pending.map (fun leaf => leaf.scope.index) == [2, 3, 4]

-- Child restoration returns the exact immutable parent, including scope,
-- fact versions, and provenance history.
#guard nested? .depthFirst |>.any fun result =>
  match result.pending[0]? with
  | some child =>
      child.restoreParent?.any fun parent =>
        parent.scope.index == 1 && parent.branch.versions == #[0, 0] &&
          parent.branch.history.isEmpty
  | none => false

-- Independent one-over resources fail before a replacement frontier or
-- accounting value is returned.
#guard match leaf 0 0 0 with
  | some root =>
      searchError (.resource .frontier) <|
        Search.startFrontierWithin stateLimits { searchLimits with maxFrontier := 0 } root
  | none => false

private def splitError (limits : Search.Limits) : Option Search.Error := do
  let root <- leaf 0 0 0
  let .ok state := Search.startFrontierWithin stateLimits searchLimits root | none
  let root <- state.head?
  let parent := root.asParent
  let left <- leaf 1 1 1 (some parent)
  let right <- leaf 2 1 2 (some parent)
  match Search.splitWithin stateLimits limits .depthFirst state left right with
  | .error error => some error
  | .ok _ => none

#guard splitError { searchLimits with maxSteps := 0 } == some (.resource .steps)
#guard splitError { searchLimits with maxSplits := 0 } == some (.resource .splits)
#guard splitError { searchLimits with maxLeaves := 1 } == some (.resource .leaves)
#guard splitError { searchLimits with maxScopes := 2 } == some (.resource .scopes)
#guard splitError { searchLimits with maxDepth := 0 } == some (.resource .depth)
#guard splitError { searchLimits with maxFrontier := 1 } == some (.resource .frontier)

private def malformedParentError : Option Search.Error := do
  let root <- leaf 0 0 0
  let malformed := { root with branch := { root.branch with versions := #[9, 0] } }
  match Search.startFrontierWithin stateLimits searchLimits malformed with
  | .error error => some error
  | .ok _ => none

private def detachedParentError : Option Search.Error := do
  let root <- leaf 0 0 0
  let detached <- leaf 9 0 9
  let .ok state := Search.startFrontierWithin stateLimits searchLimits root | none
  let parent := detached.asParent
  let left <- leaf 1 1 1 (some parent)
  let right <- leaf 2 1 2 (some parent)
  match Search.splitWithin stateLimits searchLimits .depthFirst state left right with
  | .error error => some error
  | .ok _ => none

private def secondSplitError (limits : Search.Limits) : Option Search.Error := do
  let root <- leaf 0 0 0
  let .ok state := Search.startFrontierWithin stateLimits limits root | none
  let parent := root.asParent
  let left <- leaf 1 1 1 (some parent)
  let right <- leaf 2 1 2 (some parent)
  let .ok state := Search.splitWithin stateLimits limits .depthFirst state left right | none
  let parent := left.asParent
  let leftLeft <- leaf 3 2 3 (some parent)
  let leftRight <- leaf 4 2 4 (some parent)
  match Search.splitWithin stateLimits limits .depthFirst state leftLeft leftRight with
  | .error error => some error
  | .ok _ => none

-- The sealed composite derives the split parent and cumulative counters from
-- one live frontier. Detached parents and nested one-over resources fail.
#guard malformedParentError == some .invalidSession
#guard detachedParentError == some .invalidSession
#guard secondSplitError { searchLimits with maxSteps := 1 } == some (.resource .steps)
#guard secondSplitError { searchLimits with maxSplits := 1 } == some (.resource .splits)
#guard secondSplitError { searchLimits with maxFrontier := 2 } == some (.resource .frontier)

end Hex.Interval.SearchConformance
