/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Search
import LeanBench

/-!
# Authenticated interval decision benchmark

This experimental matrix exercises one supported scheduling surface which
remains Mathlib-free: repeated `Search.chooseWithin` selection,
`Search.invokeWithin` fact updates, and checked `Search.Session.refreshWithin`
regeneration over one arithmetic DAG. FIFO, static-rank, and adaptive policies
reach the same final fact state through different authenticated action orders;
the logical-count leg selects no default.

The end-to-end `Controller.Executable` fact adapter is intentionally absent.
It currently imports the Mathlib proof driver, so importing it here would
violate the repository's Mathlib-free computational-bench contract. Mixed
typed-event and split/tree workloads are simply out of scope for this focused
policy experiment: direct Mathlib-free `Runtime.State.stepWithin` and
`Search.Result.advanceRuntimeWithin` / `splitWithin` / `settleWithin` APIs do
exist. The benchmark does not make their absence a causal claim.

The canonical `canary` input has 128 nodes and pins separate order-sensitive
policy trace hashes, one shared final-state checksum, accepted updates, and
callback comparisons. Fixed timing registrations instead measure one shared
end-to-end authenticated choose/invoke/complete-refresh transition at each
committed offer count. They include session construction and all checked
authentication and yield no comparative policy signal. Every IO runner throws
on failure and every fixed rung pins the hash of its full report.
-/

namespace Hex.Interval.DecisionBench

inductive PolicyKind where
  | fifo
  | staticRank
  | adaptive
  deriving DecidableEq, Repr

structure PolicyState where
  decisions : Nat := 0
  comparisons : Nat := 0
  orderHash : UInt64 := 0
  deriving DecidableEq, Repr

structure Report where
  nodes : Nat
  offers : Nat
  decisions : Nat
  comparisons : Nat
  updates : Nat
  orderHash : UInt64
  semantic : UInt64
  deriving DecidableEq, Repr, Hashable

private def domain : DomainId := { index := 0 }

private def constantKey : OpKey := { name := "decision-bench.constant" }

private def addKey : OpKey := { name := "decision-bench.add" }

private def ruleKey : RuleKey := { name := "decision-bench.add-forward" }

private def operations : Array Operation :=
  #[{ key := constantKey, inputs := [], output := domain },
    { key := addKey, inputs := [domain, domain], output := domain }]

private def nodeId (index : Nat) : NodeId := { index }

private def applicationId (index : Nat) : ApplicationId := { index }

/-- A Fibonacci-shaped arithmetic DAG with two constants and `n - 2` additions. -/
private def program (n : Nat) : Program :=
  let nodes := (Array.range n).map fun index =>
    if index < 2 then
      { domain, op := { index := 0 }, args := [] }
    else
      { domain, op := { index := 1 }, args := [nodeId (index - 2), nodeId (index - 1)] }
  { operations, nodes }

private def rule : Registration :=
  { key := ruleKey
    head := addKey
    kind := .forward
    watches := [.argument 0, .argument 1]
    writes := [.result] }

private def stateLimits (n : Nat) : State.Limits :=
  { maxOperations := 2
    maxNodes := n
    maxRules := 1
    maxRegistryEntries := 0
    maxReplayFormats := 0
    maxArity := 2
    maxApplications := n
    maxQueueEntries := n
    maxActions := n
    maxAcceptedFacts := n
    maxRetainedSuggestions := 0
    maxEffort := 0
    maxObservationValue := 0
    maxDiagnosticValue := 0
    maxOutcomeCandidates := 1
    maxOutcomeSuggestions := 0
    maxProposalItems := 0
    maxInstances := 0
    maxGeneration := 0
    maxNodeDepth := n
    maxEqualities := 0
    splitEndpointLimit := { maxEndpointHeight := 0, maxAlignmentShift := 0 } }

private def searchLimits (n : Nat) : Search.Limits :=
  { maxSteps := n
    maxSplits := 0
    maxLeaves := 1
    maxFrontier := 1
    maxDepth := 0
    maxScopes := 1
    leafFuel := n }

private def policyLimits (n : Nat) : Policy.Limits :=
  { maxOffers := n
    maxBytes := 64 * n
    maxPairs := 4 * n
    maxWork := 4 * n
    maxScore := 128 }

private def envelope (n : Nat) : Search.Envelope :=
  { state := stateLimits n
    policy := policyLimits n
    trace := { maxEvents := 0, maxBytes := 0, maxWork := 0, maxCode := 0 }
    search := searchLimits n }

private def measure : Policy.Measure ApplicationId RuleKey :=
  { id := fun _ => { pairs := 1, work := 1 }
    key := fun key => { bytes := key.name.length + 1, pairs := 1, work := 1 } }

private def scoreAt (index : Nat) : Int :=
  Int.ofNat ((index * 17 + 11) % 101) - 50

private def offer? (serial : Nat) (versions : Array Nat) (index : Nat) :
    Option (Search.Offer ApplicationId RuleKey) := do
  let output := index + 2
  let leftVersion ← versions[output - 2]?
  let rightVersion ← versions[output - 1]?
  let action : Action :=
    { serial
      programVersion := 0
      application := applicationId index
      rule := { index := 0 }
      key := ruleKey
      node := nodeId output
      kind := .forward
      effort := 0
      generation := 0
      inputs :=
        [{ node := nodeId (output - 2), version := leftVersion },
          { node := nodeId (output - 1), version := rightVersion }]
      writes := [nodeId output] }
  pure
    { view :=
      { id := applicationId index
        key := ruleKey
        offerClass := .invoke
        age := output % 3
        score := scoreAt index }
      action }

private def offerCount (n : Nat) : Nat := n - 2

private def budget (offers : Nat) : Policy.EngineBudgetView :=
  { actions := offers
    acceptedFacts := offers
    applications := offers }

private def offersFor (serial : Nat) (versions : Array Nat) (ids : Array Nat) :
    Option (Array (Search.Offer ApplicationId RuleKey)) :=
  ids.mapM (offer? serial versions)

private def session? (n : Nat) : Option (Search.Session Nat Nat ApplicationId RuleKey) := do
  let dag := program n
  let branch ← (State.Branch.startWithin (stateLimits n) dag (Array.replicate n 0)).toOption
  let offers ← offersFor 0 branch.versions (Array.range (offerCount n))
  Search.Session.startWithin (envelope n) measure branch #[rule] #[]
    (Array.replicate (offerCount n) 0) #[] 0 { index := 0 } offers
    (budget offers.size) false
    |>.toOption

private def mix (acc : UInt64) (value : Nat) : UInt64 :=
  acc * 0x9e3779b97f4a7c15 + UInt64.ofNat (value + 1)

private def updateState (comparisons : Nat)
    (offer : Policy.OfferView ApplicationId RuleKey) (state : PolicyState) : PolicyState :=
  { decisions := state.decisions + 1
    comparisons := state.comparisons + comparisons
    orderHash := mix state.orderHash offer.id.index }

private def first? (view : Policy.View Nat ApplicationId RuleKey) :=
  view.offers[0]?

private def staticBetter
    (left right : Policy.OfferView ApplicationId RuleKey) : Bool :=
  left.age < right.age || (left.age == right.age && left.id.index < right.id.index)

private def readiness (view : Policy.View Nat ApplicationId RuleKey)
    (offer : Policy.OfferView ApplicationId RuleKey) : Nat :=
  let output := offer.id.index + 2
  match view.facts.versions[output - 2]?, view.facts.versions[output - 1]? with
  | some left, some right => left + right
  | _, _ => 0

private def adaptiveBetter
    (view : Policy.View Nat ApplicationId RuleKey)
    (left right : Policy.OfferView ApplicationId RuleKey) : Bool :=
  let leftReady := readiness view left
  let rightReady := readiness view right
  rightReady < leftReady ||
    (leftReady == rightReady &&
      (right.score < left.score ||
        (left.score == right.score && left.id.index < right.id.index)))

private def best? (better : Policy.OfferView ApplicationId RuleKey →
    Policy.OfferView ApplicationId RuleKey → Bool)
    (view : Policy.View Nat ApplicationId RuleKey) :
    Option (Policy.OfferView ApplicationId RuleKey) × Nat := Id.run do
  let mut selected := none
  let mut comparisons := 0
  for index in [0:view.offers.size] do
    let some current := view.offers[index]? | return (none, comparisons)
    match selected with
    | none => selected := some current
    | some previous =>
        comparisons := comparisons + 1
        if better current previous then selected := some current
  return (selected, comparisons)

private def choose (kind : PolicyKind) (state : PolicyState)
    (view : Policy.View Nat ApplicationId RuleKey) :
    Policy.Step PolicyState ApplicationId RuleKey :=
  let (selected, comparisons) := match kind with
    | .fifo => (first? view, 0)
    | .staticRank => best? staticBetter view
    | .adaptive => best? (adaptiveBetter view) view
  match selected with
  | none => .stop state
  | some selected =>
      .select selected (updateState comparisons selected state)

private def policy (kind : PolicyKind) :
    Policy.Interface Nat PolicyState ApplicationId RuleKey :=
  { choose := choose kind }

private def callback (request : Search.Request Nat ApplicationId RuleKey) :=
  match request.facts.version? request.action.node with
  | none => Search.Reply.failure 0
  | some version =>
      Search.Reply.outcome
        { scope := request.scope
          serial := request.serial
          programVersion := request.programVersion
          offer := request.offer
          action := request.action
          updates :=
            #[{ programVersion := request.programVersion
                node := request.action.node
                previous := { node := request.action.node, version }
                fact := request.action.node.index + 1
                version := version + 1
                cause := request.offer.id.index }] }

private def advance? (kind : PolicyKind) (n : Nat)
    (session : Search.Session Nat Nat ApplicationId RuleKey) (state : PolicyState) :
    Option (Search.Session Nat Nat ApplicationId RuleKey × PolicyState) := do
  let choice ← (Search.chooseWithin (envelope n) measure (policy kind) state session).toOption
  match choice with
  | .select decision next =>
      let remainingIds := (session.offers.filter fun current =>
        current.view.id != decision.id).map (fun current => current.view.id.index)
      if remainingIds.size + 1 != session.offers.size then none else pure ()
      let applied ← (Search.invokeWithin (envelope n) measure callback session decision).toOption
      let updated ← match applied with
        | .applied updated => some updated
        | .stopped _ _ => none
      let remaining ← offersFor updated.serial updated.branch.versions remainingIds
      let refreshed ← (Search.Session.refreshWithin (envelope n) measure updated remaining
        (budget remaining.size) false).toOption
      pure (refreshed, next)
  | .dismiss _ _ | .stopped _ _ => none

private def report?
    (session : Search.Session Nat Nat ApplicationId RuleKey) (state : PolicyState) :
    Option Report := do
  let snapshot ← session.branch.checkedSnapshot?
  let mut semantic : UInt64 := 0
  for index in [0:snapshot.facts.size] do
    let fact ← snapshot.facts[index]?
    let version ← snapshot.versions[index]?
    semantic := mix (mix semantic fact) version
  pure
    { nodes := session.branch.program.nodes.size
      offers := session.offers.size
      decisions := state.decisions
      comparisons := state.comparisons
      updates := session.branch.history.size
      orderHash := state.orderHash
      semantic }

private def runFrom (kind : PolicyKind) (n : Nat)
    (session : Search.Session Nat Nat ApplicationId RuleKey) : Option Report := do
  let rec loop (fuel : Nat) (session : Search.Session Nat Nat ApplicationId RuleKey)
      (state : PolicyState) :
      Option (Search.Session Nat Nat ApplicationId RuleKey × PolicyState) := do
    if session.offers.isEmpty then return (session, state)
    match fuel with
    | 0 => none
    | fuel + 1 =>
        let (refreshed, next) ← advance? kind n session state
        loop fuel refreshed next
  let (session, state) ← loop (offerCount n) session {}
  report? session state

def runReport (kind : PolicyKind) (n : Nat) : Option Report := do
  let session ← session? n
  runFrom kind n session

private def runStepReport (offers : Nat) : Option Report := do
  let n := offers + 2
  let session ← session? n
  if offers == 0 then
    report? session {}
  else
    let (session, state) ← advance? .fifo n session {}
    report? session state

/-- One shared authenticated end-to-end transition, failing closed on error. -/
def runAuthenticatedStep (offers : Nat) : IO Report :=
  match runStepReport offers with
  | some report => pure report
  | none => throw <| IO.userError s!"authenticated decision step failed, offers={offers}"

private def canonicalInput : Nat := 128

private def expectedComparisons (n : Nat) : Nat :=
  let count := offerCount n
  count * (count - 1) / 2

private def canonicalFifoHash : UInt64 := 13333310190265569661

private def canonicalStaticHash : UInt64 := 9721628123875171393

private def canonicalAdaptiveHash : UInt64 := 558125824506216197

private def canonicalSemantic : UInt64 := 8880463590880745567

private def canary (input : Option Nat := none) : IO UInt32 := do
  let n := input.getD canonicalInput
  if n < 2 then
    IO.eprintln "decision benchmark requires at least two nodes"
    return 1
  let reports := [runReport .fifo n, runReport .staticRank n, runReport .adaptive n]
  IO.println s!"nodes={n} supported=arithmetic-dag"
  IO.println s!"fifo={repr reports[0]!}"
  IO.println s!"static-rank={repr reports[1]!}"
  IO.println s!"adaptive={repr reports[2]!}"
  IO.println "mixed-typed-events=out-of-scope(direct Runtime.State.stepWithin exists)"
  IO.println "split-tree=out-of-scope(direct Search.Result split/settle APIs exist)"
  match reports with
  | [some fifo, some staticRank, some adaptive] =>
      if fifo.nodes == n && staticRank.nodes == n && adaptive.nodes == n &&
          fifo.offers == 0 && staticRank.offers == 0 && adaptive.offers == 0 &&
          fifo.decisions == offerCount n &&
          fifo.comparisons == 0 && staticRank.comparisons == expectedComparisons n &&
          adaptive.comparisons == expectedComparisons n &&
          fifo.updates == offerCount n && staticRank.updates == offerCount n &&
          adaptive.updates == offerCount n && fifo.semantic == staticRank.semantic &&
          staticRank.semantic == adaptive.semantic &&
          (n != 128 ||
            (fifo.orderHash == canonicalFifoHash &&
             staticRank.orderHash == canonicalStaticHash &&
             adaptive.orderHash == canonicalAdaptiveHash &&
             fifo.semantic == canonicalSemantic)) then
        return 0
      else
        IO.eprintln "decision benchmark logical-count canary failed"
        return 1
  | _ =>
      IO.eprintln "decision benchmark fixture failed to build"
      return 1

/-
Fixed end-to-end cost attribution. Each rung includes runtime reads of the
offer count, arithmetic-program and branch setup, initial offer construction,
checked session authentication, one FIFO `chooseWithin` / `invokeWithin`
transition, complete surviving-offer regeneration and refresh authentication,
the checked snapshot walk used to build `Report`, and the fixed harness's
timed result hashing. Complete-view duplicate-ID validation scans prior offers,
so the measurements are expected to show a quadratic-dominated common cost.
They are empirical fixed points, not an automatic complexity verdict or a
policy comparison.
-/
initialize timingOffersRef : IO.Ref (Array Nat) ←
  IO.mkRef #[1024, 2048, 4096, 8192, 16384, 32768]

private def runFixed (index : Nat) : IO Report := do
  let inputs ← timingOffersRef.get
  match inputs[index]? with
  | some offers => runAuthenticatedStep offers
  | none => throw <| IO.userError s!"missing fixed decision input, index={index}"

namespace Offers1024
def run (_ : Unit) : IO Report := runFixed 0
end Offers1024

namespace Offers2048
def run (_ : Unit) : IO Report := runFixed 1
end Offers2048

namespace Offers4096
def run (_ : Unit) : IO Report := runFixed 2
end Offers4096

namespace Offers8192
def run (_ : Unit) : IO Report := runFixed 3
end Offers8192

namespace Offers16384
def run (_ : Unit) : IO Report := runFixed 4
end Offers16384

namespace Offers32768
def run (_ : Unit) : IO Report := runFixed 5
end Offers32768

setup_fixed_benchmark Offers1024.run where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some 0xbbd09a2695e38e01
}

setup_fixed_benchmark Offers2048.run where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some 0x6e4e62b8e475bb32
}

setup_fixed_benchmark Offers4096.run where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some 0xcd7bca91050befed
}

setup_fixed_benchmark Offers8192.run where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some 0x5a04b99431d279fc
}

setup_fixed_benchmark Offers16384.run where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some 0xffdc8b53fcda1fd5
}

setup_fixed_benchmark Offers32768.run where {
  repeats := 5
  maxSecondsPerCall := 5.0
  expectedHash := some 0x284aed8dace21e10
}

end Hex.Interval.DecisionBench

def main (args : List String) : IO UInt32 :=
  match args with
  | ["canary"] => Hex.Interval.DecisionBench.canary none
  | ["canary", n] => match n.toNat? with
    | some n => Hex.Interval.DecisionBench.canary (some n)
    | none => pure 2
  | _ => LeanBench.Cli.dispatch args
