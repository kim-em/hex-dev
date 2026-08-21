/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.State

@[expose] public section

/-!
# Bounded search-policy contracts

This module is the supported, function-agnostic boundary between an interval
controller and a replaceable search policy.  The controller supplies an exact
immutable view of already-authenticated offers.  A policy can retain private
state and return one unchanged offer, dismiss one unchanged offer, or stop; it
cannot construct an action or authorize a state transition.

The checked adapter bounds retained offer count, declared score magnitude, and
package-defined key size, pair, and logical-work measures.  The measurement
callbacks and equality on arbitrary identifiers, semantic keys, and
reconstructed facts are an explicit non-preemptible envelope: they may traverse
nested Lean objects before returning a bounded number.  Successful checking
bounds only the retained decoded view and subsequent controller work, not
callback allocation or time.
-/

namespace Hex.Interval.Policy

/-- Branch-local policy scope.  A compact index is meaningful only in the
controller state which issued it. -/
structure ScopeId where
  index : Nat
  deriving DecidableEq, Repr

/-- Versioned identity of an external policy implementation.  No implementation
is selected as the supported default. -/
structure PolicyKey where
  name : String
  version : Nat
  deriving DecidableEq, Repr

/-- Coarse controller-owned classification available to generic policies. -/
inductive OfferClass where
  | invoke
  | equality
  | retry
  | instantiate
  | split
  deriving DecidableEq, Repr

/-- Logical retained cost returned by package-owned measurement callbacks. -/
structure Cost where
  bytes : Nat := 0
  pairs : Nat := 0
  work : Nat := 0
  deriving DecidableEq, Repr

def Cost.add (left right : Cost) : Cost :=
  { bytes := left.bytes + right.bytes
    pairs := left.pairs + right.pairs
    work := left.work + right.work }

/-- Independent caps for one policy view. -/
structure Limits where
  maxOffers : Nat
  maxBytes : Nat
  maxPairs : Nat
  maxWork : Nat
  maxScore : Nat
  deriving DecidableEq, Repr

/-- Complete immutable policy-facing description of one engine-owned offer.
`Id` and `SemanticKey` remain controller-selected stable types. -/
structure OfferView (Id SemanticKey : Type) where
  id : Id
  key : SemanticKey
  offerClass : OfferClass
  age : Nat
  /-- Optional bounded generic score.  Zero leaves scoring entirely to an
  experimental or package-owned policy. -/
  score : Int := 0
  deriving DecidableEq

/-- Remaining engine resources exposed opaquely to the policy contract. -/
structure EngineBudgetView where
  actions : Nat := 0
  matcherVisits : Nat := 0
  acceptedFacts : Nat := 0
  nodes : Nat := 0
  applications : Nat := 0
  equalities : Nat := 0
  retainedSuggestions : Nat := 0
  instances : Nat := 0
  queueEntries : Nat := 0
  generation : Nat := 0
  deriving DecidableEq, Repr

/-- Exact immutable input to one policy callback. -/
structure View (Fact Id SemanticKey : Type) where
  scope : ScopeId
  serial : Nat
  programVersion : Nat
  offers : Array (OfferView Id SemanticKey)
  facts : Snapshot Fact
  remaining : EngineBudgetView := {}
  incomplete : Bool

/-- One exact echoed policy choice.  `expected` includes every exposed offer
field, so mutating its class, age, score, identifier, or semantic key is stale. -/
structure Decision (Id SemanticKey : Type) where
  scope : ScopeId
  serial : Nat
  programVersion : Nat
  id : Id
  expected : SemanticKey
  offerClass : OfferClass := .invoke
  age : Nat := 0
  score : Int := 0
  remaining : EngineBudgetView := {}
  deriving DecidableEq

/-- External policy result.  Only an exact view member can later pass
`revalidate`; `stop` is always conservative. -/
inductive Step (PolicyState Id SemanticKey : Type)
  | select (offer : OfferView Id SemanticKey) (next : PolicyState)
  | dismiss (offer : OfferView Id SemanticKey) (next : PolicyState)
  | stop (next : PolicyState)

/-- Replaceable policy callback.  Its implementation is outside the
preemptible resource envelope and has no state-transition or proof authority. -/
structure Interface (Fact PolicyState Id SemanticKey : Type) where
  choose : PolicyState -> View Fact Id SemanticKey -> Step PolicyState Id SemanticKey

/-- Package-owned exact logical measurements.  Both callbacks, and equality on
their inputs during validation, are non-preemptible. -/
structure Measure (Id SemanticKey : Type) where
  id : Id -> Cost
  key : SemanticKey -> Cost

inductive Error where
  | invalidProgram
  | malformedState
  | offerLimit
  | byteLimit
  | pairLimit
  | workLimit
  | scoreLimit
  | duplicateId
  | wrongScope
  | staleSerial
  | staleProgram
  | staleBudget
  | missingOffer
  | mutatedOffer
  deriving DecidableEq, Repr

def addWithin (limits : Limits) (left right : Cost) : Except Error Cost := do
  if limits.maxBytes < right.bytes || limits.maxBytes - right.bytes < left.bytes then
    throw .byteLimit
  if limits.maxPairs < right.pairs || limits.maxPairs - right.pairs < left.pairs then
    throw .pairLimit
  if limits.maxWork < right.work || limits.maxWork - right.work < left.work then
    throw .workLimit
  pure (left.add right)

variable {Fact Id SemanticKey Cause PolicyState : Type}

/-- Validate the bounded offer portion of a view whose program and fact-array
alignment have already been authenticated by the caller. -/
def checkOffersWithin [DecidableEq Id] (limits : Limits)
    (measure : Measure Id SemanticKey) (view : View Fact Id SemanticKey) : Except Error Cost := do
  if limits.maxOffers < view.offers.size then throw .offerLimit
  let mut total : Cost := {}
  for index in [0:view.offers.size] do
    let some offer := view.offers[index]? | throw .malformedState
    for prior in [0:index] do
      let some previous := view.offers[prior]? | throw .malformedState
      if previous.id == offer.id then throw .duplicateId
    if limits.maxScore < offer.score.natAbs then throw .scoreLimit
    total <- addWithin limits total (measure.id offer.id)
    total <- addWithin limits total (measure.key offer.key)
  pure total

/-- Validate all bounded retained dimensions of a complete view.  No prefix is
returned on failure. -/
def checkViewWithin [DecidableEq Id] (limits : Limits) (measure : Measure Id SemanticKey)
    (program : Program) (view : View Fact Id SemanticKey) : Except Error Cost := do
  if !program.check then throw .invalidProgram
  if view.facts.facts.size != program.nodes.size ||
      view.facts.versions.size != program.nodes.size then
    throw .malformedState
  checkOffersWithin limits measure view

/-- Construct the exact decision which an external policy must return. -/
def select (view : View Fact Id SemanticKey) (offer : OfferView Id SemanticKey) :
    Decision Id SemanticKey :=
  { scope := view.scope
    serial := view.serial
    programVersion := view.programVersion
    id := offer.id
    expected := offer.key
    offerClass := offer.offerClass
    age := offer.age
    score := offer.score
    remaining := view.remaining
  }

/-- Transactionally revalidate a policy choice against the complete current
view.  Success returns the controller-owned offer, never the policy's copy. -/
def revalidate [DecidableEq Id] [DecidableEq SemanticKey]
    (view : View Fact Id SemanticKey) (decision : Decision Id SemanticKey) :
    Except Error (OfferView Id SemanticKey) := do
  if decision.scope != view.scope then throw .wrongScope
  if decision.serial != view.serial then throw .staleSerial
  if decision.programVersion != view.programVersion then throw .staleProgram
  if decision.remaining != view.remaining then throw .staleBudget
  let some offer := view.offers.find? fun offer => offer.id == decision.id
    | throw .missingOffer
  if decision.expected != offer.key || decision.offerClass != offer.offerClass ||
      decision.age != offer.age || decision.score != offer.score then
    throw .mutatedOffer
  pure offer

/-- Validate state/program alignment as well as bounded view retention before
accepting a choice.  Branch reconstruction and program validation happen once;
comparison of arbitrary reconstructed facts remains non-preemptible.  Runtime
success remains data, never theorem evidence. -/
def checkDecisionWithin [DecidableEq Fact] [DecidableEq Id] [DecidableEq SemanticKey]
    (limits : Limits) (measure : Measure Id SemanticKey)
    (branch : State.Branch Fact Cause) (view : View Fact Id SemanticKey)
    (decision : Decision Id SemanticKey) : Except Error (OfferView Id SemanticKey) := do
  let some snapshot := branch.checkedSnapshot? | throw .malformedState
  if branch.programVersion != view.programVersion ||
      snapshot.facts != view.facts.facts || snapshot.versions != view.facts.versions ||
      snapshot.contradictory != view.facts.contradictory then
    throw .malformedState
  let _ <- checkOffersWithin limits measure view
  revalidate view decision

end Hex.Interval.Policy
