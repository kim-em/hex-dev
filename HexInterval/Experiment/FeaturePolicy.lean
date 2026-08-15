/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.AdaptivePolicy
public import HexInterval.Experiment.PolicyFeature

@[expose] public section

/-!
# Bounded package-feature scoring

This adapter combines the package-opaque feedback score from `AdaptivePolicy`
with explicitly configured package features.  The scheduler understands only
versioned feature addresses and signed integer weights.  It contains no cases
for facts, functions, operations, or package families.

Compatible feature data changes ordering only.  A decorator/scorer limit
mismatch or oversized learned score fails closed with no selection.  For a
view returned by the decorator, a successful choice is the exact
engine-owned `OfferView` which that decorator retained.  The public view type
also admits hand-built test data; scoring it does not authenticate feature
provenance or its base view.  In either case the ordinary policy session
remains the authority for freshness and transition validity.
-/

namespace Hex.Interval.Experiment.FeaturePolicy

open Propagator Propagator.Policy PolicyFeature

/-- Globally unambiguous configured feature address. -/
structure Address where
  provider : ProviderKey
  key : Nat
  deriving DecidableEq, Repr

/-- One signed linear scoring term.  Negative weights and feature values are
both meaningful. -/
structure Term where
  address : Address
  weight : Int
  deriving DecidableEq, Repr

/-- Every configuration or traversal dimension owned by this adapter has an
independent explicit bound.  `maxPairChecks` bounds feature/term comparisons,
not provider callback work performed before decoration returns. -/
structure Limits where
  maxTerms : Nat
  maxProviderComponent : Nat
  maxFeatureKey : Nat
  maxWeight : Nat
  maxOffers : Nat
  maxFeaturesPerOffer : Nat
  maxPairChecks : Nat
  maxFeatureValue : Nat
  maxScore : Nat
  deriving DecidableEq, Repr

/-- Transactional configuration rejection. -/
inductive BuildError where
  | termLimit
  | providerComponentLimit (address : Address)
  | featureKeyLimit (address : Address)
  | weightLimit (address : Address) (weight : Int)
  | duplicateAddress (address : Address)
  deriving DecidableEq, Repr

/-- Immutable validated scoring configuration. -/
structure Plan where
  private mk ::
  terms : Array Term

private def makePlan (terms : Array Term) : Plan := { terms }

private def duplicateAddress? (terms : List Term) : Option Address :=
  match terms with
  | [] => none
  | term :: rest =>
      if rest.any (fun other => other.address == term.address) then
        some term.address
      else
        duplicateAddress? rest

/-- Validate a complete scoring configuration before making any part of it
available to selection.  Caller order is retained as the deterministic
saturating-add order. -/
opaque Plan.buildWithin (limits : Limits) (terms : Array Term) :
    Except BuildError Plan :=
  if limits.maxTerms < terms.size then
    .error .termLimit
  else
    match terms.find? fun term =>
        limits.maxProviderComponent < term.address.provider.family ||
          limits.maxProviderComponent < term.address.provider.version with
    | some term => .error (.providerComponentLimit term.address)
    | none =>
        match terms.find? fun term => limits.maxFeatureKey < term.address.key with
        | some term => .error (.featureKeyLimit term.address)
        | none =>
            match terms.find? fun term => limits.maxWeight < term.weight.natAbs with
            | some term => .error (.weightLimit term.address term.weight)
            | none =>
                match duplicateAddress? terms.toList with
                | some address => .error (.duplicateAddress address)
                | none => .ok (makePlan terms)

/-- Runtime rejection is also transactional: no selection is returned. -/
inductive Error where
  | plan (error : BuildError)
  | offerAlignment
  | offerLimit
  | offerFeatureLimit (offer : OfferId)
  | pairCheckLimit
  | providerComponentLimit (offer : OfferId) (address : Address)
  | featureKeyLimit (offer : OfferId) (address : Address)
  | featureValueLimit (offer : OfferId) (address : Address) (value : Int)
  | learnedScoreLimit (offer : OfferId) (score : Nat)
  deriving DecidableEq, Repr

def clamp (limit : Nat) (value : Int) : Int :=
  let bound := Int.ofNat limit
  if value < -bound then -bound else if bound < value then bound else value

def addSat (limit : Nat) (left right : Int) : Int :=
  clamp limit (left + right)

def contribution (limits : Limits) (offer : FeaturedOffer)
    (term : Term) : Except Error Int :=
  match offer.feature? term.address.provider term.address.key with
  | none => .ok 0
  | some value =>
      if limits.maxFeatureValue < value.natAbs then
        .error (.featureValueLimit offer.base.id term.address value)
      else
        .ok (clamp limits.maxScore (term.weight * value))

/-- Conservative upper bound on feature/term comparisons made by linear
lookup.  Sizes are checked before this multiplication is performed. -/
def pairChecks (plan : Plan) (offers : Array FeaturedOffer) : Nat :=
  offers.foldl (fun total offer => total + plan.terms.size * offer.features.size) 0

def preflight (limits : Limits) (plan : Plan)
    (view : PolicyFeature.View Fact) : Except Error Unit := do
  match Plan.buildWithin limits plan.terms with
  | .error error => throw (.plan error)
  | .ok _ => pure ()
  if limits.maxOffers < view.base.offers.size ||
      limits.maxOffers < view.offers.size then
    throw .offerLimit
  if view.offers.map (fun offer => offer.base) ≠ view.base.offers then
    throw Error.offerAlignment
  for offer in view.offers do
    if limits.maxFeaturesPerOffer < offer.features.size then
      throw (.offerFeatureLimit offer.base.id)
    for feature in offer.features do
      let address : Address := { provider := feature.provider, key := feature.key }
      if limits.maxProviderComponent < feature.provider.family ||
          limits.maxProviderComponent < feature.provider.version then
        throw (.providerComponentLimit offer.base.id address)
      if limits.maxFeatureKey < feature.key then
        throw (.featureKeyLimit offer.base.id address)
      if limits.maxFeatureValue < feature.value.natAbs then
        throw (.featureValueLimit offer.base.id address feature.value)
  if limits.maxPairChecks < pairChecks plan view.offers then throw .pairCheckLimit

def featureScore (limits : Limits) (plan : Plan)
    (offer : FeaturedOffer) : Except Error Int := do
  let mut score := 0
  for term in plan.terms do
    score := addSat limits.maxScore score (<- contribution limits offer term)
  pure score

structure Ranked where
  offer : OfferView
  fair : Bool
  stage : Nat
  score : Int

def rank (limits : Limits) (state : AdaptivePolicy.State) (plan : Plan)
    (offer : FeaturedOffer) : Except Error Ranked := do
  let base := AdaptivePolicy.rankOffer state offer.base
  if limits.maxScore < base.score then
    throw (.learnedScoreLimit offer.base.id base.score)
  let learned := Int.ofNat base.score
  let score := addSat limits.maxScore learned (<- featureScore limits plan offer)
  pure { offer := offer.base, fair := base.fair, stage := base.stage, score }

/-- Preserve adaptive fairness and staged semantic tiers.  Configured feature
score participates only where learned score did: after fairness and stage, and
before age and stable decorated-view order. -/
def better (candidate current : Ranked) : Bool :=
  (candidate.fair && !current.fair) ||
    (candidate.fair == current.fair && candidate.stage < current.stage) ||
    (candidate.fair == current.fair && candidate.stage == current.stage &&
      (current.score < candidate.score ||
        (current.score == candidate.score && current.offer.age < candidate.offer.age)))

/-- Rank a bounded, aligned featured view.  Only `PolicyFeature.decorate`
authenticates provider provenance; this function deliberately also accepts
hand-built experiment data.  The returned value is always the exact
`FeaturedOffer.base`, and ordinary engine revalidation remains authoritative.
Unknown and missing configured features contribute zero. -/
def choose? (limits : Limits) (state : AdaptivePolicy.State) (plan : Plan)
    (view : PolicyFeature.View Fact) : Except Error (Option OfferView) := do
  preflight limits plan view
  let mut best : Option Ranked := none
  for offer in view.offers do
    if StagedPolicy.allowed state.config.staged offer.base then
      let candidate <- rank limits state plan offer
      best := match best with
        | none => some candidate
        | some current => if better candidate current then some candidate else best
  pure (best.map fun ranked => ranked.offer)

end Hex.Interval.Experiment.FeaturePolicy
