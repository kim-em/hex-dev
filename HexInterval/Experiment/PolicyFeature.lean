/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Experiment.Policy

@[expose] public section

/-!
# Bounded package features for interval-search policies

An interval or function package may know that one live offer is more useful
than another, even though the generic scheduler must not know how to interpret
its facts or operations.  This experiment gives such packages a stateless,
versioned feature callback.  A callback receives one immutable policy snapshot
and one engine-owned offer; the decorator accepts only bounded integer output.

Callbacks are evaluated while a view is decorated; they are never retained in
the policy state.  The decorated offer keeps the complete engine-owned offer,
so choosing it still goes through the ordinary freshness and semantic-key
checks.  A stale or dishonest feature can therefore change search order, but
cannot authorize an engine transition, enter proof evidence, or bypass replay
validation of the trace that search eventually generates.
-/

namespace Hex.Interval.Experiment.PolicyFeature

open Propagator Propagator.Policy

/-- Versioned identity of one independently registered feature provider.
Changing the meaning of any local feature requires a new provider version. -/
structure ProviderKey where
  family : Nat
  version : Nat
  deriving DecidableEq, Repr

/-- A provider-local feature before its owner is attached by the registry. -/
structure LocalFeature where
  key : Nat
  value : Int
  deriving DecidableEq, Repr

/-- Globally unambiguous feature address and its bounded integer value. -/
structure Feature where
  provider : ProviderKey
  key : Nat
  value : Int
  deriving DecidableEq, Repr

/-- Exact immutable input to a feature provider.

The request deliberately contains no package cache and grants no mutation
authority.  A goal-oriented provider may close over a fixed frontend goal;
the provider version must change when the interpretation of that configuration
changes. -/
structure Request (Fact : Type) where
  scope : ScopeId
  serial : Nat
  programVersion : Nat
  facts : Snapshot Fact
  remaining : EngineBudgetView
  incomplete : Bool
  offer : OfferView

/-- Stateless companion contribution from one interval or frontend package.
Returning an empty array means this provider contributes nothing for the offer. -/
structure Provider (Fact : Type) where
  key : ProviderKey
  features : Request Fact -> Array LocalFeature

/-- Every accepted output/count dimension which a provider can make large has
an independent cap.  Provider identities are opaque registry addresses. -/
structure Limits where
  maxProviders : Nat
  maxProviderChecks : Nat
  maxFeaturesPerProvider : Nat
  maxFeaturesPerOffer : Nat
  maxTotalFeatures : Nat
  maxFeatureKey : Nat
  maxFeatureValue : Nat
  deriving DecidableEq, Repr

/-- Exact rejection reason. Decoration is transactional: errors return no
partially featured view. -/
inductive Error where
  | providerLimit
  | duplicateProvider (key : ProviderKey)
  | providerCheckLimit
  | providerFeatureLimit (provider : ProviderKey) (offer : OfferId)
  | offerFeatureLimit (offer : OfferId)
  | totalFeatureLimit
  | featureKeyLimit (provider : ProviderKey) (key : Nat)
  | featureValueLimit (provider : ProviderKey) (key : Nat) (value : Int)
  | duplicateFeature (provider : ProviderKey) (key : Nat) (offer : OfferId)
  deriving DecidableEq, Repr

/-- Immutable provider order established by successful registry assembly. -/
structure Registry (Fact : Type) where
  private mk ::
  providers : Array (Provider Fact)

private def makeRegistry (providers : Array (Provider Fact)) : Registry Fact :=
  { providers }

namespace Registry

private def duplicateProvider? (providers : List (Provider Fact)) : Option ProviderKey :=
  match providers with
  | [] => none
  | provider :: rest =>
      if rest.any (fun other => other.key == provider.key) then
        some provider.key
      else
        duplicateProvider? rest

/-- Assemble providers in caller order after bounding and checking identities. -/
opaque buildWithin (limits : Limits) (providers : Array (Provider Fact)) :
    Except Error (Registry Fact) :=
  if limits.maxProviders < providers.size then
    .error .providerLimit
  else
    match duplicateProvider? providers.toList with
    | some key => .error (.duplicateProvider key)
    | none => .ok (makeRegistry providers)

end Registry

/-- One engine offer decorated with package data.  `base` is returned unchanged
when a policy selects this item. -/
structure FeaturedOffer where
  base : OfferView
  features : Array Feature

/-- Deterministic callback/output counts reported by one successful decoration. -/
structure Metrics where
  providerChecks : Nat
  emittedFeatures : Nat
  deriving DecidableEq, Repr

/-- A policy view plus aligned featured offers.  The base view remains the
freshness authority. -/
structure View (Fact : Type) where
  base : Policy.View Fact
  offers : Array FeaturedOffer
  metrics : Metrics

private def request (view : Policy.View Fact) (offer : OfferView) : Request Fact :=
  { scope := view.scope
    serial := view.serial
    programVersion := view.programVersion
    facts := view.facts
    remaining := view.remaining
    incomplete := view.incomplete
    offer }

private def validValue (limit : Nat) (value : Int) : Bool :=
  value.natAbs <= limit

/-- Attach package features in stable offer-major, provider-major, local order.

The complete provider/offer cross product is preflight-counted before any
callback is entered.  Returned arrays are then checked incrementally against
per-provider, per-offer, whole-view, key, and value limits. -/
opaque decorate (limits : Limits) (registry : Registry Fact)
    (view : Policy.View Fact) : Except Error (View Fact) := do
  if limits.maxProviders < registry.providers.size then throw .providerLimit
  let checks := registry.providers.size * view.offers.size
  if limits.maxProviderChecks < checks then throw .providerCheckLimit
  let mut decorated := #[]
  let mut total := 0
  for offer in view.offers do
    let mut features := #[]
    for provider in registry.providers do
      let emitted := provider.features (request view offer)
      if limits.maxFeaturesPerProvider < emitted.size then
        throw (.providerFeatureLimit provider.key offer.id)
      for feature in emitted do
        if limits.maxFeatureKey < feature.key then
          throw (.featureKeyLimit provider.key feature.key)
        if !validValue limits.maxFeatureValue feature.value then
          throw (.featureValueLimit provider.key feature.key feature.value)
        if features.any (fun old =>
            old.provider == provider.key && old.key == feature.key) then
          throw (.duplicateFeature provider.key feature.key offer.id)
        if limits.maxFeaturesPerOffer <= features.size then
          throw (.offerFeatureLimit offer.id)
        if limits.maxTotalFeatures <= total then
          throw .totalFeatureLimit
        features := features.push
          { provider := provider.key, key := feature.key, value := feature.value }
        total := total + 1
    decorated := decorated.push { base := offer, features }
  pure
    { base := view
      offers := decorated
      metrics := { providerChecks := checks, emittedFeatures := total } }

/-- Exact lookup used by policies which understand a configured feature key.
Unknown features remain inert. -/
def FeaturedOffer.feature? (offer : FeaturedOffer)
    (provider : ProviderKey) (key : Nat) : Option Int :=
  (offer.features.find? fun feature =>
    feature.provider == provider && feature.key == key).map (fun feature => feature.value)

end Hex.Interval.Experiment.PolicyFeature
