/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.PolicyFeature

/-!
# Package policy-feature conformance

Two unrelated providers decorate the same immutable policy view.  One reads a
fact at an invocation anchor; the other recognizes a split offer.  The generic
decorator contains neither interpretation.
-/

namespace Hex.Interval.PolicyFeatureConformance

local notation "OfferView" =>
  Hex.Interval.Policy.OfferView _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "Selection" =>
  Hex.Interval.Policy.Decision _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey
local notation "ScopeId" => Hex.Interval.Policy.ScopeId
local notation "OfferClass" => Hex.Interval.Policy.OfferClass

open Experiment Propagator Propagator.Policy PolicyFeature

private def node (index : Nat) : NodeId := { index }

private def invocation (index : Nat) : InvocationKey :=
  { scope := { index := 0 }
    programVersion := 7
    application := { index }
    rule := { name := "policy-feature.width", schema := 2 }
    anchor := node index
    kind := .forward
    effort := 0
    inputs := [] }

private def invokeOffer : OfferView :=
  { id := .application { index := 0 }
    key := .invoke (invocation 0)
    offerClass := .invoke
    age := 3 }

private def splitOffer : OfferView :=
  { id := .suggestion { index := 0 }
    key := .split (invocation 1) { node := node 1, version := 4 }
      0 .smallLandmark
    offerClass := .split
    age := 1 }

private def sameOffer (left right : OfferView) : Bool :=
  left == right

#guard !sameOffer invokeOffer { invokeOffer with score := 1 }

private def sameOffers : List OfferView -> List OfferView -> Bool
  | [], [] => true
  | left :: lefts, right :: rights =>
      sameOffer left right && sameOffers lefts rights
  | _, _ => false

private def baseView : (Hex.Interval.Policy.View Nat _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey) :=
  { scope := { index := 0 }
    serial := 9
    programVersion := 7
    offers := #[invokeOffer, splitOffer]
    facts := { facts := #[6, 11], versions := #[2, 4], contradictory := false }
    remaining :=
      { actions := 8
        matcherVisits := 8
        acceptedFacts := 8
        nodes := 8
        applications := 8
        equalities := 8
        retainedSuggestions := 8
        instances := 8
        queueEntries := 8
        generation := 8 }
    incomplete := false }

private def sameView (left right : (Hex.Interval.Policy.View Nat _root_.Hex.Interval.Experiment.Propagator.Policy.OfferId _root_.Hex.Interval.Experiment.Propagator.Policy.OfferKey)) : Bool :=
  left.scope == right.scope && left.serial == right.serial &&
    left.programVersion == right.programVersion &&
    sameOffers left.offers.toList right.offers.toList &&
    left.facts.facts == right.facts.facts &&
    left.facts.versions == right.facts.versions &&
    left.facts.contradictory == right.facts.contradictory &&
    left.remaining == right.remaining && left.incomplete == right.incomplete

private def widthKey : ProviderKey := { family := 41, version := 2 }
private def goalKey : ProviderKey := { family := 73, version := 1 }

/-- A domain package can expose a bounded width surrogate without teaching
the scheduler what a `Nat` fact means. -/
private def widthProvider : Provider Nat :=
  { key := widthKey
    features := fun request =>
      match request.offer.key with
      | .invoke invocation =>
          match request.facts.fact? invocation.anchor with
          | some width => #[{ key := 0, value := Int.ofNat width }]
          | none => #[]
      | _ => #[] }

/-- A frontend-owned goal provider can independently recognize a useful split
and publish signed closing potential. -/
private def goalProvider : Provider Nat :=
  { key := goalKey
    features := fun request =>
      match request.offer.key with
      | .invoke invocation =>
          if invocation.anchor == node 0 then #[{ key := 1, value := -2 }] else #[]
      | .split _ target point reason =>
          if target.node == node 1 && point == 0 && reason == .smallLandmark then
            #[{ key := 3, value := -4 }, { key := 5, value := 9 }]
          else
            #[]
      | _ => #[] }

private def limits : PolicyFeature.Limits :=
  { maxProviders := 4
    maxProviderChecks := 8
    maxFeaturesPerProvider := 3
    maxFeaturesPerOffer := 4
    maxTotalFeatures := 6
    maxFeatureKey := 10
    maxFeatureValue := 10 }

private def featured? : Option (PolicyFeature.View Nat) := do
  let registry <- (Registry.buildWithin limits #[widthProvider, goalProvider]).toOption
  (decorate limits registry baseView).toOption

/- Stable order is offer-major, provider-major, and then provider-local.  Empty
responses still consume one provider check. -/
#guard
  featured?.any fun view =>
    sameView view.base baseView &&
      view.metrics == { providerChecks := 4, emittedFeatures := 4 } &&
      view.offers.size == 2 &&
      match view.offers[0]?, view.offers[1]? with
      | some first, some second =>
          sameOffer first.base invokeOffer && first.features.size == 2 &&
            first.feature? widthKey 0 == some 6 &&
            first.features[0]?.any (fun feature => feature.provider == widthKey) &&
            first.features[1]?.any (fun feature =>
              feature.provider == goalKey && feature.key == 1 && feature.value == -2) &&
            sameOffer second.base splitOffer && second.features.size == 2 &&
            second.features[0]?.any (fun feature =>
              feature.provider == goalKey && feature.key == 3 && feature.value == -4) &&
            second.features[1]?.any (fun feature =>
              feature.provider == goalKey && feature.key == 5 && feature.value == 9)
      | _, _ => false

private def duplicateRegistry : Except Error (Registry Nat) :=
  Registry.buildWithin limits #[widthProvider, { widthProvider with features := fun _ => #[] }]

#guard
  match duplicateRegistry with
  | .error (.duplicateProvider key) => key == widthKey
  | _ => false

/- Provider count is bounded when the immutable registry is assembled. -/
#guard
  match Registry.buildWithin { limits with maxProviders := 1 }
      #[widthProvider, goalProvider] with
  | .error .providerLimit => true
  | _ => false

private def duplicateOutput : Provider Nat :=
  { key := { family := 99, version := 1 }
    features := fun _ => #[{ key := 1, value := 2 }, { key := 1, value := 3 }] }

#guard
  match Registry.buildWithin limits #[duplicateOutput] with
  | .error _ => false
  | .ok registry =>
      match decorate limits registry baseView with
      | .error (.duplicateFeature provider key offer) =>
          provider == duplicateOutput.key && key == 1 && offer == invokeOffer.id
      | _ => false

private def oversizedValue : Provider Nat :=
  { key := { family := 100, version := 1 }
    features := fun _ => #[{ key := 2, value := -11 }] }

#guard
  match Registry.buildWithin limits #[oversizedValue] with
  | .error _ => false
  | .ok registry =>
      match decorate limits registry baseView with
      | .error (.featureValueLimit provider key value) =>
          provider == oversizedValue.key && key == 2 && value == -11
      | _ => false

private def oversizedKey : Provider Nat :=
  { key := { family := 100, version := 2 }
    features := fun _ => #[{ key := 11, value := 0 }] }

#guard
  match Registry.buildWithin limits #[oversizedKey] with
  | .error _ => false
  | .ok registry =>
      match decorate limits registry baseView with
      | .error (.featureKeyLimit provider key) =>
          provider == oversizedKey.key && key == 11
      | _ => false

private def tooMany : Provider Nat :=
  { key := { family := 101, version := 1 }
    features := fun _ =>
      #[{ key := 0, value := 0 }, { key := 1, value := 0 },
        { key := 2, value := 0 }, { key := 3, value := 0 }] }

#guard
  match Registry.buildWithin limits #[tooMany] with
  | .error _ => false
  | .ok registry =>
      match decorate limits registry baseView with
      | .error (.providerFeatureLimit provider offer) =>
          provider == tooMany.key && offer == invokeOffer.id
      | _ => false

/- The provider/offer cross product is rejected before any package output is
accepted into a partial decorated view. -/
#guard
  match Registry.buildWithin limits #[widthProvider, goalProvider] with
  | .error _ => false
  | .ok registry =>
      match decorate { limits with maxProviderChecks := 3 } registry baseView with
      | .error .providerCheckLimit => true
      | _ => false

/- Per-offer and whole-view caps are independent of the provider-local cap. -/
#guard
  match Registry.buildWithin limits #[widthProvider, goalProvider] with
  | .error _ => false
  | .ok registry =>
      match decorate { limits with maxFeaturesPerOffer := 1 } registry baseView with
      | .error (.offerFeatureLimit offer) => offer == invokeOffer.id
      | _ => false

#guard
  match Registry.buildWithin limits #[widthProvider, goalProvider] with
  | .error _ => false
  | .ok registry =>
      match decorate { limits with maxTotalFeatures := 3 } registry baseView with
      | .error .totalFeatureLimit => true
      | _ => false

/- Decoration rechecks the provider-count limit rather than trusting the
limits used by an earlier registry build. -/
#guard
  match Registry.buildWithin limits #[widthProvider] with
  | .error _ => false
  | .ok registry =>
      match decorate { limits with maxProviders := 0 } registry baseView with
      | .error .providerLimit => true
      | _ => false

/- Zero providers are valid under zero count/check/feature limits and retain
the complete base offers without manufacturing features. -/
#guard
  match Registry.buildWithin { limits with maxProviders := 0 } #[] with
  | .error _ => false
  | .ok registry =>
      match decorate
          { limits with
            maxProviders := 0
            maxProviderChecks := 0
            maxFeaturesPerProvider := 0
            maxFeaturesPerOffer := 0
            maxTotalFeatures := 0 }
          registry baseView with
      | .ok view =>
          sameView view.base baseView &&
            view.offers.size == baseView.offers.size &&
            view.metrics == { providerChecks := 0, emittedFeatures := 0 } &&
            match view.offers[0]?, view.offers[1]? with
            | some first, some second =>
                sameOffer first.base invokeOffer && first.features.isEmpty &&
                  sameOffer second.base splitOffer && second.features.isEmpty
            | _, _ => false
      | .error _ => false

end Hex.Interval.PolicyFeatureConformance
