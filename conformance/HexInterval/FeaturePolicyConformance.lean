/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexInterval.Experiment.FeaturePolicy

/-!
# Bounded package-feature policy conformance

Two unrelated providers change otherwise-tied width and goal/split choices.
The policy sees only configured addresses and signed integers.
-/

namespace Hex.Interval.FeaturePolicyConformance

open Experiment Propagator Propagator.Policy PolicyFeature FeaturePolicy

private def node (index : Nat) : NodeId := { index }

private def invocation (index : Nat) (kind : ActionKind := .forward) : InvocationKey :=
  { scope := { index := 0 }
    programVersion := 3
    application := { index }
    rule := { name := "feature-policy.test", schema := 1 }
    anchor := node index
    kind
    effort := 0
    inputs := [] }

private def invokeOffer (index : Nat) : OfferView :=
  { id := .application { index }
    key := .invoke (invocation index)
    offerClass := .invoke
    age := 0 }

private def splitOffer (index : Nat) : OfferView :=
  { id := .suggestion { index }
    key := .split (invocation index .split) { node := node index, version := 1 }
      index .midpoint
    offerClass := .split
    age := 0 }

private def view (offers : Array OfferView) : Policy.View Nat :=
  { scope := { index := 0 }
    serial := 2
    programVersion := 3
    offers
    facts := { facts := #[8, 3], versions := #[1, 1], contradictory := false }
    remaining :=
      { actions := 20
        matcherVisits := 20
        acceptedFacts := 20
        nodes := 20
        applications := 20
        equalities := 20
        retainedSuggestions := 20
        instances := 20
        queueEntries := 20
        generation := 20 }
    incomplete := false }

private def widthProviderKey : ProviderKey := { family := 10, version := 1 }
private def goalProviderKey : ProviderKey := { family := 20, version := 4 }

/-- A fact-domain companion publishes negative width, so a narrower interval
has a larger score.  The policy does not know what the `Nat` means. -/
private def widthProvider : Provider Nat :=
  { key := widthProviderKey
    features := fun request =>
      match request.offer.key with
      | .invoke invocation =>
          match request.facts.fact? invocation.anchor with
          | some width => #[{ key := 0, value := -(Int.ofNat width) }]
          | none => #[]
      | _ => #[] }

/-- An independent frontend companion publishes split closing potential. -/
private def goalProvider : Provider Nat :=
  { key := goalProviderKey
    features := fun request =>
      match request.offer.key with
      | .split _ target _ _ =>
          #[{ key := 2, value := if target.node == node 1 then 9 else 2 },
            { key := 9, value := 7 }]
      | _ => #[] }

private def featureLimits : PolicyFeature.Limits :=
  { maxProviders := 2
    maxProviderChecks := 8
    maxFeaturesPerProvider := 2
    maxFeaturesPerOffer := 2
    maxTotalFeatures := 8
    maxFeatureKey := 10
    maxFeatureValue := 20 }

private def scoreLimits : FeaturePolicy.Limits :=
  { maxTerms := 4
    maxProviderComponent := 100
    maxFeatureKey := 10
    maxWeight := 20
    maxOffers := 4
    maxFeaturesPerOffer := 4
    maxPairChecks := 16
    maxFeatureValue := 20
    maxScore := 100 }

private def registry? : Option (PolicyFeature.Registry Nat) :=
  (PolicyFeature.Registry.buildWithin featureLimits #[widthProvider, goalProvider]).toOption

private def address (provider : ProviderKey) (key : Nat) : Address := { provider, key }

private def widthPlan? : Option Plan :=
  (Plan.buildWithin scoreLimits
    #[{ address := address widthProviderKey 0, weight := 1 }]).toOption

private def goalPlan? : Option Plan :=
  (Plan.buildWithin scoreLimits
    #[{ address := address goalProviderKey 2, weight := 1 }]).toOption

private def reverseGoalPlan? : Option Plan :=
  (Plan.buildWithin scoreLimits
    #[{ address := address goalProviderKey 2, weight := -1 }]).toOption

private def emptyPlan? : Option Plan :=
  (Plan.buildWithin scoreLimits #[]).toOption

private def planOrError (plan : Option Plan) : Except FeaturePolicy.Error Plan :=
  match plan with
  | none => .error .offerLimit
  | some plan => .ok plan

private def choose (offers : Array OfferView) (plan : Plan) :
    Except FeaturePolicy.Error (Option OfferView) := do
  let registry <- match registry? with
    | none => .error .offerLimit
    | some registry => .ok registry
  let featured <- (decorate featureLimits registry (view offers)).mapError fun _ => .offerLimit
  FeaturePolicy.choose? scoreLimits (AdaptivePolicy.State.initial {}) plan featured

/- Width changes a tie: stable base order is wide then narrow, but the second
offer has the larger negative-width score. -/
#guard
  match do
    let plan <- planOrError widthPlan?
    let selected <- choose #[invokeOffer 0, invokeOffer 1] plan
    pure selected with
  | .ok (some selected) => selected.id == (invokeOffer 1).id
  | _ => false

/- The unrelated goal provider changes a tied split choice. -/
#guard
  match do
    let plan <- planOrError goalPlan?
    let selected <- choose #[splitOffer 0, splitOffer 1] plan
    pure selected with
  | .ok (some selected) => selected.id == (splitOffer 1).id
  | _ => false

/- Signed weights are accepted.  Reversing the goal weight reverses the
otherwise-tied choice even when the newly preferred offer comes second. -/
#guard
  match do
    let plan <- planOrError reverseGoalPlan?
    let selected <- choose #[splitOffer 1, splitOffer 0] plan
    pure selected with
  | .ok (some selected) => selected.id == (splitOffer 0).id
  | _ => false

/- Missing configured data and emitted unknown keys are inert; stable base
order remains the final tie-break. -/
private def missingPlan? : Option Plan :=
  (Plan.buildWithin scoreLimits
    #[{ address := address goalProviderKey 8, weight := 7 }]).toOption

#guard
  match do
    let plan <- planOrError missingPlan?
    let selected <- choose #[invokeOffer 0, invokeOffer 1] plan
    pure selected with
  | .ok (some selected) => selected.id == (invokeOffer 0).id
  | _ => false

#guard
  match do
    let plan <- planOrError widthPlan?
    let selected <- choose #[splitOffer 0, splitOffer 1] plan
    pure selected with
  | .ok (some selected) => selected.id == (splitOffer 0).id
  | _ => false

/- Negative feature values are used as signed values, not absolute values. -/
#guard
  match do
    let plan <- planOrError widthPlan?
    let selected <- choose #[invokeOffer 1, invokeOffer 0] plan
    pure selected with
  | .ok (some selected) => selected.id == (invokeOffer 1).id
  | _ => false

/- Saturation is applied after every configured term in caller order.  Here
`20 * 20` reaches `10`, then `-7` lowers it to `3`; the competing score `4`
wins.  Saturating only the final mathematical sum would choose the first. -/
private def overflowProviderKey : ProviderKey := { family := 30, version := 1 }

private def overflowView : PolicyFeature.View Nat :=
  { base := view #[invokeOffer 0, invokeOffer 1]
    offers :=
      #[{ base := invokeOffer 0
          features :=
            #[{ provider := overflowProviderKey, key := 0, value := 20 },
              { provider := overflowProviderKey, key := 1, value := -7 }] },
        { base := invokeOffer 1
          features := #[{ provider := overflowProviderKey, key := 0, value := 0 },
            { provider := overflowProviderKey, key := 1, value := 4 }] }]
    metrics := { providerChecks := 0, emittedFeatures := 4 } }

private def overflowLimits : FeaturePolicy.Limits :=
  { scoreLimits with maxScore := 10, maxWeight := 20 }

private def overflowPlan? : Option Plan :=
  (Plan.buildWithin overflowLimits
    #[{ address := address overflowProviderKey 0, weight := 20 },
      { address := address overflowProviderKey 1, weight := 1 }]).toOption

#guard
  match do
    let plan <- planOrError overflowPlan?
    let selected <- FeaturePolicy.choose? overflowLimits
      (AdaptivePolicy.State.initial { optimism := 0 }) plan overflowView
    pure selected with
  | .ok (some selected) => selected.id == (invokeOffer 1).id
  | _ => false

private def scoredView (first second : OfferView) (firstScore secondScore : Int) :
    PolicyFeature.View Nat :=
  { base := view #[first, second]
    offers :=
      #[{ base := first
          features := #[{ provider := goalProviderKey, key := 2, value := firstScore }] },
        { base := second
          features := #[{ provider := goalProviderKey, key := 2, value := secondScore }] }]
    metrics := { providerChecks := 0, emittedFeatures := 2 } }

/- With no configured feature terms and learned scores inside the explicit
bound, the result equals the wrapped adaptive policy's result exactly. -/
#guard
  match do
    let plan <- planOrError emptyPlan?
    let state := AdaptivePolicy.State.initial {}
    let featured := scoredView (invokeOffer 0) { invokeOffer 1 with age := 1 } 20 (-20)
    let selected <- FeaturePolicy.choose? scoreLimits state plan featured
    pure (selected, AdaptivePolicy.choose? state featured.base.offers) with
  | .ok (selected, adaptive) => selected == adaptive
  | _ => false

/- Feature score cannot cross the adaptive fairness tier. -/
#guard
  match do
    let plan <- planOrError goalPlan?
    FeaturePolicy.choose? scoreLimits (AdaptivePolicy.State.initial {}) plan
      (scoredView { invokeOffer 0 with age := 20 } (invokeOffer 1) (-20) 20) with
  | .ok (some selected) => selected.id == (invokeOffer 0).id
  | _ => false

/- Nor can it cross the staged semantic tier. -/
#guard
  match do
    let plan <- planOrError goalPlan?
    FeaturePolicy.choose? scoreLimits (AdaptivePolicy.State.initial {}) plan
      (scoredView (invokeOffer 0) (splitOffer 1) (-20) 20) with
  | .ok (some selected) => selected.id == (invokeOffer 0).id
  | _ => false

/- Duplicate and oversized plans are rejected before a plan exists. -/
private def widthTerm : Term := { address := address widthProviderKey 0, weight := 1 }

#guard
  match Plan.buildWithin scoreLimits #[widthTerm, widthTerm] with
  | .error (.duplicateAddress found) => found == widthTerm.address
  | _ => false

#guard
  match Plan.buildWithin { scoreLimits with maxTerms := 0 } #[widthTerm] with
  | .error .termLimit => true
  | _ => false

#guard
  match Plan.buildWithin { scoreLimits with maxWeight := 0 } #[widthTerm] with
  | .error (.weightLimit found weight) => found == widthTerm.address && weight == 1
  | _ => false

#guard
  match Plan.buildWithin { scoreLimits with maxProviderComponent := 5 } #[widthTerm] with
  | .error (.providerComponentLimit found) => found == widthTerm.address
  | _ => false

#guard
  match Plan.buildWithin { scoreLimits with maxFeatureKey := 0 }
      #[{ address := address widthProviderKey 1, weight := 0 }] with
  | .error (.featureKeyLimit found) => found == address widthProviderKey 1
  | _ => false

/- Runtime work bounds reject transactionally, and a configured feature value
outside the scoring limit is rejected before multiplication. -/
private def oneFeatured (features : Array Feature) : PolicyFeature.View Nat :=
  { base := view #[invokeOffer 0]
    offers := #[{ base := invokeOffer 0, features }]
    metrics := { providerChecks := 0, emittedFeatures := features.size } }

/- Oversized adaptive scores fail closed rather than being clamped and
silently flattened. -/
#guard
  match do
    let plan <- planOrError emptyPlan?
    FeaturePolicy.choose? { scoreLimits with maxScore := 100 }
      (AdaptivePolicy.State.initial { optimism := 101 }) plan (oneFeatured #[]) with
  | .error (.learnedScoreLimit offer score) =>
      offer == (invokeOffer 0).id && score == 101
  | _ => false

/- A plan built under generous limits is revalidated against the limits used
for selection. -/
#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? { scoreLimits with maxTerms := 0 }
      (AdaptivePolicy.State.initial {}) plan (oneFeatured #[]) with
  | .error (.plan .termLimit) => true
  | _ => false

/- Even a publicly constructed featured view cannot substitute or reorder the
engine-owned offers retained in its base view. -/
private def misaligned : PolicyFeature.View Nat :=
  { base := view #[invokeOffer 0, invokeOffer 1]
    offers :=
      #[{ base := invokeOffer 1, features := #[] },
        { base := invokeOffer 0, features := #[] }]
    metrics := { providerChecks := 0, emittedFeatures := 0 } }

#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? scoreLimits (AdaptivePolicy.State.initial {}) plan misaligned with
  | .error .offerAlignment => true
  | _ => false

/- Alignment compares every field of each retained offer, not only its engine
identity or array position. -/
private def changedOffer : PolicyFeature.View Nat :=
  { base := view #[invokeOffer 0]
    offers := #[{ base := { invokeOffer 0 with age := 1 }, features := #[] }]
    metrics := { providerChecks := 0, emittedFeatures := 0 } }

#guard
  match do
    let plan <- planOrError emptyPlan?
    FeaturePolicy.choose? scoreLimits (AdaptivePolicy.State.initial {}) plan changedOffer with
  | .error .offerAlignment => true
  | _ => false

/- Offer-count rejection precedes alignment traversal, even for a malformed
oversized view. -/
#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? { scoreLimits with maxOffers := 0 }
      (AdaptivePolicy.State.initial {}) plan misaligned with
  | .error .offerLimit => true
  | _ => false

#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? { scoreLimits with maxOffers := 0 }
      (AdaptivePolicy.State.initial {}) plan (oneFeatured #[]) with
  | .error .offerLimit => true
  | _ => false

#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? { scoreLimits with maxFeaturesPerOffer := 0 }
      (AdaptivePolicy.State.initial {}) plan
      (oneFeatured #[{ provider := widthProviderKey, key := 0, value := 1 }]) with
  | .error (.offerFeatureLimit offer) => offer == (invokeOffer 0).id
  | _ => false

#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? { scoreLimits with maxPairChecks := 0 }
      (AdaptivePolicy.State.initial {}) plan
      (oneFeatured #[{ provider := widthProviderKey, key := 0, value := 1 }]) with
  | .error .pairCheckLimit => true
  | _ => false

#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? scoreLimits (AdaptivePolicy.State.initial {}) plan
      (oneFeatured
        #[{ provider := { family := 101, version := 1 }, key := 0, value := 0 }]) with
  | .error (.providerComponentLimit offer found) =>
      offer == (invokeOffer 0).id && found.provider.family == 101
  | _ => false

#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? scoreLimits (AdaptivePolicy.State.initial {}) plan
      (oneFeatured #[{ provider := widthProviderKey, key := 11, value := 0 }]) with
  | .error (.featureKeyLimit offer found) =>
      offer == (invokeOffer 0).id && found == address widthProviderKey 11
  | _ => false

#guard
  match do
    let plan <- planOrError widthPlan?
    FeaturePolicy.choose? { scoreLimits with maxFeatureValue := 2 }
      (AdaptivePolicy.State.initial {}) plan
      (oneFeatured #[{ provider := widthProviderKey, key := 0, value := -3 }]) with
  | .error (.featureValueLimit offer address value) =>
      offer == (invokeOffer 0).id && address == widthTerm.address && value == -3
  | _ => false

end Hex.Interval.FeaturePolicyConformance
