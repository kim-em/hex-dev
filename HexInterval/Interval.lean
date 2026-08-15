/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Canonical

public section

/-!
# Public exact interval operations

This module begins the supported arithmetic surface with exact intersection,
hull, and negation.  The operations retain a resource-aware result: public
interval values do not remember the construction budget under which their
endpoints were admitted, so a later comparison must preflight its own alignment
work.
-/

namespace Hex.Interval

namespace Raw

/-- Larger of two lower cuts.  This unchecked helper may compare dyadics and
is used only after the public operation has preflighted that comparison. -/
@[expose] def intersectLowerUnchecked : Lower → Lower → Lower
  | .unbounded, cut | cut, .unbounded => cut
  | left@(.finite leftValue leftStrict), right@(.finite rightValue rightStrict) =>
      if leftValue < rightValue then right
      else if leftValue = rightValue then
        .finite leftValue (leftStrict || rightStrict)
      else left

/-- Smaller of two upper cuts.  This unchecked helper may compare dyadics and
is used only after the public operation has preflighted that comparison. -/
@[expose] def intersectUpperUnchecked : Upper → Upper → Upper
  | .unbounded, cut | cut, .unbounded => cut
  | left@(.finite leftValue leftStrict), right@(.finite rightValue rightStrict) =>
      if leftValue < rightValue then left
      else if leftValue = rightValue then
        .finite leftValue (leftStrict || rightStrict)
      else right

/-- Exact raw intersection candidate after the same-side finite comparisons
have been preflighted. The selected lower/upper pair is deliberately left
unnormalized: the supported wrapper sends it through `ofRawWithin`, which
preflights that final crossed comparison before canonicalization. -/
@[expose] def intersectUnchecked : Raw → Raw → Raw
  | .empty, _ | _, .empty => .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      Raw.bounds
        (intersectLowerUnchecked leftLower rightLower)
        (intersectUpperUnchecked leftUpper rightUpper)

/-- Smaller of two lower cuts. An unbounded lower cut wins. At a tied finite
endpoint the hull is strict only when both inputs exclude that endpoint. -/
@[expose] def hullLowerUnchecked : Lower → Lower → Lower
  | .unbounded, _ | _, .unbounded => .unbounded
  | left@(.finite leftValue leftStrict), right@(.finite rightValue rightStrict) =>
      if leftValue < rightValue then left
      else if leftValue = rightValue then
        .finite leftValue (leftStrict && rightStrict)
      else right

/-- Larger of two upper cuts. An unbounded upper cut wins. At a tied finite
endpoint the hull is strict only when both inputs exclude that endpoint. -/
@[expose] def hullUpperUnchecked : Upper → Upper → Upper
  | .unbounded, _ | _, .unbounded => .unbounded
  | left@(.finite leftValue leftStrict), right@(.finite rightValue rightStrict) =>
      if leftValue < rightValue then right
      else if leftValue = rightValue then
        .finite leftValue (leftStrict && rightStrict)
      else left

/-- Exact raw interval-hull candidate after same-side finite comparisons have
been preflighted. Empty is an identity. The selected lower/upper pair remains
unnormalized so the supported wrapper preflights its final comparison. -/
@[expose] def hullUnchecked : Raw → Raw → Raw
  | .empty, raw | raw, .empty => raw
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      Raw.bounds
        (hullLowerUnchecked leftLower rightLower)
        (hullUpperUnchecked leftUpper rightUpper)

/-- Exact raw image under negation.  Negation swaps the cuts and preserves
their strictness. -/
@[expose] def negUnchecked : Raw → Raw
  | .empty => .empty
  | .bounds sourceLower sourceUpper =>
      let resultLower :=
        match sourceUpper with
        | .unbounded => Lower.unbounded
        | .finite value strict => Lower.finite (-value) strict
      let resultUpper :=
        match sourceLower with
        | .unbounded => Upper.unbounded
        | .finite value strict => Upper.finite (-value) strict
      Raw.bounds resultLower resultUpper

end Raw

private def compareCost? (limit : EndpointLimit) (left right : Dyadic) :
    Option CompareCost :=
  let cost := CompareCost.ofDyadic left right
  if cost.allowed limit then none else some cost

private def lowerCost? (limit : EndpointLimit) : Lower → Lower → Option CompareCost
  | .finite left _, .finite right _ => compareCost? limit left right
  | _, _ => none

private def upperCost? (limit : EndpointLimit) : Upper → Upper → Option CompareCost
  | .finite left _, .finite right _ => compareCost? limit left right
  | _, _ => none

/-- The first finite-cut comparison refused by an intersection preflight. -/
private def intersectCost? (limit : EndpointLimit) : Raw → Raw → Option CompareCost
  | .empty, _ | _, .empty => none
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      match lowerCost? limit leftLower rightLower with
      | some cost => some cost
      | none => upperCost? limit leftUpper rightUpper

/-- The first same-side finite-cut comparison refused by a hull preflight. -/
private def hullCost? (limit : EndpointLimit) : Raw → Raw → Option CompareCost
  | .empty, _ | _, .empty => none
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      match lowerCost? limit leftLower rightLower with
      | some cost => some cost
      | none => upperCost? limit leftUpper rightUpper

/-- Exact set intersection with preflighted dyadic comparisons.  Refusal is
distinct from the canonical empty result. -/
def intersectWithin (limit : EndpointLimit)
    (left right : Hex.Interval) : BuildResult :=
  match intersectCost? limit left.view right.view with
  | some cost => .resourceLimit cost
  | none => ofRawWithin limit (Raw.intersectUnchecked left.view right.view)

/-- A successful intersection exposes exactly the canonical raw
intersection. -/
theorem view_intersectWithin_ready {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (h : intersectWithin limit left right = .ready result) :
    result.view = (Raw.intersectUnchecked left.view right.view).normalizeUnchecked := by
  unfold intersectWithin at h
  split at h
  · contradiction
  · exact view_ofRawWithin_ready h

/-- Exact interval hull with preflighted same-side endpoint selection and
checked final canonicalization. Empty is an identity; refusal is distinct from
an empty interval. -/
def hullWithin (limit : EndpointLimit)
    (left right : Hex.Interval) : BuildResult :=
  match hullCost? limit left.view right.view with
  | some cost => .resourceLimit cost
  | none => ofRawWithin limit (Raw.hullUnchecked left.view right.view)

/-- A successful hull exposes exactly the normalized selected-cut candidate. -/
theorem view_hullWithin_ready {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (h : hullWithin limit left right = .ready result) :
    result.view = (Raw.hullUnchecked left.view right.view).normalizeUnchecked := by
  unfold hullWithin at h
  split at h
  · contradiction
  · exact view_ofRawWithin_ready h

/-- Exact interval negation with endpoint-height and final-comparison
preflight. -/
def negWithin (limit : EndpointLimit) (input : Hex.Interval) : BuildResult :=
  ofRawWithin limit (Raw.negUnchecked input.view)

/-- A successful negation exposes exactly the raw negated cuts. -/
theorem view_negWithin_ready {limit : EndpointLimit} {input result : Hex.Interval}
    (h : negWithin limit input = .ready result) :
    result.view = (Raw.negUnchecked input.view).normalizeUnchecked :=
  view_ofRawWithin_ready h

end Hex.Interval
