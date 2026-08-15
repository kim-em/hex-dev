/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Arithmetic

public section

/-!
# Public exact interval operations

This module begins the supported arithmetic surface with exact intersection,
hull, negation, addition, subtraction, minimum, maximum, and absolute value.
The operations retain a resource-aware result: public
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

/-- Exact raw interval image under binary minimum. Empty is absorbing. The
lower cut is the hull-selected lower cut, while the upper cut is the
intersection-selected upper cut; their tied strictness records whether the
corresponding extremum is attained by either or both inputs respectively. -/
@[expose] def minUnchecked : Raw → Raw → Raw
  | .empty, _ | _, .empty => .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      .bounds
        (hullLowerUnchecked leftLower rightLower)
        (intersectUpperUnchecked leftUpper rightUpper)

/-- Exact raw interval image under binary maximum. Empty is absorbing. The
lower cut is the intersection-selected lower cut, while the upper cut is the
hull-selected upper cut; their tied strictness records whether the
corresponding extremum is attained by both or either input respectively. -/
@[expose] def maxUnchecked : Raw → Raw → Raw
  | .empty, _ | _, .empty => .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      .bounds
        (intersectLowerUnchecked leftLower rightLower)
        (hullUpperUnchecked leftUpper rightUpper)

/-- Exact lower cut of a Minkowski sum. Either unbounded lower input makes the
sum unbounded below; finite endpoint strictness is disjunction because the sum
attains its lower endpoint exactly when both inputs attain theirs.

This helper may align dyadic mantissas. Call it only after preflighting the
finite endpoint pair with `CompareCost`. -/
@[expose] def addLowerUnchecked : Lower → Lower → Lower
  | .unbounded, _ | _, .unbounded => .unbounded
  | .finite left leftStrict, .finite right rightStrict =>
      .finite (left + right) (leftStrict || rightStrict)

/-- Exact upper cut of a Minkowski sum. Either unbounded upper input makes the
sum unbounded above; finite endpoint strictness is disjunction because the sum
attains its upper endpoint exactly when both inputs attain theirs.

This helper may align dyadic mantissas. Call it only after preflighting the
finite endpoint pair with `CompareCost`. -/
@[expose] def addUpperUnchecked : Upper → Upper → Upper
  | .unbounded, _ | _, .unbounded => .unbounded
  | .finite left leftStrict, .finite right rightStrict =>
      .finite (left + right) (leftStrict || rightStrict)

/-- Exact raw Minkowski-sum cuts after both finite endpoint additions have
been preflighted. Empty is absorbing. The candidate remains unnormalized so
the public wrapper checks its retained endpoint sizes and final comparison. -/
@[expose] def addUnchecked : Raw → Raw → Raw
  | .empty, _ | _, .empty => .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      .bounds
        (addLowerUnchecked leftLower rightLower)
        (addUpperUnchecked leftUpper rightUpper)

/-- Exact lower cut of a Minkowski difference. An unbounded left lower or
right upper cut makes the result unbounded below. Finite strictness is
disjunction because the endpoint is attained exactly when both contributors
attain theirs.

This helper may align dyadic mantissas. Call it only after preflighting the
finite endpoint pair with `CompareCost`. -/
@[expose] def subLowerUnchecked : Lower → Upper → Lower
  | .unbounded, _ | _, .unbounded => .unbounded
  | .finite left leftStrict, .finite right rightStrict =>
      .finite (left - right) (leftStrict || rightStrict)

/-- Exact upper cut of a Minkowski difference. An unbounded left upper or
right lower cut makes the result unbounded above. Finite strictness is
disjunction because the endpoint is attained exactly when both contributors
attain theirs.

This helper may align dyadic mantissas. Call it only after preflighting the
finite endpoint pair with `CompareCost`. -/
@[expose] def subUpperUnchecked : Upper → Lower → Upper
  | .unbounded, _ | _, .unbounded => .unbounded
  | .finite left leftStrict, .finite right rightStrict =>
      .finite (left - right) (leftStrict || rightStrict)

/-- Exact raw Minkowski-difference cuts after the crossed finite endpoint
subtractions have been preflighted. Empty is absorbing. The candidate remains
unnormalized so the public wrapper checks retained endpoint sizes and the final
comparison. -/
@[expose] def subUnchecked : Raw → Raw → Raw
  | .empty, _ | _, .empty => .empty
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      .bounds
        (subLowerUnchecked leftLower rightUpper)
        (subUpperUnchecked leftUpper rightLower)

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

/-- Exact raw image under absolute value. The result retains a zero endpoint
exactly when the source retains zero. If the source crosses zero, its upper
cut is selected from the larger endpoint magnitude; tied magnitudes are strict
only when both source endpoints are strict.

The comparison between opposite endpoint magnitudes is unchecked here. The
public wrapper preflights it before calling this decoder-level helper. -/
@[expose] def absUnchecked : Raw → Raw
  | .empty => .empty
  | .bounds .unbounded .unbounded =>
      .bounds (.finite 0 false) .unbounded
  | .bounds .unbounded (.finite upper upperStrict) =>
      if upper ≤ 0 then
        .bounds (.finite (-upper) upperStrict) .unbounded
      else
        .bounds (.finite 0 false) .unbounded
  | .bounds (.finite lower lowerStrict) .unbounded =>
      if 0 ≤ lower then
        .bounds (.finite lower lowerStrict) .unbounded
      else
        .bounds (.finite 0 false) .unbounded
  | .bounds (.finite lower lowerStrict) (.finite upper upperStrict) =>
      if 0 ≤ lower then
        .bounds (.finite lower lowerStrict) (.finite upper upperStrict)
      else if upper ≤ 0 then
        .bounds (.finite (-upper) upperStrict) (.finite (-lower) lowerStrict)
      else
        let leftMagnitude := -lower
        let resultUpper :=
          if leftMagnitude < upper then
            Upper.finite upper upperStrict
          else if leftMagnitude = upper then
            Upper.finite upper (lowerStrict && upperStrict)
          else
            Upper.finite leftMagnitude lowerStrict
        .bounds (.finite 0 false) resultUpper

/-- Direct raw subtraction agrees with addition after raw negation. The
checked public operation uses the direct form so it can preflight only the two
crossed endpoint pairs, without normalizing an intermediate negated interval. -/
theorem sub_eq_add_neg (left right : Raw) :
    subUnchecked left right = addUnchecked left (negUnchecked right) := by
  cases left with
  | empty => cases right <;> rfl
  | bounds leftLower leftUpper =>
      cases right with
      | empty => rfl
      | bounds rightLower rightUpper =>
          cases leftLower <;> cases leftUpper <;>
            cases rightLower <;> cases rightUpper <;> rfl

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

private def lowerUpperCost? (limit : EndpointLimit) : Lower → Upper → Option CompareCost
  | .finite left _, .finite right _ => compareCost? limit left right
  | _, _ => none

private def upperLowerCost? (limit : EndpointLimit) : Upper → Lower → Option CompareCost
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

/-- The first same-side finite-cut comparison refused before selecting the
cuts of a minimum or maximum image. Both comparisons finish before either
unchecked selector runs. -/
private def minMaxCost? (limit : EndpointLimit) : Raw → Raw → Option CompareCost
  | .empty, _ | _, .empty => none
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      match lowerCost? limit leftLower rightLower with
      | some cost => some cost
      | none => upperCost? limit leftUpper rightUpper

/-- The first finite endpoint addition refused by the Minkowski-sum preflight.
`CompareCost.allowed` bounds both retained inputs and their exponent gap before
`Dyadic.add` shifts a mantissa. A successful preflight bounds the temporary
sum numerator by the larger input numerator plus the permitted shift and one
carry bit. The eventual retained result is checked separately by
`ofRawWithin`. -/
private def addCost? (limit : EndpointLimit) : Raw → Raw → Option CompareCost
  | .empty, _ | _, .empty => none
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      match lowerCost? limit leftLower rightLower with
      | some cost => some cost
      | none => upperCost? limit leftUpper rightUpper

/-- The first crossed finite endpoint subtraction refused by the direct
Minkowski-difference preflight. `CompareCost.allowed` bounds both inputs and
their exponent gap before `Dyadic.sub` negates and shifts a mantissa. The raw
result is retained only after the separate `ofRawWithin` check. -/
private def subCost? (limit : EndpointLimit) : Raw → Raw → Option CompareCost
  | .empty, _ | _, .empty => none
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper =>
      match lowerUpperCost? limit leftLower rightUpper with
      | some cost => some cost
      | none => upperLowerCost? limit leftUpper rightLower

/-- Refused opposite-magnitude comparison for an interval that crosses zero.
Negation preserves endpoint size and exponent, so the cost is computed from
the retained lower and upper values before allocating the negated lower used
by the selector. Sign-separated and unbounded cases need no endpoint selection
comparison. -/
private def absCost? (limit : EndpointLimit) : Raw → Option CompareCost
  | .bounds (.finite lower _) (.finite upper _) =>
      if 0 ≤ lower || upper ≤ 0 then none
      else compareCost? limit lower upper
  | _ => none

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

/-- Exact interval image under binary minimum. Empty is absorbing. Both
same-side finite comparisons are preflighted before cut selection, and the
selected candidate crosses `ofRawWithin` for its independent final check. -/
def minWithin (limit : EndpointLimit)
    (left right : Hex.Interval) : BuildResult :=
  match minMaxCost? limit left.view right.view with
  | some cost => .resourceLimit cost
  | none => ofRawWithin limit (Raw.minUnchecked left.view right.view)

/-- A successful minimum exposes exactly the normalized selected cuts. -/
theorem view_minWithin_ready {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (h : minWithin limit left right = .ready result) :
    result.view = (Raw.minUnchecked left.view right.view).normalizeUnchecked := by
  unfold minWithin at h
  split at h
  · contradiction
  · exact view_ofRawWithin_ready h

/-- Exact interval image under binary maximum. Empty is absorbing. Both
same-side finite comparisons are preflighted before cut selection, and the
selected candidate crosses `ofRawWithin` for its independent final check. -/
def maxWithin (limit : EndpointLimit)
    (left right : Hex.Interval) : BuildResult :=
  match minMaxCost? limit left.view right.view with
  | some cost => .resourceLimit cost
  | none => ofRawWithin limit (Raw.maxUnchecked left.view right.view)

/-- A successful maximum exposes exactly the normalized selected cuts. -/
theorem view_maxWithin_ready {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (h : maxWithin limit left right = .ready result) :
    result.view = (Raw.maxUnchecked left.view right.view).normalizeUnchecked := by
  unfold maxWithin at h
  split at h
  · contradiction
  · exact view_ofRawWithin_ready h

/-- Exact interval addition with allocation-safe dyadic endpoint sums.
Empty is absorbing. Every finite endpoint pair is preflighted before addition;
the raw result then crosses the checked canonical boundary, so refusal remains
distinct from an empty sum. -/
def addWithin (limit : EndpointLimit)
    (left right : Hex.Interval) : BuildResult :=
  match addCost? limit left.view right.view with
  | some cost => .resourceLimit cost
  | none => ofRawWithin limit (Raw.addUnchecked left.view right.view)

/-- A successful addition exposes exactly the normalized Minkowski-sum cuts. -/
theorem view_addWithin_ready {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (h : addWithin limit left right = .ready result) :
    result.view = (Raw.addUnchecked left.view right.view).normalizeUnchecked := by
  unfold addWithin at h
  split at h
  · contradiction
  · exact view_ofRawWithin_ready h

/-- Exact interval subtraction with allocation-safe crossed endpoint
differences. The direct implementation avoids an intermediate checked
negation, whose unrelated endpoint comparison could refuse before either
subtraction. Empty is absorbing and resource refusal remains distinct. -/
def subWithin (limit : EndpointLimit)
    (left right : Hex.Interval) : BuildResult :=
  match subCost? limit left.view right.view with
  | some cost => .resourceLimit cost
  | none => ofRawWithin limit (Raw.subUnchecked left.view right.view)

/-- A successful subtraction exposes exactly the normalized
Minkowski-difference cuts. -/
theorem view_subWithin_ready {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (h : subWithin limit left right = .ready result) :
    result.view = (Raw.subUnchecked left.view right.view).normalizeUnchecked := by
  unfold subWithin at h
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

/-- Exact interval absolute value with preflighted opposite-magnitude
selection. Empty is preserved. Resource refusal remains distinct from an
empty image. -/
def absWithin (limit : EndpointLimit) (input : Hex.Interval) : BuildResult :=
  match absCost? limit input.view with
  | some cost => .resourceLimit cost
  | none => ofRawWithin limit (Raw.absUnchecked input.view)

/-- A successful absolute value exposes exactly the normalized selected cuts. -/
theorem view_absWithin_ready {limit : EndpointLimit} {input result : Hex.Interval}
    (h : absWithin limit input = .ready result) :
    result.view = (Raw.absUnchecked input.view).normalizeUnchecked := by
  unfold absWithin at h
  split at h
  · contradiction
  · exact view_ofRawWithin_ready h

end Hex.Interval
