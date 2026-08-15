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
hull, negation, addition, subtraction, minimum, maximum, absolute value,
natural power, and splitting. The operations retain a resource-aware result:
public interval values do not remember the construction budget under which
their endpoints were admitted, so a later comparison must preflight its own
alignment work. Resource-checked multiplication is kept in
`HexInterval.Multiplication` because it additionally depends on
arithmetic-growth diagnostics and corner candidate selection.
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

/-- Raise both finite cuts to a natural power, preserving strictness and
unbounded sides. This decoder-level helper is used only where the power map is
known to be strictly monotone: directly for odd exponents, and after
`absUnchecked` for positive even exponents. -/
@[expose] def powCutsUnchecked : Raw → Nat → Raw
  | .empty, _ => .empty
  | .bounds lower upper, exponent =>
      let resultLower :=
        match lower with
        | .unbounded => Lower.unbounded
        | .finite value strict => Lower.finite (value ^ exponent) strict
      let resultUpper :=
        match upper with
        | .unbounded => Upper.unbounded
        | .finite value strict => Upper.finite (value ^ exponent) strict
      .bounds resultLower resultUpper

/-- Exact raw hull of a natural-power image. Empty remains empty even at
exponent zero. Every nonempty zero power is `{1}`. Positive odd powers map the
source cuts directly; positive even powers first select the exact absolute
value cuts and then map their nonnegative endpoints.

Endpoint powers and the magnitude comparison inside `absUnchecked` are
unchecked here. The public wrapper authenticates all of them before calling
this decoder-level helper. -/
@[expose] def powUnchecked : Raw → Nat → Raw
  | .empty, _ => .empty
  | .bounds _ _, 0 =>
      .bounds (.finite 1 false) (.finite 1 false)
  | raw@(.bounds _ _), exponent =>
      if exponent % 2 = 1 then
        powCutsUnchecked raw exponent
      else
        powCutsUnchecked raw.absUnchecked exponent

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

/-! ## Interval splitting -/

/-- Raw split at a dyadic point. The left child owns the point and the right
child excludes it. The pair remains unnormalized so the public wrapper can
preflight both final child comparisons before constructing either result. -/
@[expose] def splitUnchecked (input : Raw) (point : Dyadic) : Raw × Raw :=
  match input with
  | .empty => (.empty, .empty)
  | .bounds lower upper =>
      ( .bounds lower
          (intersectUpperUnchecked upper (.finite point false)),
        .bounds
          (intersectLowerUnchecked lower (.finite point true)) upper )

/-! ## Precision-indexed reciprocal enclosure -/

/-- A lower reciprocal cut, rounded toward negative infinity.  A missing
upper source cut approaches zero from one side; an open zero source endpoint
approaches infinity and is never passed to `Dyadic.invAtPrec`.  Finite rounded
cuts are closed because this public operation promises an outward enclosure,
not exact endpoint attainment. This is a decoder-level cut helper; untrusted
callers use `invWithin`. -/
@[expose] def invLowerUnchecked (precision : Precision) : Upper → Lower
  | .unbounded => .finite 0 true
  | .finite value _ =>
      if value = 0 then .unbounded
      else .finite (value.invAtPrec precision) false

/-- An upper reciprocal cut, rounded toward positive infinity by negating the
downward-rounded reciprocal of the negated source lower endpoint. This is a
decoder-level cut helper; untrusted callers use `invWithin`. -/
@[expose] def invUpperUnchecked (precision : Precision) : Lower → Upper
  | .unbounded => .finite 0 true
  | .finite value _ =>
      if value = 0 then .unbounded
      else .finite (-(-value).invAtPrec precision) false

/-- Whether a lower cut places the entire nonempty interval strictly above
zero.  The equality case is positive exactly for an open lower cut. This is a
decoder-level classifier used to interpret checked reciprocal output. -/
@[expose] def strictlyPositive : Lower → Bool
  | .unbounded => false
  | .finite value strict =>
      if 0 < value then true else if value = 0 then strict else false

/-- Whether an upper cut places the entire nonempty interval strictly below
zero.  The equality case is negative exactly for an open upper cut. This is a
decoder-level classifier used to interpret checked reciprocal output. -/
@[expose] def strictlyNegative : Upper → Bool
  | .unbounded => false
  | .finite value strict =>
      if value < 0 then true else if value = 0 then strict else false

/-- Whether a cut is the closed zero endpoint used by the connected-hull
policy for Lean's total reciprocal (`0⁻¹ = 0`). This decoder-level
classifier does not perform resource admission. -/
@[expose] def closedZeroLower : Lower → Bool
  | .finite value strict => value = 0 && !strict
  | .unbounded => false

/-- Upper-cut counterpart of `closedZeroLower`, used only to decode the
connected-hull reciprocal shape after checked admission. -/
@[expose] def closedZeroUpper : Upper → Bool
  | .finite value strict => value = 0 && !strict
  | .unbounded => false

/-- Raw connected outward enclosure of Lean's total reciprocal. On an
interval separated from zero it reverses the cuts and rounds both finite
endpoints outward.  A closed zero endpoint contributes the value zero and an
unbounded one-sided branch; a sign-crossing interval has the whole line as its
connected hull. This cut computation does not claim a tightness converse for
the generally disconnected image across zero. It is a decoder-level
combinator; untrusted callers use `invWithin`. -/
@[expose] def invUnchecked (precision : Precision) : Raw → Raw
  | .empty => .empty
  | .bounds lower upper =>
      if Raw.strictlyPositive lower || Raw.strictlyNegative upper then
        .bounds (invLowerUnchecked precision upper) (invUpperUnchecked precision lower)
      else if Raw.closedZeroLower lower then
        if Raw.closedZeroUpper upper then
          .bounds (.finite 0 false) (.finite 0 false)
        else
          .bounds (.finite 0 false) .unbounded
      else if Raw.closedZeroUpper upper then
        .bounds .unbounded (.finite 0 false)
      else
        .bounds .unbounded .unbounded

/-! ## Precision-indexed division enclosure -/

/-- Recover the value of a closed finite singleton. This decoder-level
classifier performs no resource admission; untrusted callers use `divWithin`. -/
@[expose] def singletonValue? : Raw → Option Dyadic
  | .bounds (.finite lower false) (.finite upper false) =>
      if lower = upper then some lower else none
  | _ => none

/-- Raw first-slice enclosure of Lean's total division. Empty is absorbing. A
singleton-zero numerator or denominator maps exactly to `{0}`. Two nonzero
finite singletons use direct outward Core division, and every other nonempty
shape returns the whole interval. This decoder-level combinator performs no
resource admission; untrusted callers use `divWithin`. -/
@[expose] def divUnchecked (precision : Precision)
    (numerator denominator : Raw) : Raw :=
  match numerator, denominator with
  | .empty, _ | _, .empty => .empty
  | numerator, denominator =>
      match numerator.singletonValue?, denominator.singletonValue? with
      | some .zero, _ | _, some .zero =>
          .bounds (.finite 0 false) (.finite 0 false)
      | some numerator, some denominator =>
          .bounds
            (.finite (numerator.divAtPrec denominator precision) false)
            (.finite (-(-numerator).divAtPrec denominator precision) false)
      | _, _ => .bounds .unbounded .unbounded

end Raw

/-- Transactional result of a checked split. A successful value contains both
sealed canonical children; refusal exposes no partial pair. -/
inductive SplitResult where
  | ready (left right : Hex.Interval)
  | resourceLimit (cost : CompareCost)

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

/-- First refused Core-power prerequisite for one selected finite cut. -/
private def powValueCost? (endpointLimit : EndpointLimit)
    (workLimits : Arithmetic.PowLimits) (value : Dyadic) (exponent : Nat) :
    Option Arithmetic.Cost :=
  match Arithmetic.preflightPow endpointLimit workLimits value exponent with
  | .ok _ => none
  | .error cost => some cost

/-- First refused Core-power prerequisite for the finite cuts selected by a
monotone power map. Both cuts are checked before either is evaluated. -/
private def powCutsCost? (endpointLimit : EndpointLimit)
    (workLimits : Arithmetic.PowLimits) (raw : Raw) (exponent : Nat) :
    Option Arithmetic.Cost :=
  match raw with
  | .empty => none
  | .bounds lower upper =>
      let lowerCost :=
        match lower with
        | .unbounded => none
        | .finite value _ =>
            powValueCost? endpointLimit workLimits value exponent
      match lowerCost with
      | some cost => some cost
      | none =>
          match upper with
          | .unbounded => none
          | .finite value _ =>
              powValueCost? endpointLimit workLimits value exponent

/-- First refusal before constructing a natural-power image. The mixed-sign
absolute-value selector comparison is authenticated before it executes, then
all selected finite endpoint powers are preflighted before any Core power.
Exponent zero and empty inputs perform no endpoint power. -/
private def powCost? (endpointLimit : EndpointLimit)
    (workLimits : Arithmetic.PowLimits) (raw : Raw) (exponent : Nat) :
    Option Arithmetic.Cost :=
  match raw, exponent with
  | .empty, _ | _, 0 => none
  | raw@(.bounds _ _), exponent =>
      if exponent % 2 = 1 then
        powCutsCost? endpointLimit workLimits raw exponent
      else
        match absCost? endpointLimit raw with
        | some cost => some (.comparison cost)
        | none =>
            powCutsCost? endpointLimit workLimits raw.absUnchecked exponent

private def refused? (limit : EndpointLimit) (cost : CompareCost) : Option CompareCost :=
  if cost.allowed limit then none else some cost

/-- Authenticated raw split candidate. The equality is proof-only; the runtime
payload is the one selected pair that the checked wrapper will seal. -/
private structure PreparedSplit (input : Raw) (point : Dyadic) where
  children : Raw × Raw
  selected : children = input.splitUnchecked point

/-- Prepare both raw children only after point and selector preflight, then
preflight both final normalization comparisons before returning the selected
pair. -/
private def admitSplit (limit : EndpointLimit) (input : Raw) (point : Dyadic) :
    Except CompareCost (PreparedSplit input point) := do
  match hinput : input with
  | .empty => pure ⟨(.empty, .empty), by simp [hinput, Raw.splitUnchecked]⟩
  | .bounds lower upper =>
      let pointCost :=
        (Raw.bounds .unbounded (.finite point false)).normalizeCost
      if let some cost := refused? limit pointCost then throw cost
      match lower with
      | .finite lower _ =>
          if let some cost := compareCost? limit lower point then throw cost
      | .unbounded => pure ()
      match upper with
      | .finite upper _ =>
          if let some cost := compareCost? limit point upper then throw cost
      | .unbounded => pure ()
      let children := Raw.splitUnchecked (.bounds lower upper) point
      if let some cost := refused? limit children.1.normalizeCost then throw cost
      if let some cost := refused? limit children.2.normalizeCost then throw cost
      pure ⟨children, by simp [hinput, children, Raw.splitUnchecked]⟩

private def admitZeroComparison (limits : Arithmetic.PrecisionLimits)
    (value : Dyadic) : Except Arithmetic.Cost Unit := do
  let _ ← Arithmetic.admitEndpoint limits value
  let cost := CompareCost.ofDyadic value 0
  if !cost.allowed limits.endpoint then
    throw (.comparison cost)

private def admitLowerZero (limits : Arithmetic.PrecisionLimits) : Lower →
    Except Arithmetic.Cost Unit
  | .unbounded => pure ()
  | .finite value _ => admitZeroComparison limits value

private def admitUpperZero (limits : Arithmetic.PrecisionLimits) : Upper →
    Except Arithmetic.Cost Unit
  | .unbounded => pure ()
  | .finite value _ => admitZeroComparison limits value

private def admitInvLower (limits : Arithmetic.PrecisionLimits)
    (precision : Precision) : Upper → Except Arithmetic.Cost Unit
  | .unbounded => pure ()
  | .finite value _ => do
      if value ≠ 0 then
        let _ ← Arithmetic.preflightInv limits value precision

private def admitInvUpper (limits : Arithmetic.PrecisionLimits)
    (precision : Precision) : Lower → Except Arithmetic.Cost Unit
  | .unbounded => pure ()
  | .finite value _ => do
      if value ≠ 0 then
        let _ ← Arithmetic.preflightInv limits (-value) precision

/-- Preflight every retained source comparison before classification, then
both rational-backed endpoint computations before either is executed. -/
private def admitInv (limits : Arithmetic.PrecisionLimits)
    (precision : Precision) : Raw → Except Arithmetic.Cost Unit
  | .empty => pure ()
  | .bounds lower upper => do
      admitLowerZero limits lower
      admitUpperZero limits upper
      if Raw.strictlyPositive lower || Raw.strictlyNegative upper then
        admitInvLower limits precision upper
        admitInvUpper limits precision lower

/-- Preflight both direct Core quotient calls before either executes. Empty,
total-zero cases, and the whole-line nonsingleton fallback perform no quotient
work. No caller-provided plan or intermediate reciprocal is accepted. -/
private def admitDiv (limits : Arithmetic.PrecisionLimits)
    (precision : Precision) (numerator denominator : Raw) :
    Except Arithmetic.Cost Unit := do
  match numerator, denominator with
  | .empty, _ | _, .empty => pure ()
  | numerator, denominator =>
      match numerator.singletonValue?, denominator.singletonValue? with
      | some .zero, _ | _, some .zero => pure ()
      | some numerator, some denominator =>
          let _ ← Arithmetic.preflightDiv limits numerator denominator precision
          let _ ← Arithmetic.preflightDiv limits (-numerator) denominator precision
      | _, _ => pure ()

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

/-- Exact interval natural power with authenticated exponent work, retained
endpoint growth, even-power magnitude selection, and final canonicalization.
Empty is absorbing, including at exponent zero. Refusal is never interpreted
as an empty image. -/
def powWithin (endpointLimit : EndpointLimit)
    (workLimits : Arithmetic.PowLimits) (input : Hex.Interval)
    (exponent : Nat) : Arithmetic.Result :=
  match powCost? endpointLimit workLimits input.view exponent with
  | some cost => .resourceLimit cost
  | none =>
      Arithmetic.Result.ofBuild
        (ofRawWithin endpointLimit (Raw.powUnchecked input.view exponent))

/-- A successful natural power exposes exactly the normalized direct image
cuts selected by `Raw.powUnchecked`. -/
theorem view_powWithin_ready {endpointLimit : EndpointLimit}
    {workLimits : Arithmetic.PowLimits} {input result : Hex.Interval}
    {exponent : Nat}
    (h : powWithin endpointLimit workLimits input exponent = .ready result) :
    result.view = (Raw.powUnchecked input.view exponent).normalizeUnchecked := by
  unfold powWithin at h
  split at h
  · contradiction
  · cases hraw : ofRawWithin endpointLimit
        (Raw.powUnchecked input.view exponent) with
    | ready interval =>
        simp only [Arithmetic.Result.ofBuild, hraw] at h
        cases h
        exact view_ofRawWithin_ready hraw
    | resourceLimit cost =>
        simp [Arithmetic.Result.ofBuild, hraw] at h

/-- Split an interval into `input ∩ (-∞, point]` and
`input ∩ (point, +∞)`. Empty short-circuits without inspecting the point.
For a nonempty input, all point, selector, and final child comparisons are
preflighted before the transactional result can expose either child. -/
def splitWithin (limit : EndpointLimit) (input : Hex.Interval)
    (point : Dyadic) : SplitResult :=
  match admitSplit limit input.view point with
  | .error cost => .resourceLimit cost
  | .ok prepared =>
      match ofRawWithin limit prepared.children.1,
          ofRawWithin limit prepared.children.2 with
      | .ready left, .ready right => .ready left right
      -- `admitSplit` already admitted these exact normalization costs. These
      -- defensive arms keep final sealing honest and still expose no partial
      -- pair if that checked constructor is strengthened in the future.
      | .resourceLimit cost, _ | _, .resourceLimit cost => .resourceLimit cost

/-- A successful split exposes exactly both normalized raw children. -/
theorem view_splitWithin_ready {limit : EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (h : splitWithin limit input point = .ready left right) :
    let children := Raw.splitUnchecked input.view point
    left.view = children.1.normalizeUnchecked ∧
      right.view = children.2.normalizeUnchecked := by
  unfold splitWithin at h
  split at h
  · contradiction
  · next prepared preparedEq =>
      generalize leftEq : ofRawWithin limit prepared.children.1 = leftResult at h
      generalize rightEq : ofRawWithin limit prepared.children.2 = rightResult at h
      cases leftResult <;> cases rightResult <;> simp_all
      rw [← prepared.selected]
      exact ⟨view_ofRawWithin_ready leftEq, view_ofRawWithin_ready rightEq⟩

/-- Precision-indexed connected outward enclosure of Lean's total reciprocal.
The operation internally invokes `Arithmetic.preflightInv` for every nonzero
endpoint it will evaluate before either Core reciprocal call; no caller-provided
plan is accepted. Every input not separated from zero, including empty and
zero-only inputs, performs no precision work. Across zero the result follows
the connected-hull policy of `Raw.invUnchecked`, not a
tightness converse for the generally disconnected image. -/
def invWithin (limits : Arithmetic.PrecisionLimits) (precision : Precision)
    (input : Hex.Interval) : Arithmetic.Result :=
  match admitInv limits precision input.view with
  | .error cost => .resourceLimit cost
  | .ok () =>
      Arithmetic.Result.ofBuild
        (ofRawWithin limits.endpoint (Raw.invUnchecked precision input.view))

/-- Every successful reciprocal exposes exactly the normalized computed
outward cuts.  This characterizes the successful result, without claiming
that a connected hull is the exact image across zero or that rounded finite
cuts are attained. -/
theorem view_invWithin_ready {limits : Arithmetic.PrecisionLimits}
    {precision : Precision} {input result : Hex.Interval}
    (h : invWithin limits precision input = .ready result) :
    result.view = (Raw.invUnchecked precision input.view).normalizeUnchecked := by
  unfold invWithin at h
  split at h
  · contradiction
  · generalize builtEq :
        ofRawWithin limits.endpoint (Raw.invUnchecked precision input.view) = built at h
    cases built with
    | ready interval =>
        simp only [Arithmetic.Result.ofBuild] at h
        cases h
        exact view_ofRawWithin_ready builtEq
    | resourceLimit cost =>
        simp [Arithmetic.Result.ofBuild] at h

/-- Precision-indexed public division using Core's direct rational quotient
for two nonzero finite singletons. Both quotient calls are internally
preflighted before either executes; no caller plan or intermediate reciprocal
is accepted. Empty and total-zero cases are exact, while every other nonempty
shape receives the sound whole-line enclosure. -/
def divWithin (limits : Arithmetic.PrecisionLimits) (precision : Precision)
    (numerator denominator : Hex.Interval) : Arithmetic.Result :=
  match admitDiv limits precision numerator.view denominator.view with
  | .error cost => .resourceLimit cost
  | .ok () =>
      Arithmetic.Result.ofBuild
        (ofRawWithin limits.endpoint
          (Raw.divUnchecked precision numerator.view denominator.view))

/-- Every successful division exposes exactly the normalized computed cuts.
This theorem does not claim that the whole-line fallback is an exact image or
that rounded singleton endpoints are attained. -/
theorem view_divWithin_ready {limits : Arithmetic.PrecisionLimits}
    {precision : Precision} {numerator denominator result : Hex.Interval}
    (h : divWithin limits precision numerator denominator = .ready result) :
    result.view =
      (Raw.divUnchecked precision numerator.view denominator.view).normalizeUnchecked := by
  unfold divWithin at h
  split at h
  · contradiction
  · generalize builtEq :
        ofRawWithin limits.endpoint
          (Raw.divUnchecked precision numerator.view denominator.view) = built at h
    cases built with
    | ready interval =>
        simp only [Arithmetic.Result.ofBuild] at h
        cases h
        exact view_ofRawWithin_ready builtEq
    | resourceLimit cost =>
        simp [Arithmetic.Result.ofBuild] at h

end Hex.Interval
