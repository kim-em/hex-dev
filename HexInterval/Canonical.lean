/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexInterval.Basic

public section

/-!
# Canonical public intervals

`Hex.Interval` is the sealed public value selected by the D2 representation
measurement.  It stores canonical raw cuts together with their consistency
proof.  The proof is erased from compiled code; callers observe the value only
through `view` and construct it through resource-safe smart constructors.
-/

namespace Hex

/-- A canonical exact interval.  Its constructor and representation fields are
private so every public value has exactly one canonical empty shape and
consistent finite cuts. -/
structure Interval where
  private mk ::
  /-- The canonical raw-cut view. -/
  view : Hex.Interval.Raw
  private valid : view.CutConsistent

namespace Interval

/-- Every observable public interval has canonical cuts. -/
theorem view_consistent (interval : Hex.Interval) : interval.view.CutConsistent :=
  interval.valid

/-- Equality of canonical views determines equality of public intervals. -/
@[ext]
theorem ext {left right : Hex.Interval} (h : left.view = right.view) : left = right := by
  cases left
  cases right
  simp_all

/-- Public intervals compare through their canonical raw views. -/
instance : DecidableEq Hex.Interval := fun left right =>
  if h : left.view = right.view then
    isTrue (ext h)
  else
    isFalse fun equal => h (congrArg Hex.Interval.view equal)

/-- Result of constructing a canonical public interval from untrusted cuts. -/
inductive BuildResult where
  | ready (interval : Hex.Interval)
  | resourceLimit (cost : CompareCost)

/-- Canonicalize untrusted raw cuts after preflighting endpoint height and
alignment cost.  Resource refusal is distinct from an empty interval. -/
def ofRawWithin (limit : EndpointLimit) (raw : Raw) : BuildResult :=
  match raw.normalizeWithin limit with
  | .ready normalized valid => .ready (.mk normalized valid)
  | .resourceLimit cost => .resourceLimit cost

/-- A successful untrusted construction exposes exactly the canonicalized
input cuts. -/
theorem view_ofRawWithin_ready {limit : EndpointLimit} {raw : Raw}
    {interval : Hex.Interval} (h : ofRawWithin limit raw = .ready interval) :
    interval.view = raw.normalizeUnchecked := by
  unfold ofRawWithin at h
  split at h
  · next normalized valid equality =>
      unfold Raw.normalizeWithin at equality
      dsimp only at equality
      split at equality
      · cases equality
        cases h
        rfl
      · contradiction
  · contradiction

/-- The canonical empty interval. -/
def empty : Hex.Interval := .mk .empty (by rfl)

/-- The interval containing every value. -/
def whole : Hex.Interval :=
  .mk (.bounds .unbounded .unbounded) (by rfl)

/-- Closed consistent finite cuts recover the endpoint order needed by trusted
representation decoders. This consumes an existing kernel proof; it performs
no executable dyadic comparison. -/
theorem ordered_of_consistent {lower upper : Dyadic}
    (h : (Raw.bounds (.finite lower false) (.finite upper false)).CutConsistent) :
    lower ≤ upper := by
  by_cases less : lower < upper
  · rw [← Dyadic.toRat_le_toRat_iff]
    exact Rat.le_of_lt (Dyadic.toRat_lt_toRat_iff.mpr less)
  · by_cases equal : lower = upper
    · exact equal ▸ Dyadic.le_refl lower
    · simp [Raw.CutConsistent, Raw.consistent, less, equal] at h

/-- Construct a closed interval from independently preflighted ordered bounds.

This is an explicitly unchecked bridge for trusted representation decoders.
It performs no endpoint-height or comparison-cost preflight. Callers must
preflight both costs before producing `ordered`, and must not manufacture that
proof with an unbounded `decide`: deciding dyadic order can itself perform the
prohibited exponent-alignment work. Ordinary untrusted endpoints must enter
through `betweenWithin` or `ofRawWithin`.

The total result lets a proof emitter quote an interval without embedding a
module-boundary reduction proof that a `BuildResult` is ready. The caller,
rather than the emitted term, continues to own the dynamic-range policy. -/
def ofOrderedBoundsUnchecked (lower upper : Dyadic) (ordered : lower ≤ upper) :
    Hex.Interval :=
  .mk (.bounds (.finite lower false) (.finite upper false)) (by
    simp only [Raw.CutConsistent, Raw.consistent]
    by_cases less : lower < upper
    · simp [less]
    · have equal : lower = upper :=
        Dyadic.le_antisymm ordered (Dyadic.not_le.mp less)
      simp [equal])

/-- An unchecked ordered-bounds construction exposes its exact closed cuts. -/
@[simp]
theorem view_ofOrderedBoundsUnchecked
    (lower upper : Dyadic) (ordered : lower ≤ upper) :
    (ofOrderedBoundsUnchecked lower upper ordered).view =
      .bounds (.finite lower false) (.finite upper false) := by
  rfl

/-- Whenever the checked raw constructor admits already-consistent closed
bounds, it returns exactly the unchecked trusted-decoder construction. -/
theorem eq_ordered_ofRawWithin {limit : EndpointLimit} {lower upper : Dyadic}
    {interval : Hex.Interval} (ordered : lower ≤ upper)
    (h : ofRawWithin limit
      (.bounds (.finite lower false) (.finite upper false)) = .ready interval) :
    interval = ofOrderedBoundsUnchecked lower upper ordered := by
  apply ext
  rw [view_ofRawWithin_ready h, view_ofOrderedBoundsUnchecked]
  apply Raw.normalizeUnchecked_eq_self
  exact view_consistent (ofOrderedBoundsUnchecked lower upper ordered)

/-- Construct a singleton after endpoint-cost preflight. -/
def singletonWithin (limit : EndpointLimit) (value : Dyadic) : BuildResult :=
  ofRawWithin limit (.bounds (.finite value false) (.finite value false))

/-- A successful singleton exposes its exact normalized closed cuts. -/
theorem view_singletonWithin_ready {limit : EndpointLimit} {value : Dyadic}
    {result : Hex.Interval} (h : singletonWithin limit value = .ready result) :
    result.view =
      (Raw.bounds (.finite value false) (.finite value false)).normalizeUnchecked := by
  unfold singletonWithin at h
  exact view_ofRawWithin_ready h

/-- Construct a one-sided interval with a finite lower cut. -/
def aboveWithin (limit : EndpointLimit) (value : Dyadic) (strict : Bool) : BuildResult :=
  ofRawWithin limit (.bounds (.finite value strict) .unbounded)

/-- Construct a one-sided interval with a finite upper cut. -/
def belowWithin (limit : EndpointLimit) (value : Dyadic) (strict : Bool) : BuildResult :=
  ofRawWithin limit (.bounds .unbounded (.finite value strict))

/-- Construct a finite interval after endpoint-cost and consistency checks. -/
def betweenWithin (limit : EndpointLimit)
    (lower : Dyadic) (lowerStrict : Bool)
    (upper : Dyadic) (upperStrict : Bool) : BuildResult :=
  ofRawWithin limit
    (.bounds (.finite lower lowerStrict) (.finite upper upperStrict))

@[simp]
theorem view_empty : empty.view = .empty := by rfl

@[simp]
theorem view_whole : whole.view = .bounds .unbounded .unbounded := by rfl

end Interval
end Hex
