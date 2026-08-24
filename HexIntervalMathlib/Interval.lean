/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import HexInterval.Canonical
public import HexInterval.Interval

@[expose] public section

/-!
# Real semantics for public intervals

This companion interprets every canonical public interval as a subset of
`ℝ`. Successful resource-checked intersection is exactly conjunction, hull is
the exact interval/selected-cut closure of its inputs, and negation is exactly
precomposition by real negation.
-/

namespace Hex.Interval

/-- Mathematical real value of a Core dyadic. -/
def toReal (value : Dyadic) : ℝ := (value.toRat : ℝ)

theorem toReal_lt {left right : Dyadic} (h : left < right) :
    toReal left < toReal right := by
  exact (Rat.cast_lt (K := ℝ)).2 (Dyadic.toRat_lt_toRat_iff.2 h)

theorem toReal_lt_iff {left right : Dyadic} :
    toReal left < toReal right ↔ left < right := by
  exact (Rat.cast_lt (K := ℝ)).trans Dyadic.toRat_lt_toRat_iff

theorem toReal_inj {left right : Dyadic} :
    toReal left = toReal right ↔ left = right := by
  constructor
  · intro equal
    apply Dyadic.toRat_inj.mp
    exact Rat.cast_injective equal
  · exact fun equal => congrArg toReal equal

@[simp]
theorem toReal_neg (value : Dyadic) : toReal (-value) = -toReal value := by
  simp [toReal]

/-- Meaning of a lower interval cut. -/
def Lower.Contains : Lower → ℝ → Prop
  | .unbounded, _ => True
  | .finite value false, x => toReal value ≤ x
  | .finite value true, x => toReal value < x

/-- Meaning of an upper interval cut. -/
def Upper.Contains : Upper → ℝ → Prop
  | .finite value false, x => x ≤ toReal value
  | .finite value true, x => x < toReal value
  | .unbounded, _ => True

/-- Mathematical membership in raw interval cuts. -/
def Raw.Contains : Raw → ℝ → Prop
  | .empty, _ => False
  | .bounds lower upper, x => lower.Contains x ∧ upper.Contains x

/-- Exact selected-cut meaning of the interval hull of two raw inputs. Empty
is an identity. For two bounded inputs, the hull uses the union of their lower
predicates and the union of their upper predicates; this deliberately includes
the interval interior between separated inputs and is not set union. -/
def Raw.HullContains : Raw → Raw → ℝ → Prop
  | .empty, right, x => right.Contains x
  | left, .empty, x => left.Contains x
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper, x =>
      (leftLower.Contains x ∨ rightLower.Contains x) ∧
        (leftUpper.Contains x ∨ rightUpper.Contains x)

/-- Mathematical membership in a canonical public interval. -/
def Contains (interval : Hex.Interval) (x : ℝ) : Prop := interval.view.Contains x

/-- Exact real membership in an independently preflighted closed-bounds
construction. This theorem adds semantics but does not weaken the unchecked
constructor's trusted-decoder preflight obligation. -/
@[simp]
theorem contains_ofOrderedBoundsUnchecked
    (lower upper : Dyadic) (ordered : lower ≤ upper) (x : ℝ) :
    (ofOrderedBoundsUnchecked lower upper ordered).Contains x ↔
      toReal lower ≤ x ∧ x ≤ toReal upper := by
  simp [Contains, Raw.Contains, Lower.Contains, Upper.Contains]

theorem contains_normalize (raw : Raw) (x : ℝ) :
    raw.normalizeUnchecked.Contains x ↔ raw.Contains x := by
  cases raw with
  | empty => simp [Raw.Contains, Raw.normalizeUnchecked]
  | bounds lower upper =>
      cases lower with
      | unbounded =>
          simp [Raw.Contains, Raw.normalizeUnchecked, Raw.consistent]
      | finite lower lowerStrict =>
          cases upper with
          | unbounded =>
              simp [Raw.Contains, Raw.normalizeUnchecked, Raw.consistent]
          | finite upper upperStrict =>
              by_cases less : lower < upper
              · simp [Raw.Contains, Raw.normalizeUnchecked, Raw.consistent, less]
              · by_cases equal : lower = upper
                · subst upper
                  cases lowerStrict <;> cases upperStrict
                  · simp [Raw.Contains, Lower.Contains, Upper.Contains,
                      Raw.normalizeUnchecked, Raw.consistent]
                  · have impossible : ¬(toReal lower ≤ x ∧ x < toReal lower) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simp [Raw.Contains, Lower.Contains, Upper.Contains,
                      Raw.normalizeUnchecked, Raw.consistent, less, impossible]
                  · have impossible : ¬(toReal lower < x ∧ x ≤ toReal lower) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simp [Raw.Contains, Lower.Contains, Upper.Contains,
                      Raw.normalizeUnchecked, Raw.consistent, less, impossible]
                  · have impossible : ¬(toReal lower < x ∧ x < toReal lower) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [Raw.Contains, Lower.Contains, Upper.Contains,
                      Raw.normalizeUnchecked, Raw.consistent, less] using impossible
                · have realNotLess : ¬toReal lower < toReal upper := by
                    simpa only [toReal_lt_iff] using less
                  have realNotEqual : toReal lower ≠ toReal upper := by
                    intro same
                    exact equal (toReal_inj.mp same)
                  have realGreater : toReal upper < toReal lower :=
                    lt_of_le_of_ne (le_of_not_gt realNotLess) (Ne.symm realNotEqual)
                  cases lowerStrict <;> cases upperStrict
                  · have impossible : ¬(toReal lower ≤ x ∧ x ≤ toReal upper) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [Raw.Contains, Lower.Contains, Upper.Contains,
                      Raw.normalizeUnchecked, Raw.consistent, less, equal] using impossible
                  · have impossible : ¬(toReal lower ≤ x ∧ x < toReal upper) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [Raw.Contains, Lower.Contains, Upper.Contains,
                      Raw.normalizeUnchecked, Raw.consistent, less, equal] using impossible
                  · have impossible : ¬(toReal lower < x ∧ x ≤ toReal upper) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [Raw.Contains, Lower.Contains, Upper.Contains,
                      Raw.normalizeUnchecked, Raw.consistent, less, equal] using impossible
                  · have impossible : ¬(toReal lower < x ∧ x < toReal upper) := by
                      rintro ⟨lowerBound, upperBound⟩
                      linarith
                    simpa [Raw.Contains, Lower.Contains, Upper.Contains,
                      Raw.normalizeUnchecked, Raw.consistent, less, equal] using impossible

theorem lowerContains_intersect (left right : Lower) (x : ℝ) :
    (Raw.intersectLowerUnchecked left right).Contains x ↔
      left.Contains x ∧ right.Contains x := by
  cases left with
  | unbounded => simp [Raw.intersectLowerUnchecked, Lower.Contains]
  | finite left leftStrict =>
      cases right with
      | unbounded => simp [Raw.intersectLowerUnchecked, Lower.Contains]
      | finite right rightStrict =>
          by_cases less : left < right
          · have realOrder := toReal_lt less
            rw [Raw.intersectLowerUnchecked]
            simp only [less, ↓reduceIte]
            constructor
            · intro rightBound
              refine ⟨?_, rightBound⟩
              cases leftStrict <;> cases rightStrict <;>
                simp [Lower.Contains] at rightBound ⊢ <;> linarith
            · exact fun bounds => bounds.2
          · by_cases equal : left = right
            · subst right
              rw [Raw.intersectLowerUnchecked]
              simp only [less, ↓reduceIte]
              cases leftStrict <;> cases rightStrict
              · simp [Lower.Contains]
              · change toReal left < x ↔ toReal left ≤ x ∧ toReal left < x
                constructor
                · exact fun bound => ⟨le_of_lt bound, bound⟩
                · exact fun bounds => bounds.2
              · change toReal left < x ↔ toReal left < x ∧ toReal left ≤ x
                constructor
                · exact fun bound => ⟨bound, le_of_lt bound⟩
                · exact fun bounds => bounds.1
              · simp [Lower.Contains]
            · have realNotLess : ¬toReal left < toReal right := by
                simpa only [toReal_lt_iff] using less
              have realNotEqual : toReal left ≠ toReal right := by
                intro same
                exact equal (toReal_inj.mp same)
              have realOrder : toReal right < toReal left :=
                lt_of_le_of_ne (le_of_not_gt realNotLess) (Ne.symm realNotEqual)
              rw [Raw.intersectLowerUnchecked]
              simp only [less, equal, ↓reduceIte]
              constructor
              · intro leftBound
                refine ⟨leftBound, ?_⟩
                cases leftStrict <;> cases rightStrict <;>
                  simp [Lower.Contains] at leftBound ⊢ <;> linarith
              · exact fun bounds => bounds.1

theorem upperContains_intersect (left right : Upper) (x : ℝ) :
    (Raw.intersectUpperUnchecked left right).Contains x ↔
      left.Contains x ∧ right.Contains x := by
  cases left with
  | unbounded => simp [Raw.intersectUpperUnchecked, Upper.Contains]
  | finite left leftStrict =>
      cases right with
      | unbounded => simp [Raw.intersectUpperUnchecked, Upper.Contains]
      | finite right rightStrict =>
          by_cases less : left < right
          · have realOrder := toReal_lt less
            rw [Raw.intersectUpperUnchecked]
            simp only [less, ↓reduceIte]
            constructor
            · intro leftBound
              refine ⟨leftBound, ?_⟩
              cases leftStrict <;> cases rightStrict <;>
                simp [Upper.Contains] at leftBound ⊢ <;> linarith
            · exact fun bounds => bounds.1
          · by_cases equal : left = right
            · subst right
              rw [Raw.intersectUpperUnchecked]
              simp only [less, ↓reduceIte]
              cases leftStrict <;> cases rightStrict
              · simp [Upper.Contains]
              · change x < toReal left ↔ x ≤ toReal left ∧ x < toReal left
                constructor
                · exact fun bound => ⟨le_of_lt bound, bound⟩
                · exact fun bounds => bounds.2
              · change x < toReal left ↔ x < toReal left ∧ x ≤ toReal left
                constructor
                · exact fun bound => ⟨bound, le_of_lt bound⟩
                · exact fun bounds => bounds.1
              · simp [Upper.Contains]
            · have realNotLess : ¬toReal left < toReal right := by
                simpa only [toReal_lt_iff] using less
              have realNotEqual : toReal left ≠ toReal right := by
                intro same
                exact equal (toReal_inj.mp same)
              have realOrder : toReal right < toReal left :=
                lt_of_le_of_ne (le_of_not_gt realNotLess) (Ne.symm realNotEqual)
              rw [Raw.intersectUpperUnchecked]
              simp only [less, equal, ↓reduceIte]
              constructor
              · intro rightBound
                refine ⟨?_, rightBound⟩
                cases leftStrict <;> cases rightStrict <;>
                  simp [Upper.Contains] at rightBound ⊢ <;> linarith
              · exact fun bounds => bounds.2

private theorem rawContains_intersect (left right : Raw) (x : ℝ) :
    (Raw.intersectUnchecked left right).Contains x ↔
      left.Contains x ∧ right.Contains x := by
  cases left with
  | empty => simp [Raw.intersectUnchecked, Raw.Contains]
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.intersectUnchecked, Raw.Contains]
      | bounds rightLower rightUpper =>
          rw [Raw.intersectUnchecked]
          change
            (Raw.intersectLowerUnchecked leftLower rightLower).Contains x ∧
                (Raw.intersectUpperUnchecked leftUpper rightUpper).Contains x ↔ _
          rw [lowerContains_intersect, upperContains_intersect]
          simp only [Raw.Contains]
          aesop

/-- A successful executable intersection denotes exactly the conjunction of
the two input interval predicates. -/
theorem contains_intersectWithin {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (checked : intersectWithin limit left right = .ready result) (x : ℝ) :
    result.Contains x ↔ left.Contains x ∧ right.Contains x := by
  simp only [Contains]
  rw [view_intersectWithin_ready checked, contains_normalize]
  exact rawContains_intersect left.view right.view x

theorem lowerContains_hull (left right : Lower) (x : ℝ) :
    (Raw.hullLowerUnchecked left right).Contains x ↔
      left.Contains x ∨ right.Contains x := by
  cases left with
  | unbounded => simp [Raw.hullLowerUnchecked, Lower.Contains]
  | finite left leftStrict =>
      cases right with
      | unbounded => simp [Raw.hullLowerUnchecked, Lower.Contains]
      | finite right rightStrict =>
          by_cases less : left < right
          · have realOrder := toReal_lt less
            rw [Raw.hullLowerUnchecked]
            simp only [less, ↓reduceIte]
            constructor
            · exact Or.inl
            · rintro (leftBound | rightBound)
              · exact leftBound
              · cases leftStrict <;> cases rightStrict <;>
                  simp [Lower.Contains] at * <;> linarith
          · by_cases equal : left = right
            · subst right
              rw [Raw.hullLowerUnchecked]
              simp only [less, ↓reduceIte]
              cases leftStrict <;> cases rightStrict <;>
                simp [Lower.Contains] <;> exact le_of_lt
            · have realNotLess : ¬toReal left < toReal right := by
                simpa only [toReal_lt_iff] using less
              have realNotEqual : toReal left ≠ toReal right := by
                intro same
                exact equal (toReal_inj.mp same)
              have realOrder : toReal right < toReal left :=
                lt_of_le_of_ne (le_of_not_gt realNotLess) (Ne.symm realNotEqual)
              rw [Raw.hullLowerUnchecked]
              simp only [less, equal, ↓reduceIte]
              constructor
              · exact Or.inr
              · rintro (leftBound | rightBound)
                · cases leftStrict <;> cases rightStrict <;>
                    simp [Lower.Contains] at * <;> linarith
                · exact rightBound

theorem upperContains_hull (left right : Upper) (x : ℝ) :
    (Raw.hullUpperUnchecked left right).Contains x ↔
      left.Contains x ∨ right.Contains x := by
  cases left with
  | unbounded => simp [Raw.hullUpperUnchecked, Upper.Contains]
  | finite left leftStrict =>
      cases right with
      | unbounded => simp [Raw.hullUpperUnchecked, Upper.Contains]
      | finite right rightStrict =>
          by_cases less : left < right
          · have realOrder := toReal_lt less
            rw [Raw.hullUpperUnchecked]
            simp only [less, ↓reduceIte]
            constructor
            · exact Or.inr
            · rintro (leftBound | rightBound)
              · cases leftStrict <;> cases rightStrict <;>
                  simp [Upper.Contains] at * <;> linarith
              · exact rightBound
          · by_cases equal : left = right
            · subst right
              rw [Raw.hullUpperUnchecked]
              simp only [less, ↓reduceIte]
              cases leftStrict <;> cases rightStrict <;>
                simp [Upper.Contains] <;> exact le_of_lt
            · have realNotLess : ¬toReal left < toReal right := by
                simpa only [toReal_lt_iff] using less
              have realNotEqual : toReal left ≠ toReal right := by
                intro same
                exact equal (toReal_inj.mp same)
              have realOrder : toReal right < toReal left :=
                lt_of_le_of_ne (le_of_not_gt realNotLess) (Ne.symm realNotEqual)
              rw [Raw.hullUpperUnchecked]
              simp only [less, equal, ↓reduceIte]
              constructor
              · exact Or.inl
              · rintro (leftBound | rightBound)
                · exact leftBound
                · cases leftStrict <;> cases rightStrict <;>
                    simp [Upper.Contains] at * <;> linarith

private theorem rawContains_hull (left right : Raw) (x : ℝ) :
    (Raw.hullUnchecked left right).Contains x ↔ left.HullContains right x := by
  cases left with
  | empty => simp [Raw.hullUnchecked, Raw.HullContains]
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.hullUnchecked, Raw.HullContains]
      | bounds rightLower rightUpper =>
          rw [Raw.hullUnchecked]
          change
            (Raw.hullLowerUnchecked leftLower rightLower).Contains x ∧
                (Raw.hullUpperUnchecked leftUpper rightUpper).Contains x ↔ _
          rw [lowerContains_hull, upperContains_hull]
          rfl

/-- Exact membership in a successful interval hull. For two nonempty inputs
this is the selected-cut (equivalently, interval-convex-closure)
characterization, not membership in the set union. -/
theorem contains_hullWithin {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (checked : hullWithin limit left right = .ready result) (x : ℝ) :
    result.Contains x ↔ left.view.HullContains right.view x := by
  simp only [Contains]
  rw [view_hullWithin_ready checked, contains_normalize]
  exact rawContains_hull left.view right.view x

private theorem rawContains_hull_left (left right : Raw) (x : ℝ) :
    left.Contains x → left.HullContains right x := by
  cases left with
  | empty => simp [Raw.Contains]
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.HullContains]
      | bounds rightLower rightUpper =>
          rintro ⟨lower, upper⟩
          exact ⟨Or.inl lower, Or.inl upper⟩

private theorem rawContains_hull_right (left right : Raw) (x : ℝ) :
    right.Contains x → left.HullContains right x := by
  cases left with
  | empty => simp [Raw.HullContains]
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.Contains]
      | bounds rightLower rightUpper =>
          rintro ⟨lower, upper⟩
          exact ⟨Or.inr lower, Or.inr upper⟩

/-- Every member of the left input belongs to a successful hull. -/
theorem contains_hullWithin_left {limit : EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : hullWithin limit left right = .ready result)
    (member : left.Contains x) : result.Contains x :=
  (contains_hullWithin checked x).2
    (rawContains_hull_left left.view right.view x member)

/-- Every member of the right input belongs to a successful hull. -/
theorem contains_hullWithin_right {limit : EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : hullWithin limit left right = .ready result)
    (member : right.Contains x) : result.Contains x :=
  (contains_hullWithin checked x).2
    (rawContains_hull_right left.view right.view x member)

private theorem lowerContains_neg (upper : Upper) (x : ℝ) :
    (match upper with
      | .unbounded => Lower.unbounded
      | .finite value strict => Lower.finite (-value) strict).Contains x ↔
      upper.Contains (-x) := by
  cases upper with
  | unbounded => simp [Lower.Contains, Upper.Contains]
  | finite value strict =>
      cases strict
      · change toReal (-value) ≤ x ↔ -x ≤ toReal value
        rw [toReal_neg]
        constructor <;> intro bound <;> linarith
      · change toReal (-value) < x ↔ -x < toReal value
        rw [toReal_neg]
        constructor <;> intro bound <;> linarith

private theorem upperContains_neg (lower : Lower) (x : ℝ) :
    (match lower with
      | .unbounded => Upper.unbounded
      | .finite value strict => Upper.finite (-value) strict).Contains x ↔
      lower.Contains (-x) := by
  cases lower with
  | unbounded => simp [Lower.Contains, Upper.Contains]
  | finite value strict =>
      cases strict
      · change x ≤ toReal (-value) ↔ toReal value ≤ -x
        rw [toReal_neg]
        constructor <;> intro bound <;> linarith
      · change x < toReal (-value) ↔ toReal value < -x
        rw [toReal_neg]
        constructor <;> intro bound <;> linarith

/-- Raw negation contains `x` exactly when its source contains `-x`. -/
theorem contains_negUnchecked (raw : Raw) (x : ℝ) :
    raw.negUnchecked.Contains x ↔ raw.Contains (-x) := by
  cases raw with
  | empty => simp [Raw.negUnchecked, Raw.Contains]
  | bounds lower upper =>
      change
        (match upper with
          | .unbounded => Lower.unbounded
          | .finite value strict => Lower.finite (-value) strict).Contains x ∧
          (match lower with
          | .unbounded => Upper.unbounded
          | .finite value strict => Upper.finite (-value) strict).Contains x ↔ _
      rw [lowerContains_neg, upperContains_neg]
      simp only [Raw.Contains, and_comm]

/-- A successful executable negation contains `x` exactly when the input
contains `-x`. -/
theorem contains_negWithin {limit : EndpointLimit} {input result : Hex.Interval}
    (checked : negWithin limit input = .ready result) (x : ℝ) :
    result.Contains x ↔ input.Contains (-x) := by
  simp only [Contains]
  rw [view_negWithin_ready checked, contains_normalize]
  exact contains_negUnchecked input.view x

end Hex.Interval
