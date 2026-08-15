/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Interval

@[expose] public section

/-!
# Exact semantics of checked interval splitting

The public split owns its dyadic point on the left and excludes it on the
right. This module proves exact child membership directly from the supported
raw cuts; the experimental branch manager and propagation fact domain are not
proof inputs.
-/

namespace Hex.Interval

private theorem upperContains_split (upper : Upper) (point : Dyadic) (x : ℝ) :
    (Raw.intersectUpperUnchecked upper (.finite point false)).Contains x ↔
      upper.Contains x ∧ x ≤ toReal point := by
  simpa [Upper.Contains] using
    upperContains_intersect upper (.finite point false) x

private theorem lowerContains_split (lower : Lower) (point : Dyadic) (x : ℝ) :
    (Raw.intersectLowerUnchecked lower (.finite point true)).Contains x ↔
      lower.Contains x ∧ toReal point < x := by
  simpa [Lower.Contains] using
    lowerContains_intersect lower (.finite point true) x

private theorem rawContains_splitLeft (raw : Raw) (point : Dyadic) (x : ℝ) :
    (raw.splitUnchecked point).1.Contains x ↔
      raw.Contains x ∧ x ≤ toReal point := by
  cases raw with
  | empty => simp [Raw.splitUnchecked, Raw.Contains]
  | bounds lower upper =>
      simp only [Raw.splitUnchecked, Raw.Contains]
      rw [upperContains_split]
      aesop

private theorem rawContains_splitRight (raw : Raw) (point : Dyadic) (x : ℝ) :
    (raw.splitUnchecked point).2.Contains x ↔
      raw.Contains x ∧ toReal point < x := by
  cases raw with
  | empty => simp [Raw.splitUnchecked, Raw.Contains]
  | bounds lower upper =>
      simp only [Raw.splitUnchecked, Raw.Contains]
      rw [lowerContains_split]
      aesop

/-- Exact membership in the left child: original membership together with the
closed condition `x ≤ point`. -/
theorem contains_splitWithin_left {limit : EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (checked : splitWithin limit input point = .ready left right) (x : ℝ) :
    left.Contains x ↔ input.Contains x ∧ x ≤ toReal point := by
  have views := view_splitWithin_ready checked
  simp only [Contains]
  rw [views.1, contains_normalize]
  exact rawContains_splitLeft input.view point x

/-- Exact membership in the right child: original membership together with
the strict condition `point < x`. -/
theorem contains_splitWithin_right {limit : EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (checked : splitWithin limit input point = .ready left right) (x : ℝ) :
    right.Contains x ↔ input.Contains x ∧ toReal point < x := by
  have views := view_splitWithin_ready checked
  simp only [Contains]
  rw [views.2, contains_normalize]
  exact rawContains_splitRight input.view point x

/-- Both children are subsets of the source interval. -/
theorem splitWithin_contained {limit : EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (checked : splitWithin limit input point = .ready left right) {x : ℝ} :
    (left.Contains x → input.Contains x) ∧
      (right.Contains x → input.Contains x) :=
  ⟨fun member => (contains_splitWithin_left checked x).1 member |>.1,
    fun member => (contains_splitWithin_right checked x).1 member |>.1⟩

/-- The two children cover the source interval. -/
theorem splitWithin_cover {limit : EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (checked : splitWithin limit input point = .ready left right) {x : ℝ}
    (member : input.Contains x) : left.Contains x ∨ right.Contains x := by
  by_cases side : x ≤ toReal point
  · exact Or.inl ((contains_splitWithin_left checked x).2 ⟨member, side⟩)
  · exact Or.inr ((contains_splitWithin_right checked x).2
      ⟨member, lt_of_not_ge side⟩)

/-- The left-closed/right-open ownership makes the children disjoint. -/
theorem splitWithin_disjoint {limit : EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (checked : splitWithin limit input point = .ready left right) (x : ℝ) :
    ¬(left.Contains x ∧ right.Contains x) := by
  rintro ⟨leftMember, rightMember⟩
  have leftBound := (contains_splitWithin_left checked x).1 leftMember |>.2
  have rightBound := (contains_splitWithin_right checked x).1 rightMember |>.2
  exact (not_lt_of_ge leftBound) rightBound

/-- The split point belongs to the left child exactly when it belonged to the
source. -/
theorem splitWithin_point_left {limit : EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (checked : splitWithin limit input point = .ready left right) :
    left.Contains (toReal point) ↔ input.Contains (toReal point) := by
  simpa using contains_splitWithin_left checked (toReal point)

/-- The strict right child never owns the split point. -/
theorem splitWithin_point_not_right {limit : EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (checked : splitWithin limit input point = .ready left right) :
    ¬right.Contains (toReal point) := by
  intro member
  exact lt_irrefl _ ((contains_splitWithin_right checked _).1 member |>.2)

end Hex.Interval
