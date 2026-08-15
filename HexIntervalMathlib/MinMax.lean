/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Interval

@[expose] public section

/-!
# Real semantics for interval minimum and maximum

The exact selected-cut predicates characterize the computed interval. The
image theorems prove that pointwise real minimum and maximum are enclosed; no
converse set-image theorem is claimed here.
-/

namespace Hex.Interval

/-- Exact selected-cut meaning of the interval image under binary minimum. -/
def Raw.MinContains : Raw → Raw → ℝ → Prop
  | .empty, _, _ | _, .empty, _ => False
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper, x =>
      (leftLower.Contains x ∨ rightLower.Contains x) ∧
        (leftUpper.Contains x ∧ rightUpper.Contains x)

/-- Exact selected-cut meaning of the interval image under binary maximum. -/
def Raw.MaxContains : Raw → Raw → ℝ → Prop
  | .empty, _, _ | _, .empty, _ => False
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper, x =>
      (leftLower.Contains x ∧ rightLower.Contains x) ∧
        (leftUpper.Contains x ∨ rightUpper.Contains x)

private theorem rawContains_min (left right : Raw) (x : ℝ) :
    (Raw.minUnchecked left right).Contains x ↔ left.MinContains right x := by
  cases left with
  | empty => simp [Raw.minUnchecked, Raw.Contains, Raw.MinContains]
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.minUnchecked, Raw.Contains, Raw.MinContains]
      | bounds rightLower rightUpper =>
          rw [Raw.minUnchecked]
          change
            (Raw.hullLowerUnchecked leftLower rightLower).Contains x ∧
                (Raw.intersectUpperUnchecked leftUpper rightUpper).Contains x ↔ _
          rw [lowerContains_hull, upperContains_intersect]
          rfl

private theorem rawContains_max (left right : Raw) (x : ℝ) :
    (Raw.maxUnchecked left right).Contains x ↔ left.MaxContains right x := by
  cases left with
  | empty => simp [Raw.maxUnchecked, Raw.Contains, Raw.MaxContains]
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.maxUnchecked, Raw.Contains, Raw.MaxContains]
      | bounds rightLower rightUpper =>
          rw [Raw.maxUnchecked]
          change
            (Raw.intersectLowerUnchecked leftLower rightLower).Contains x ∧
                (Raw.hullUpperUnchecked leftUpper rightUpper).Contains x ↔ _
          rw [lowerContains_intersect, upperContains_hull]
          rfl

/-- A successful minimum has exactly its selected lower and upper cut
predicates, including empty absorption and unbounded sides. -/
theorem contains_minWithin {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (checked : minWithin limit left right = .ready result) (x : ℝ) :
    result.Contains x ↔ left.view.MinContains right.view x := by
  simp only [Contains]
  rw [view_minWithin_ready checked, contains_normalize]
  exact rawContains_min left.view right.view x

/-- A successful maximum has exactly its selected lower and upper cut
predicates, including empty absorption and unbounded sides. -/
theorem contains_maxWithin {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (checked : maxWithin limit left right = .ready result) (x : ℝ) :
    result.Contains x ↔ left.view.MaxContains right.view x := by
  simp only [Contains]
  rw [view_maxWithin_ready checked, contains_normalize]
  exact rawContains_max left.view right.view x

private theorem lowerContains_mono (cut : Lower) {x y : ℝ}
    (xy : x ≤ y) (member : cut.Contains x) : cut.Contains y := by
  cases cut with
  | unbounded => trivial
  | finite value strict => cases strict <;> simp [Lower.Contains] at member ⊢ <;> linarith

private theorem upperContains_anti (cut : Upper) {x y : ℝ}
    (xy : x ≤ y) (member : cut.Contains y) : cut.Contains x := by
  cases cut with
  | unbounded => trivial
  | finite value strict => cases strict <;> simp [Upper.Contains] at member ⊢ <;> linarith

private theorem rawMinImage {left right : Raw} {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    left.MinContains right (min x y) := by
  cases left with
  | empty => simp [Raw.Contains] at leftMember
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.Contains] at rightMember
      | bounds rightLower rightUpper =>
          rcases leftMember with ⟨leftLowerMember, leftUpperMember⟩
          rcases rightMember with ⟨rightLowerMember, rightUpperMember⟩
          by_cases xy : x ≤ y
          · rw [min_eq_left xy]
            exact ⟨Or.inl leftLowerMember,
              leftUpperMember, upperContains_anti rightUpper xy rightUpperMember⟩
          · have yx : y ≤ x := le_of_not_ge xy
            rw [min_eq_right yx]
            exact ⟨Or.inr rightLowerMember,
              upperContains_anti leftUpper yx leftUpperMember, rightUpperMember⟩

private theorem rawMaxImage {left right : Raw} {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    left.MaxContains right (max x y) := by
  cases left with
  | empty => simp [Raw.Contains] at leftMember
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.Contains] at rightMember
      | bounds rightLower rightUpper =>
          rcases leftMember with ⟨leftLowerMember, leftUpperMember⟩
          rcases rightMember with ⟨rightLowerMember, rightUpperMember⟩
          by_cases xy : x ≤ y
          · rw [max_eq_right xy]
            exact ⟨⟨lowerContains_mono leftLower xy leftLowerMember,
              rightLowerMember⟩, Or.inr rightUpperMember⟩
          · have yx : y ≤ x := le_of_not_ge xy
            rw [max_eq_left yx]
            exact ⟨⟨leftLowerMember,
              lowerContains_mono rightLower yx rightLowerMember⟩,
              Or.inl leftUpperMember⟩

/-- Pointwise real minimum of two input members belongs to every successful
computed minimum interval. -/
theorem min_mem_minWithin {limit : EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : minWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (min x y) :=
  (contains_minWithin checked (min x y)).2
    (rawMinImage leftMember rightMember)

/-- Pointwise real maximum of two input members belongs to every successful
computed maximum interval. -/
theorem max_mem_maxWithin {limit : EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : maxWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (max x y) :=
  (contains_maxWithin checked (max x y)).2
    (rawMaxImage leftMember rightMember)

end Hex.Interval
