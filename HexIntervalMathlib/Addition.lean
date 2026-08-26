/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Interval

@[expose] public section

/-!
# Exact semantics of public interval addition

This module relates successful resource-checked addition to the exact raw
Minkowski-sum cuts and proves the arithmetic image theorem used by propagators.
Empty inputs are absorbing, unbounded cuts remain independent, and a finite
result endpoint is strict exactly when either contributing endpoint is strict.
-/

namespace Hex.Interval

@[simp]
theorem toReal_add (left right : Dyadic) :
    toReal (left + right) = toReal left + toReal right := by
  simp [toReal]

/-- Computed cut-level sum predicate. Empty is absorbing. For two
nonempty inputs it is the conjunction of the summed lower and upper cuts;
unboundedness and endpoint attainment are therefore represented independently
on the two sides. -/
def Raw.AddContains : Raw → Raw → ℝ → Prop
  | .empty, _, _ | _, .empty, _ => False
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper, x =>
      (Raw.addLowerUnchecked leftLower rightLower).Contains x ∧
        (Raw.addUpperUnchecked leftUpper rightUpper).Contains x

private theorem rawContains_addUnchecked (left right : Raw) (x : ℝ) :
    (Raw.addUnchecked left right).Contains x ↔ left.AddContains right x := by
  cases left <;> cases right <;>
    simp [Raw.addUnchecked, Raw.Contains, Raw.AddContains]

private theorem lowerContains_add (left right : Lower) {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    (Raw.addLowerUnchecked left right).Contains (x + y) := by
  cases left with
  | unbounded => simp [Raw.addLowerUnchecked, Lower.Contains]
  | finite left leftStrict =>
      cases right with
      | unbounded => simp [Raw.addLowerUnchecked, Lower.Contains]
      | finite right rightStrict =>
          cases leftStrict <;> cases rightStrict <;>
            simp [Raw.addLowerUnchecked, Lower.Contains, toReal_add] at * <;>
            linarith

private theorem upperContains_add (left right : Upper) {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    (Raw.addUpperUnchecked left right).Contains (x + y) := by
  cases left with
  | unbounded => simp [Raw.addUpperUnchecked, Upper.Contains]
  | finite left leftStrict =>
      cases right with
      | unbounded => simp [Raw.addUpperUnchecked, Upper.Contains]
      | finite right rightStrict =>
          cases leftStrict <;> cases rightStrict <;>
            simp [Raw.addUpperUnchecked, Upper.Contains, toReal_add] at * <;>
            linarith

private theorem rawContains_add (left right : Raw) {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    (Raw.addUnchecked left right).Contains (x + y) := by
  cases left with
  | empty => simp [Raw.Contains] at leftMember
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.Contains] at rightMember
      | bounds rightLower rightUpper =>
          rcases leftMember with ⟨leftLowerMember, leftUpperMember⟩
          rcases rightMember with ⟨rightLowerMember, rightUpperMember⟩
          exact ⟨
            lowerContains_add leftLower rightLower leftLowerMember rightLowerMember,
            upperContains_add leftUpper rightUpper leftUpperMember rightUpperMember⟩

/-- A successful public addition has the normalized raw summed cuts. This
characterizes the computed cut predicate; `add_mem_addWithin` supplies the
representation-independent enclosure theorem. -/
theorem contains_addWithin {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (checked : addWithin limit left right = .ready result) (x : ℝ) :
    result.Contains x ↔ left.view.AddContains right.view x := by
  simp only [Contains]
  rw [view_addWithin_ready checked, contains_normalize]
  exact rawContains_addUnchecked left.view right.view x

/-- Addition maps every pair of input members into the successful public
Minkowski sum. -/
theorem add_mem_addWithin {limit : EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : addWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (x + y) :=
  (contains_addWithin checked (x + y)).2
    ((rawContains_addUnchecked left.view right.view (x + y)).1
      (rawContains_add left.view right.view leftMember rightMember))

end Hex.Interval
