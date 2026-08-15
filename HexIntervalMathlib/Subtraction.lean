/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexIntervalMathlib.Addition

@[expose] public section

/-!
# Exact semantics of public interval subtraction

This module relates successful resource-checked subtraction to its computed
crossed endpoint cuts and proves the arithmetic image theorem. Empty inputs
are absorbing, unbounded cuts remain independent, and a finite result endpoint
is strict exactly when either contributing endpoint is strict.
-/

namespace Hex.Interval

@[simp]
theorem toReal_sub (left right : Dyadic) :
    toReal (left - right) = toReal left - toReal right := by
  simp [toReal]

/-- Computed cut-level Minkowski-difference predicate. Empty is absorbing. For
two nonempty inputs it uses the left lower minus right upper cut and the left
upper minus right lower cut. -/
def Raw.SubContains : Raw → Raw → ℝ → Prop
  | .empty, _, _ | _, .empty, _ => False
  | .bounds leftLower leftUpper, .bounds rightLower rightUpper, x =>
      (Raw.subLowerUnchecked leftLower rightUpper).Contains x ∧
        (Raw.subUpperUnchecked leftUpper rightLower).Contains x

private theorem rawContains_subUnchecked (left right : Raw) (x : ℝ) :
    (Raw.subUnchecked left right).Contains x ↔ left.SubContains right x := by
  cases left <;> cases right <;>
    simp [Raw.subUnchecked, Raw.Contains, Raw.SubContains]

private theorem lowerContains_sub (left : Lower) (right : Upper) {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    (Raw.subLowerUnchecked left right).Contains (x - y) := by
  cases left with
  | unbounded => simp [Raw.subLowerUnchecked, Lower.Contains]
  | finite left leftStrict =>
      cases right with
      | unbounded => simp [Raw.subLowerUnchecked, Lower.Contains]
      | finite right rightStrict =>
          cases leftStrict <;> cases rightStrict <;>
            simp [Raw.subLowerUnchecked, Lower.Contains, Upper.Contains,
              toReal_sub] at * <;>
            linarith

private theorem upperContains_sub (left : Upper) (right : Lower) {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    (Raw.subUpperUnchecked left right).Contains (x - y) := by
  cases left with
  | unbounded => simp [Raw.subUpperUnchecked, Upper.Contains]
  | finite left leftStrict =>
      cases right with
      | unbounded => simp [Raw.subUpperUnchecked, Upper.Contains]
      | finite right rightStrict =>
          cases leftStrict <;> cases rightStrict <;>
            simp [Raw.subUpperUnchecked, Lower.Contains, Upper.Contains,
              toReal_sub] at * <;>
            linarith

private theorem rawContains_sub (left right : Raw) {x y : ℝ}
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    (Raw.subUnchecked left right).Contains (x - y) := by
  cases left with
  | empty => simp [Raw.Contains] at leftMember
  | bounds leftLower leftUpper =>
      cases right with
      | empty => simp [Raw.Contains] at rightMember
      | bounds rightLower rightUpper =>
          rcases leftMember with ⟨leftLowerMember, leftUpperMember⟩
          rcases rightMember with ⟨rightLowerMember, rightUpperMember⟩
          exact ⟨
            lowerContains_sub leftLower rightUpper leftLowerMember rightUpperMember,
            upperContains_sub leftUpper rightLower leftUpperMember rightLowerMember⟩

/-- A successful public subtraction has the normalized raw crossed difference
cuts. This characterizes the computed cut predicate; `sub_mem_subWithin`
supplies the representation-independent enclosure theorem. -/
theorem contains_subWithin {limit : EndpointLimit}
    {left right result : Hex.Interval}
    (checked : subWithin limit left right = .ready result) (x : ℝ) :
    result.Contains x ↔ left.view.SubContains right.view x := by
  simp only [Contains]
  rw [view_subWithin_ready checked, contains_normalize]
  exact rawContains_subUnchecked left.view right.view x

/-- Subtraction maps every pair of input members into the successful public
Minkowski difference. -/
theorem sub_mem_subWithin {limit : EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : subWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (x - y) :=
  (contains_subWithin checked (x - y)).2
    ((rawContains_subUnchecked left.view right.view (x - y)).1
      (rawContains_sub left.view right.view leftMember rightMember))

end Hex.Interval
