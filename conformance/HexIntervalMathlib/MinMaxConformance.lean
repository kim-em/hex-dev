/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib

/-!
# Minimum and maximum semantic conformance

The ordinary-kernel wrappers pin the exact selected-cut characterizations and
the two real-image enclosure theorems without asserting a set-image converse.
-/

namespace Hex.IntervalMathlib.MinMaxConformance

theorem minExact {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.minWithin limit left right = .ready result) :
    result.Contains x ↔ left.view.MinContains right.view x :=
  Hex.Interval.contains_minWithin checked x

theorem minImage {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : Hex.Interval.minWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (min x y) :=
  Hex.Interval.min_mem_minWithin checked leftMember rightMember

theorem maxExact {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.maxWithin limit left right = .ready result) :
    result.Contains x ↔ left.view.MaxContains right.view x :=
  Hex.Interval.contains_maxWithin checked x

theorem maxImage {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : Hex.Interval.maxWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (max x y) :=
  Hex.Interval.max_mem_maxWithin checked leftMember rightMember

/-- info: 'Hex.IntervalMathlib.MinMaxConformance.minExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minExact

/-- info: 'Hex.IntervalMathlib.MinMaxConformance.minImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms minImage

/-- info: 'Hex.IntervalMathlib.MinMaxConformance.maxExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms maxExact

/-- info: 'Hex.IntervalMathlib.MinMaxConformance.maxImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms maxImage

end Hex.IntervalMathlib.MinMaxConformance
