/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib

/-!
Conformance checks for the supported public interval semantics.  Computational
shape/resource cases live in `HexInterval.Conformance`; this companion pins the
ordinary-kernel meaning of every successful intersection, hull, addition,
subtraction, multiplication, negation, absolute value, and natural power.
-/

namespace Hex.IntervalMathlib.Conformance

/-- Both input membership proofs are required to establish membership in a
successful public intersection. -/
theorem intersectMember {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.intersectWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains x) :
    result.Contains x :=
  (Hex.Interval.contains_intersectWithin checked x).2 ⟨leftMember, rightMember⟩

/-- Membership in the public intersection recovers both exact input facts. -/
theorem intersectInputs {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.intersectWithin limit left right = .ready result)
    (member : result.Contains x) : left.Contains x ∧ right.Contains x :=
  (Hex.Interval.contains_intersectWithin checked x).1 member

/-- A successful hull has the exact selected-cut/interval-closure meaning,
including explicit empty identities. -/
theorem hullExact {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.hullWithin limit left right = .ready result) :
    result.Contains x ↔ left.view.HullContains right.view x :=
  Hex.Interval.contains_hullWithin checked x

/-- The left input is contained in every successful public hull. -/
theorem hullLeft {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.hullWithin limit left right = .ready result)
    (member : left.Contains x) : result.Contains x :=
  Hex.Interval.contains_hullWithin_left checked member

/-- The right input is contained in every successful public hull. -/
theorem hullRight {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.hullWithin limit left right = .ready result)
    (member : right.Contains x) : result.Contains x :=
  Hex.Interval.contains_hullWithin_right checked member

/-- Public negation transports membership in both directions. -/
theorem negMember {limit : Hex.Interval.EndpointLimit}
    {input result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.negWithin limit input = .ready result) :
    result.Contains x ↔ input.Contains (-x) :=
  Hex.Interval.contains_negWithin checked x

/-- A successful addition has exactly its independent summed lower and upper
cut semantics, including empty absorption and unbounded sides. -/
theorem addExact {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.addWithin limit left right = .ready result) :
    result.Contains x ↔ left.view.AddContains right.view x :=
  Hex.Interval.contains_addWithin checked x

/-- Both source membership proofs are consumed by the arithmetic image
theorem for successful interval addition. -/
theorem addImage {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : Hex.Interval.addWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (x + y) :=
  Hex.Interval.add_mem_addWithin checked leftMember rightMember

/-- A successful subtraction has exactly its crossed lower and upper cut
semantics, including empty absorption and independent unbounded sides. -/
theorem subExact {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.subWithin limit left right = .ready result) :
    result.Contains x ↔ left.view.SubContains right.view x :=
  Hex.Interval.contains_subWithin checked x

/-- Both source membership proofs are consumed by the arithmetic image
theorem for successful interval subtraction. -/
theorem subImage {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : Hex.Interval.subWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (x - y) :=
  Hex.Interval.sub_mem_subWithin checked leftMember rightMember

/-- A successful absolute value has exactly its selected raw cuts. -/
theorem absExact {limit : Hex.Interval.EndpointLimit}
    {input result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.absWithin limit input = .ready result) :
    result.Contains x ↔ input.view.absUnchecked.Contains x :=
  Hex.Interval.contains_absWithin checked x

/-- Source membership is consumed by the absolute-value image theorem. -/
theorem absImage {limit : Hex.Interval.EndpointLimit}
    {input result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.absWithin limit input = .ready result)
    (member : input.Contains x) : result.Contains |x| :=
  Hex.Interval.abs_mem_absWithin checked member

/-- A successful multiplication has exactly its normalized computed corner
candidate semantics. -/
theorem mulExact {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.mulWithin limit left right = .ready result) :
    result.Contains x ↔ left.view.MulContains right.view x :=
  Hex.Interval.contains_mulWithin checked x

/-- Both source membership proofs are consumed by the arithmetic image theorem
for successful interval multiplication. -/
theorem mulImage {limit : Hex.Interval.EndpointLimit}
    {left right result : Hex.Interval} {x y : ℝ}
    (checked : Hex.Interval.mulWithin limit left right = .ready result)
    (leftMember : left.Contains x) (rightMember : right.Contains y) :
    result.Contains (x * y) :=
  Hex.Interval.mul_mem_mulWithin checked leftMember rightMember

/-- A successful natural power has exactly its normalized selected raw cuts. -/
theorem powExact {limit : Hex.Interval.EndpointLimit}
    {workLimits : Hex.Interval.Arithmetic.PowLimits}
    {input result : Hex.Interval} {exponent : Nat} {x : ℝ}
    (checked : Hex.Interval.powWithin limit workLimits input exponent =
      .ready result) :
    result.Contains x ↔ (input.view.powUnchecked exponent).Contains x :=
  Hex.Interval.contains_powWithin checked x

/-- Source membership and the caller's exponent are consumed by the direct
natural-power image theorem. -/
theorem powImage {limit : Hex.Interval.EndpointLimit}
    {workLimits : Hex.Interval.Arithmetic.PowLimits}
    {input result : Hex.Interval} {exponent : Nat} {x : ℝ}
    (checked : Hex.Interval.powWithin limit workLimits input exponent =
      .ready result)
    (member : input.Contains x) : result.Contains (x ^ exponent) :=
  Hex.Interval.pow_mem_powWithin checked member

/-- Successful splitting has exact closed-left membership. -/
theorem splitLeft {limit : Hex.Interval.EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic} {x : ℝ}
    (checked : Hex.Interval.splitWithin limit input point = .ready left right) :
    left.Contains x ↔ input.Contains x ∧ x ≤ Hex.Interval.toReal point :=
  Hex.Interval.contains_splitWithin_left checked x

/-- Successful splitting has exact strict-right membership. -/
theorem splitRight {limit : Hex.Interval.EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic} {x : ℝ}
    (checked : Hex.Interval.splitWithin limit input point = .ready left right) :
    right.Contains x ↔ input.Contains x ∧ Hex.Interval.toReal point < x :=
  Hex.Interval.contains_splitWithin_right checked x

/-- Both source subsets are produced by a successful transactional split. -/
theorem splitCover {limit : Hex.Interval.EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic} {x : ℝ}
    (checked : Hex.Interval.splitWithin limit input point = .ready left right)
    (member : input.Contains x) : left.Contains x ∨ right.Contains x :=
  Hex.Interval.splitWithin_cover checked member

/-- Closed-left/strict-right ownership makes successful children disjoint. -/
theorem splitDisjoint {limit : Hex.Interval.EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic} (x : ℝ)
    (checked : Hex.Interval.splitWithin limit input point = .ready left right) :
    ¬(left.Contains x ∧ right.Contains x) :=
  Hex.Interval.splitWithin_disjoint checked x

/-- The point is owned by the left child exactly when it was in the source,
and is never owned by the right child. -/
theorem splitPoint {limit : Hex.Interval.EndpointLimit}
    {input left right : Hex.Interval} {point : Dyadic}
    (checked : Hex.Interval.splitWithin limit input point = .ready left right) :
    (left.Contains (Hex.Interval.toReal point) ↔
        input.Contains (Hex.Interval.toReal point)) ∧
      ¬right.Contains (Hex.Interval.toReal point) :=
  ⟨Hex.Interval.splitWithin_point_left checked,
    Hex.Interval.splitWithin_point_not_right checked⟩

/-- A successful reciprocal has exactly its computed connected outward-cut
predicate. This is cut exactness, not a claim that rounded cuts are attained
or that a connected hull equals the generally-disconnected image. -/
theorem invExact {limits : Hex.Interval.Arithmetic.PrecisionLimits}
    {precision : Hex.Interval.Precision} {input result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.invWithin limits precision input = .ready result) :
    result.Contains x ↔ input.view.InvContains precision x :=
  Hex.Interval.contains_invWithin checked x

/-- Lean's total reciprocal maps every source member into every successful
public enclosure, including `0⁻¹ = 0` and the connected hull across zero. -/
theorem invImage {limits : Hex.Interval.Arithmetic.PrecisionLimits}
    {precision : Hex.Interval.Precision} {input result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.invWithin limits precision input = .ready result)
    (member : input.Contains x) : result.Contains x⁻¹ :=
  Hex.Interval.inv_mem_invWithin checked member

/-- info: 'Hex.IntervalMathlib.Conformance.intersectMember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intersectMember

/-- info: 'Hex.IntervalMathlib.Conformance.intersectInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intersectInputs

/-- info: 'Hex.IntervalMathlib.Conformance.hullExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hullExact

/-- info: 'Hex.IntervalMathlib.Conformance.hullLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hullLeft

/-- info: 'Hex.IntervalMathlib.Conformance.hullRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hullRight

/-- info: 'Hex.IntervalMathlib.Conformance.negMember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negMember

/-- info: 'Hex.IntervalMathlib.Conformance.addExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms addExact

/-- info: 'Hex.IntervalMathlib.Conformance.addImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms addImage

/-- info: 'Hex.IntervalMathlib.Conformance.subExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subExact

/-- info: 'Hex.IntervalMathlib.Conformance.subImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms subImage

/-- info: 'Hex.IntervalMathlib.Conformance.absExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms absExact

/-- info: 'Hex.IntervalMathlib.Conformance.absImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms absImage

/-- info: 'Hex.IntervalMathlib.Conformance.mulExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulExact

/-- info: 'Hex.IntervalMathlib.Conformance.mulImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mulImage

/-- info: 'Hex.IntervalMathlib.Conformance.powExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms powExact

/-- info: 'Hex.IntervalMathlib.Conformance.powImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms powImage

/-- info: 'Hex.IntervalMathlib.Conformance.splitLeft' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitLeft

/-- info: 'Hex.IntervalMathlib.Conformance.splitRight' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitRight

/-- info: 'Hex.IntervalMathlib.Conformance.splitCover' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitCover

/-- info: 'Hex.IntervalMathlib.Conformance.splitDisjoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitDisjoint

/-- info: 'Hex.IntervalMathlib.Conformance.splitPoint' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms splitPoint

/-- info: 'Hex.IntervalMathlib.Conformance.invExact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invExact

/-- info: 'Hex.IntervalMathlib.Conformance.invImage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invImage

end Hex.IntervalMathlib.Conformance
