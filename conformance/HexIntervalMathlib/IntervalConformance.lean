/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

import HexIntervalMathlib

/-!
Conformance checks for the supported public interval semantics.  Computational
shape/resource cases live in `HexInterval.Conformance`; this companion pins the
ordinary-kernel meaning of every successful intersection and negation.
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

/-- Public negation transports membership in both directions. -/
theorem negMember {limit : Hex.Interval.EndpointLimit}
    {input result : Hex.Interval} {x : ℝ}
    (checked : Hex.Interval.negWithin limit input = .ready result) :
    result.Contains x ↔ input.Contains (-x) :=
  Hex.Interval.contains_negWithin checked x

/-- info: 'Hex.IntervalMathlib.Conformance.intersectMember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intersectMember

/-- info: 'Hex.IntervalMathlib.Conformance.intersectInputs' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms intersectInputs

/-- info: 'Hex.IntervalMathlib.Conformance.negMember' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms negMember

end Hex.IntervalMathlib.Conformance
