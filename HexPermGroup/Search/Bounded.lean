/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.BoundedLeaf
public import HexPermGroup.Search.Build

public section

namespace Hex.PermGroup.Search

namespace Bounded

variable {G : Group n} {P : Predicate n} {budget : Budget}

/-- The bounded traversal uses the same checked node decomposition and
coverage rules as exact search. Every stopping point retains a verified
lower bound; only a complete traversal returns a completeness certificate. -/
@[expose] def visit (C : Constraint G P) (Q : Tester P budget) (t : Node G)
    (a : Accumulator G P) (m : Meter budget) : Result C t a budget :=
  match m.spend .nodes 1 with
  | .error failure => Result.stop C t a failure
  | .ok meter =>
    match t.coveredWith a.group meter with
    | .exhausted failure => Result.stop C t a failure
    | .ok covered meter =>
      if hc : covered.val = true then
        Result.finish C t a a (fun _ hp => hp) (fun _ => .covered) (by
          simpa only [checkTree] using covered.property.symm.trans hc) meter
      else
        match C.refineWith t meter with
        | .exhausted failure => Result.stop C t a failure
        | .ok (some reason) meter =>
          Result.finish C t a a (fun _ hp => hp) (fun _ => .rejected reason.val) (by
            simpa only [checkTree] using reason.property) meter
        | .ok none meter =>
          match hs : t.suffix with
          | .leaf S words => leaf C Q t hs a meter
          | .cons level tail =>
            let children := collect C (t.child hs)
              (fun a m i => visit C Q (t.child hs i) a m) a meter level.orbit.points.size (Nat.le_refl _)
            match children.status with
            | .incomplete failure => ⟨children.acc, children.grows, .incomplete failure⟩
            | .complete certificates checked meter =>
              Result.finish C t a children.acc children.grows (fun _ => .branch certificates.toArray) (by
                rw [checkTree_branch C children.acc.group t hs]
                simp only [Vector.size_toArray]
                exact decide_eq_true checked) meter
termination_by t.suffix.length
decreasing_by
  all_goals
    change tail.length < t.suffix.length
    rw [hs]
    exact Nat.lt_succ_self _

end Bounded

/-- Incomplete subgroup output has only lower-bound semantics. Its own chain
is checked, but it has no certificate claiming equality to the search result. -/
inductive Outcome {G : Group n} {P : Predicate n} (C : Constraint G P) (budget : Budget) where
  | complete (solution : Solution C) (meter : Meter budget)
  | incomplete (lowerBound : Accumulator G P) (failure : Exhausted budget)

/-- Budgeted exact subgroup search. The leaf evaluator shares the same sift
counter with prefix coverage and redundant-generator checks. -/
@[expose] def solveWith (budget : Budget) {G : Group n} {P : Predicate n} (C : Constraint G P)
    (Q : Tester P budget) : Outcome C budget :=
  let r := Bounded.visit C Q (Node.root G) (Accumulator.empty G P) (Meter.empty budget)
  match r.status with
  | .incomplete failure => .incomplete r.acc failure
  | .complete certificate checked meter =>
    .complete
      { group := r.acc.group
        certificate := certificate
        checked := by
          rw [checkSearch, Bool.and_eq_true, Bool.and_eq_true]
          refine ⟨⟨(Group.isSubgroup_iff _ _).mpr r.acc.inside, ?_⟩, checked⟩
          apply decide_eq_true
          intro i
          exact r.acc.satisfies _ (.generator (Array.getElem_mem i.isLt)) }
      meter

end Hex.PermGroup.Search
