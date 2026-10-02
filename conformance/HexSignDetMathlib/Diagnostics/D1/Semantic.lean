/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.Diagnostics.D1.Accept
public import HexSignDetMathlib.Diagnostics.Semantics

public section

namespace Hex.SignDetMathlib.Diagnostics.D1.Semantic
open Hex Hex.SignDet Hex.SignDet.Conformance Hex.SignDetMathlib.Diagnostics

/-- Apply the proved root semantics to the accepted literal graph. The
Boolean acceptance module is a warm dependency, not recomputed in this probe. -/
theorem counts_roots : ∃ t,
    Dag.replay? Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper
      (List.replicate (2 ^ 1) (DensePoly.C (2 : Rat))) Accept.evidence = some t ∧
    ∀ condition, t.val.node.system.count condition =
      (Semantics.roots.filter (fun x => Semantics.signCondition 1 x = condition)).card := by
  obtain ⟨t, replayed, checked⟩ := Dag.check_replay (by
    simpa only [Inputs.check, Accept.evidence] using Accept.checked)
  refine ⟨t, replayed, fun condition => ?_⟩
  exact t.val.count_roots (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) Sturm.orderSign Semantics.rational_sign
    7 singletonRaw.head singletonRaw.lower singletonRaw.upper
    (List.replicate (2 ^ 1) (DensePoly.C (2 : Rat))) checked condition

/-- info: 'Hex.SignDetMathlib.Diagnostics.D1.Semantic.counts_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms counts_roots


end Hex.SignDetMathlib.Diagnostics.D1.Semantic
