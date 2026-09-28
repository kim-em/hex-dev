/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.ProofProbe.D1.Accept
public import HexSignDetMathlib.ProofProbe.Semantics

public section

namespace Hex.SignDetMathlib.ProofProbe.D1.Semantic
open Hex Hex.SignDet Hex.SignDet.Conformance Hex.SignDetMathlib.ProofProbe

/-- Apply the proved root semantics to the accepted literal graph. The
Boolean acceptance module is a warm dependency, not recomputed in this probe. -/
theorem counts_roots : ∃ t : Replay Rat Nat,
    t.check Sturm.orderSign 7 singletonRaw.head singletonRaw.lower singletonRaw.upper
      (List.replicate (2 ^ 1) (DensePoly.C (2 : Rat))) = true ∧
    ∀ condition, t.node.system.count condition =
      (Semantics.roots.filter (fun x => Semantics.word 1 x = condition)).card := by
  obtain ⟨t, _, checked⟩ := Dag.check_replay (by
    simpa only [Inputs.check, Accept.evidence] using Accept.checked)
  refine ⟨t.val, checked, fun condition => ?_⟩
  exact t.val.count_roots (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) Sturm.orderSign Semantics.rational_sign
    7 singletonRaw.head singletonRaw.lower singletonRaw.upper
    (List.replicate (2 ^ 1) (DensePoly.C (2 : Rat))) checked condition

/-- info: 'Hex.SignDetMathlib.ProofProbe.D1.Semantic.counts_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms counts_roots

-- The diagnostic runner records this ordinary-kernel dependency inventory.
#print axioms counts_roots

end Hex.SignDetMathlib.ProofProbe.D1.Semantic
