/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RootProducer
public import HexSignDetMathlib.SelectedRoot
public import HexSignDet.Conformance
public import HexRealRootsMathlib.RealClosed

public section

/-! Actual root support from accepted BKR replay.
Computational conformance owner: `HexSignDet`. -/
namespace Hex.SignDetMathlib.RootSemantics

open Hex Hex.SignDet Hex.SignDet.Conformance HexPolyMathlib.Interpret HexRealRootsMathlib

private theorem rational_sign (x : Rat) :
    Sturm.orderSign x = (SignType.sign (x : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono x).symm

/-- The literal two-query replay retains exactly its real sign conditions.
The acceptance proof is independent of the semantic admission. -/
theorem literal_support (s : List Int) :
    (∃ x ∈ Tarski.rootsIn
      (interpret (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero) singletonRaw.head)
      (singletonRaw.lower.map fun r : Rat => (r : ℝ))
      (singletonRaw.upper.map fun r : Rat => (r : ℝ)),
      signsAt (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
        (singletonRaw.full []).queries x = s) ↔ s = [1, 1] := by
  have h := fullReplay.check_support (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) Sturm.orderSign rational_sign
    7 singletonRaw.head singletonRaw.lower singletonRaw.upper (singletonRaw.full []).queries
    full_kernel s
  have hs : fullReplay.node.system.support = [[1, 1]] := by decide +kernel
  simpa only [hs, List.mem_singleton] using h.symm

/-- info: 'Hex.SignDetMathlib.RootSemantics.literal_support' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms literal_support

/-- info: 'Hex.SignDet.Conformance.full_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Conformance.full_kernel

/-- info: 'Hex.SignDet.Replay.check_counts' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Replay.check_counts

/-- info: 'Hex.SignDet.buildPrepared_roots' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.buildPrepared_roots

/-- info: 'Hex.SignDet.Descriptor.build_noError' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.build_noError

/-- info: 'Hex.SignDet.Descriptor.build_of_unique_root' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.build_of_unique_root

/-- info: 'Hex.SignDet.Descriptor.build_success_iff' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.build_success_iff

/-- info: 'Hex.SignDet.Descriptor.build_valid_cases' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.build_valid_cases

/-- info: 'Hex.SignDet.Descriptor.build_success_formal' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.build_success_formal

/-- info: 'Hex.SignDet.Descriptor.existsUnique_root' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.existsUnique_root

/-- info: 'Hex.SignDet.Descriptor.root_derivatives' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Descriptor.root_derivatives

/-- info: 'Hex.SignDet.Completion.root_eq_source' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Completion.root_eq_source

/-- info: 'Hex.SignDet.Completion.signs_at_source' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Completion.signs_at_source

/-- info: 'Hex.SignDet.SelectedSigns.value_at_root' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.SelectedSigns.value_at_root

/-- info: 'Hex.SignDet.Reencoding.target_constraints' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Reencoding.target_constraints

/-- info: 'Hex.SignDet.Reencoding.root_eq_source' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Reencoding.root_eq_source

/-- info: 'Hex.SignDet.Comparison.eq_iff_root_eq' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.Comparison.eq_iff_root_eq

/-- info: 'Hex.SignDet.moment_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.SignDet.moment_entry

end Hex.SignDetMathlib.RootSemantics
