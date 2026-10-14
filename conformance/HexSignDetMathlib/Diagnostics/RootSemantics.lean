/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexSignDetMathlib.RootProducer
public import HexSignDetMathlib.SelectedRoot
public import HexSignDetMathlib.SelectedProducer
public import HexSignDetMathlib.TableProducer
public import HexSignDetMathlib.CompletionProducer
public import HexSignDetMathlib.ThomRoots
public import HexSignDetMathlib.ThomReencoding
public import HexSignDetMathlib.ComparisonProducer
public import HexSignDetMathlib.Naturality
public import HexSignDetMathlib.Embedding
public import HexSignDet.Conformance
public import HexRealRootsMathlib.RealClosed


public section

/-! Actual root support from accepted BKR replay. -/
namespace Hex.SignDetMathlib.RootSemantics

open Hex Hex.SignDet Hex.SignDet.Conformance HexPolyMathlib.Interpret HexRealRootsMathlib

private theorem rational_sign (x : Rat) :
    Sturm.orderSign x = (SignType.sign (x : ℝ) : Int) := by
  rw [HexSturmMathlib.orderSign_eq]
  congr 1
  exact (StrictMono.sign_comp (f := Rat.castHom ℝ) Rat.cast_strictMono x).symm

/-- The literal two-query replay retains exactly its real sign conditions.
The acceptance proof is independent of the root-sum theorem. -/
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

/-- Finite extraction of the existing literal full replay uses its checked
row directly, without constructing a prepared domain or running a producer. -/
theorem literal_extraction :
    let raw : RawDescriptor Rat Nat :=
      ⟨7, singletonRaw.head, singletonRaw.lower, singletonRaw.upper, [], []⟩
    ∃ out, Descriptor.rootsFrom Sturm.orderSign 7 raw fullReplay
      (fullReplay.table full_kernel).rows.toList = .ok out ∧ out.length = 1 := by
  dsimp only
  let raw : RawDescriptor Rat Nat :=
    ⟨7, singletonRaw.head, singletonRaw.lower, singletonRaw.upper, [], []⟩
  have hp : 0 < raw.head.natDegree := by decide +kernel
  have hctx : raw.context = 7 := rfl
  have hc : fullReplay.check Sturm.orderSign 7 raw.head raw.lower raw.upper
      (raw.full []).queries = true := full_kernel
  have rows : (fullReplay.table hc).rows.toList = [([1, 1], 1)] := by
    rw [Replay.table_rows]
    decide +kernel
  have member : ([1, 1], 1) ∈ (fullReplay.table hc).rows.toList := by
    rw [rows]
    simp
  let d := Descriptor.ofFullRow raw fullReplay hp hctx hc ([1, 1], 1) member rfl
  refine ⟨[d], ?_, rfl⟩
  change Descriptor.rootsFrom Sturm.orderSign 7 raw fullReplay
    (fullReplay.table hc).rows.toList = .ok [d]
  rw [← Descriptor.rootsFromTable_eq raw fullReplay hp hctx hc
    (fullReplay.table hc).rows.toList (fun _ h => h)]
  simp only [rows]
  rw [Descriptor.rootsFromTable_cons raw fullReplay hp hctx hc ([1, 1], 1) [] _ rfl]
  rw [Descriptor.rootsFromTable_nil]
  simp only [Except.bind, Thom.insert_nil]
  rfl

/-- The supplied literal replay has one root in its requested real interval,
with complete coverage, no duplicate values and strict order. This consumes the supplied-replay exports, without native
root-production facts. -/
theorem literal_roots :
    ∃ roots : List ℝ, roots.length = 1 ∧
      (∀ x, x ∈ Tarski.rootsIn
        (interpret (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero) singletonRaw.head)
        (singletonRaw.lower.map fun r : Rat => (r : ℝ))
        (singletonRaw.upper.map fun r : Rat => (r : ℝ)) ↔ x ∈ roots) ∧
        roots.Nodup ∧ roots.Pairwise (· < ·) := by
  obtain ⟨out, extracted, length⟩ := literal_extraction
  have coverage := Descriptor.rootsFrom_coverage
    (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    fullReplay full_kernel extracted
  have ordered := Descriptor.rootsFrom_ordered
    (fun r : Rat => (r : ℝ)) (fun _ => Rat.cast_eq_zero)
    (by simp) (fun _ _ => Rat.cast_add _ _) (fun _ _ => Rat.cast_sub _ _)
    (fun _ _ => Rat.cast_mul _ _) (fun _ => by simp) rational_sign
    ⟨7, singletonRaw.head, singletonRaw.lower, singletonRaw.upper, [], []⟩
    fullReplay extracted
  exact ⟨_, by simpa only [List.length_map] using length, coverage.1, coverage.2, ordered⟩

/-- info: 'Hex.SignDetMathlib.RootSemantics.literal_extraction' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms literal_extraction

/-- info: 'Hex.SignDetMathlib.RootSemantics.literal_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms literal_roots

/-- info: 'Hex.SignDetMathlib.RootSemantics.literal_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms literal_support

/-- info: 'Hex.SignDet.Conformance.full_kernel' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Conformance.full_kernel

/-- info: 'Hex.SignDet.Replay.check_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Replay.check_counts

/-- info: 'Hex.SignDet.buildPrepared_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.buildPrepared_roots

/-- info: 'Hex.SignDet.Descriptor.build_noError' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.build_noError

/-- info: 'Hex.SignDet.Descriptor.build_of_unique_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.build_of_unique_root

/-- info: 'Hex.SignDet.Descriptor.build_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.build_success_iff

/-- info: 'Hex.SignDet.Descriptor.validate_success_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.validate_success_iff

/-- info: 'Hex.SignDet.Descriptor.build_valid_cases' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.build_valid_cases

/-- info: 'Hex.SignDet.Descriptor.build_success_formal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.build_success_formal

/-- info: 'Hex.SignDet.Descriptor.validate_success_formal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.validate_success_formal

/-- info: 'Hex.SignDet.Descriptor.existsUnique_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.existsUnique_root

/-- info: 'Hex.SignDet.Descriptor.root_derivatives' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.root_derivatives

/-- info: 'Hex.SignDet.Completion.root_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Completion.root_eq_source

/-- info: 'Hex.SignDet.Completion.signs_at_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Completion.signs_at_source

/-- info: 'Hex.SignDet.SelectedSigns.value_at_root' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.SelectedSigns.value_at_root

/-- info: 'Hex.SignDet.Descriptor.buildSigns_ofTable' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildSigns_ofTable

/-- info: 'Hex.SignDet.Descriptor.signs_rows' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.signs_rows

/-- info: 'Hex.SignDet.Descriptor.buildSigns_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildSigns_success

/-- info: 'Hex.SignDet.Descriptor.buildSigns_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildSigns_roots

/-- info: 'Hex.SignDet.Descriptor.signAt_ofBuild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.signAt_ofBuild

/-- info: 'Hex.SignDet.Descriptor.signAt_ternary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.signAt_ternary

/-- info: 'Hex.SignDet.Descriptor.signAt_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.signAt_success

/-- info: 'Hex.SignDet.Descriptor.signAt_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.signAt_correct

/-- info: 'Hex.SignDet.Reencoding.target_constraints' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Reencoding.target_constraints

/-- info: 'Hex.SignDet.Reencoding.root_eq_source' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Reencoding.root_eq_source

/-- info: 'Hex.SignDet.Comparison.eq_iff_root_eq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Comparison.eq_iff_root_eq

/-- info: 'Hex.SignDet.moment_entry' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.moment_entry

/-- info: 'Hex.SignDet.determine_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.determine_correct

/-- info: 'Hex.SignDet.determinePrepared_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.determinePrepared_success

/-- info: 'Hex.SignDet.Descriptor.complete_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.complete_correct

/-- info: 'Hex.SignDet.Descriptor.compare_correct' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_correct

/-- info: 'Hex.SignDet.Descriptor.buildRoots_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_roots

/-- info: 'Hex.SignDet.Descriptor.buildReencoding_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildReencoding_isSome

/-- info: 'Hex.SignDet.Descriptor.convert_signAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.convert_signAt

/-- info: 'Hex.SignDet.Descriptor.convert_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.convert_compare

/-- info: 'Hex.SignDet.determine_convert_counts' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.determine_convert_counts

/-- info: 'Hex.SignDet.determine_convert_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.determine_convert_isSome

/-- info: 'Hex.SignDet.Descriptor.buildRoots_convert_roots' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_convert_roots

/-- info: 'Hex.SignDet.Descriptor.buildRoots_convert_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_convert_isSome

/-- info: 'Hex.SignDet.Descriptor.buildRoots_isSome' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_isSome

/-- info: 'Hex.SignDet.Descriptor.buildRoots_domain' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.buildRoots_domain

/-- info: 'Hex.SignDet.Descriptor.compare_lt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_lt_iff

/-- info: 'Hex.SignDet.Descriptor.compare_eq_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_eq_iff

/-- info: 'Hex.SignDet.Descriptor.compare_gt_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.compare_gt_iff

/-- info: 'Hex.SignDet.Descriptor.root_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.root_comp

/-- info: 'Hex.SignDet.Descriptor.rootsFrom_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.rootsFrom_coverage

/-- info: 'Hex.SignDet.Descriptor.rootsFrom_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.SignDet.Descriptor.rootsFrom_ordered

end Hex.SignDetMathlib.RootSemantics
