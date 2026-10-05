/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseSubsequenceTests
public import HexRealClosureMathlib.CacheGather
public import HexRealClosure.SharedPresentation

public section

namespace Hex.RealClosure.BaseContext.SubsequenceTests

open OrderedFn OrderedFn.Oracle

/-- The shared factory rebuilds a complete algebraic suffix over `[β]` in the
actual registered `[α, β]` target, retaining its earlier infinitesimals. Only the
target's provider realization is passed to model derivation. -/
theorem gather_insert_before {registry : Registry} (source parent : RealPrefix.Model registry)
    (α β : ConstantKey) (sourceKeys : source.context.keys = [β])
    (parentKeys : parent.context.keys = [α])
    (present : (registry β).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry β).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry β).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ)
    (n m : Nat) (depth : n ≤ m)
    (suffix : Tower.Suffix (Tower.Context.ofBase (source.context.finish.extend n))) :
    let child := parent.register β present τ contained width transcendental
    let base := child.context.finish.extend m
    let following := child.staged m
    let reference := following.reference.model
    ∃ shared, Tower.Shared.gather? base [suffix.context] = some shared ∧
      Nonempty (Tower.Shared.Model shared following reference) := by
  intro child base following reference
  apply Tower.Shared.gather?_models following reference [suffix.context]
  intro owner member
  have same : owner = suffix.context := by simpa only [List.mem_singleton] using member
  subst owner
  rw [Tower.Suffix.base_eq, Tower.Context.ofBase_origin_base]
  simp only [base, PackedContext.extend_signature, RealPrefix.finish_signature]
  constructor
  · rw [sourceKeys, RealPrefix.Model.register_keys, parentKeys]
    exact List.sublist_append_right [α] [β]
  · simpa only [Nat.zero_add] using depth


end Hex.RealClosure.BaseContext.SubsequenceTests

/-- info: 'Hex.RealClosure.BaseContext.SubsequenceTests.gather_insert_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.SubsequenceTests.gather_insert_before
