/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseSubsequence

public section

namespace Hex.RealClosure.BaseContext.SubsequenceTests

open OrderedFn OrderedFn.Oracle

/-- Registering β over an existing α context also admits an independently
registered β context. The prefix-only producer rejects that inclusion. -/
theorem insert_before {registry : Registry} (source parent : RealPrefix.Model registry)
    (α β : ConstantKey) (different : β ≠ α)
    (sourceKeys : source.context.keys = [β]) (parentKeys : parent.context.keys = [α])
    (present : (registry β).isSome = true) (τ : ℝ)
    (contained : ∀ δ, 0 < δ → Contains ((registry β).get present δ) τ)
    (width : ∀ δ, 0 < δ → ((registry β).get present δ).width ≤ δ)
    (transcendental : letI : Field parent.context.Carrier := HexPolyMathlib.fieldOfGrind
      Real.RelativeTranscendence parent.interpretation.hom τ) :
    let child := parent.register β present τ contained width transcendental
    source.context.embedding? child.context = none ∧
      ∃ map : FieldEmbedding source.context.Carrier child.context.Carrier,
        source.context.subsequence? child.context = some map ∧
        ∀ a, child.interpretation.hom (map.value a) = source.interpretation.hom a := by
  intro child
  have childKeys : child.context.keys = [α, β] := by
    rw [RealPrefix.Model.register_keys, parentKeys]
    rfl
  constructor
  · have rejected : ¬ (source.context.embedding? child.context).isSome = true := by
      rw [RealPrefix.embedding?_isSome, sourceKeys, childKeys, List.singleton_prefix_cons_iff]
      exact different
    cases found : source.context.embedding? child.context with
    | none => rfl
    | some map => exact False.elim (rejected (by simp only [found, Option.isSome_some]))
  · apply source.subsequence_map child
    rw [sourceKeys, childKeys]
    exact List.sublist_append_right [α] [β]


end Hex.RealClosure.BaseContext.SubsequenceTests

/-- info: 'Hex.RealClosure.BaseContext.SubsequenceTests.insert_before' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.SubsequenceTests.insert_before
