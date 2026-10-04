/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ContextModel
public import HexRealClosureMathlib.CacheGather
public import HexOrderedFnMathlib.LiouvilleTests

public section

namespace Hex.RealClosure.BaseContext.FactoryTests

open OrderedFn OrderedFn.Oracle

local instance (priority := 2000) : Lean.Grind.Field Rat := Lean.Grind.instFieldRat

private def key (version : Nat) : ConstantKey := ⟨"liouville", version⟩
private def registry : Registry := fun k =>
  if k.name = "liouville" then some OrderedFn.LiouvilleTests.provider else none
private abbrev prefixContext := RealContext.rational registry

private theorem present (version : Nat) : (registry (key version)).isSome = true := by
  simp [registry, key]

private noncomputable abbrev rationalModel := RealPrefix.Model.rational registry

private theorem providerTranscendence :
    letI : Field rationalModel.context.Carrier := HexPolyMathlib.fieldOfGrind
    Real.RelativeTranscendence rationalModel.interpretation.hom (liouvilleNumber 2) := by
  let : Field Rat := HexPolyMathlib.fieldOfGrind
  change Real.RelativeTranscendence (Rat.castHom ℝ) (liouvilleNumber 2)
  exact OrderedFn.LiouvilleTests.transcendence

private theorem providerContained (δ : Rat) (_positive : 0 < δ) :
    Contains ((registry (key 1)).get (present 1) δ) (liouvilleNumber 2) :=
  OrderedFn.LiouvilleTests.provider_contains δ

private theorem providerWidth (δ : Rat) (positive : 0 < δ) :
    ((registry (key 1)).get (present 1) δ).width ≤ δ :=
  OrderedFn.LiouvilleTests.provider_width δ positive

/-- This constructs the full native prefix and its coherent predecessor model
using only the actual Liouville provider's analytic premises. -/
private noncomputable def providerModel := rationalModel.register (key 1) (present 1)
  (liouvilleNumber 2) providerContained providerWidth providerTranscendence

noncomputable example : (providerModel.context.finish.extend 2).Realization := providerModel.staged 2

example : ((providerModel.staged 2).restrict?
    (rationalModel.context.finish.extend 1)).isSome = true := by
  rw [PackedContext.Realization.restrict?_isSome]
  simp only [PackedContext.extend_signature, RealPrefix.finish_signature]
  constructor
  · have keys : rationalModel.context.keys = [] := by
      simp only [rationalModel, RealPrefix.Model.rational, RealPrefix.Model.context,
        RealPrefix.keys, RealContext.keys, RealContext.ofChain_chain, RealChain.keys]
    rw [keys]
    exact List.nil_prefix
  · decide

private theorem originBase (base : PackedContext registry) :
    (Tower.Context.ofBase base).origin.base = base := by
  cases base with
  | pack base =>
    simp only [Tower.Context.ofBase, Tower.Context.origin_base, Tower.Origin.base]
    rfl

/-- Canonical owner lookup uses the actual Liouville provider history across a
proper real prefix and differing infinitesimal depths. The child factory
preserves the generated parent's values without an agreement premise. -/
example {R : Type} [Field R] [LinearOrder R] [DecidableEq R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    (reference : Tower.Model (Tower.Context.ofBase (providerModel.context.finish.extend 2)) R)
    (descriptor : SignDet.Descriptor
      (Tower.Context.ofBase (rationalModel.context.finish.extend 1)).Value Tower.Signature
      (Tower.Context.ofBase (rationalModel.context.finish.extend 1)).sign
      (Tower.Context.ofBase (rationalModel.context.finish.extend 1)).signature) :
    let source := Tower.Context.ofBase (rationalModel.context.finish.extend 1)
    ∃ original : Tower.Model source R,
      source.model? (providerModel.staged 2) reference = some original ∧
      ∃ child : Tower.Model (source.adjoin descriptor).context R,
        (source.adjoin descriptor).context.model? (providerModel.staged 2) reference = some child ∧
        ∀ a, child.value ((source.adjoin descriptor).embed a) = original.value a := by
  let source := Tower.Context.ofBase (rationalModel.context.finish.extend 1)
  have compatible : source.origin.base.signature.constants <+:
      (providerModel.context.finish.extend 2).signature.constants ∧
      source.origin.base.signature.infinitesimals ≤
        (providerModel.context.finish.extend 2).signature.infinitesimals := by
    rw [originBase]
    simp only [PackedContext.extend_signature, RealPrefix.finish_signature]
    have keys : rationalModel.context.keys = [] := by
      simp only [rationalModel, RealPrefix.Model.rational, RealPrefix.Model.context,
        RealPrefix.keys, RealContext.keys, RealContext.ofChain_chain, RealChain.keys]
    rw [keys]
    exact ⟨List.nil_prefix, by decide⟩
  have success := (source.model?_isSome (providerModel.staged 2) reference).mpr compatible
  obtain ⟨original, produced⟩ := Option.isSome_iff_exists.mp success
  have childProduced : (source.adjoin descriptor).context.model? (providerModel.staged 2)
      reference = some (original.adjoin descriptor) := by
    rw [Tower.Context.model?_adjoin, produced, Option.map_some]
  exact ⟨original, produced, original.adjoin descriptor, childProduced,
    source.model?_embed (providerModel.staged 2) reference descriptor original
      (original.adjoin descriptor) produced childProduced⟩

/-- The factory also follows the stored nonempty real-provider history when
only the infinitesimal depth grows. Every base value agrees with the reference. -/
example {R : Type} [Field R] [LinearOrder R] [DecidableEq R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    (reference : Tower.Model (Tower.Context.ofBase (providerModel.context.finish.extend 2)) R) :
    let source := providerModel.context.finish.extend 1
    ∃ inclusion : Tower.BaseInclusion source (providerModel.context.finish.extend 2),
      Tower.BaseInclusion.make? source (providerModel.context.finish.extend 2) = some inclusion ∧
      ∃ original : Tower.Model (Tower.Context.ofBase source) R,
        (Tower.Context.ofBase source).model? (providerModel.staged 2) reference = some original ∧
        ∀ a, reference.value (inclusion.value a) = original.value a := by
  let source := providerModel.context.finish.extend 1
  have success := (Tower.BaseInclusion.make?_isSome source
    (providerModel.context.finish.extend 2)).mpr (by
      simp only [source, PackedContext.extend_signature]
      exact ⟨List.prefix_refl _, by omega⟩)
  obtain ⟨inclusion, produced⟩ := Option.isSome_iff_exists.mp success
  let original := (Tower.BaseInclusion.Model.derive (providerModel.staged 2)
    inclusion reference).source
  have ownerProduced := Tower.Context.model?_baseMap source (providerModel.staged 2)
    reference inclusion produced
  exact ⟨inclusion, produced, original, ownerProduced,
    Tower.Context.model?_value source (providerModel.staged 2) reference inclusion produced
      original ownerProduced⟩

/-- The actual packed reference is usable by the canonical owner consumer,
without a supplied real-closed field or reference-model hypothesis. -/
example :
    ((Tower.Context.ofBase (rationalModel.context.finish.extend 1)).model?
      (providerModel.staged 2) (providerModel.staged 2).reference.model).isSome = true := by
  rw [Tower.Context.model?_isSome, originBase]
  simp only [PackedContext.extend_signature, RealPrefix.finish_signature]
  have keys : rationalModel.context.keys = [] := by
    simp only [rationalModel, RealPrefix.Model.rational, RealPrefix.Model.context,
      RealPrefix.keys, RealContext.keys, RealContext.ofChain_chain, RealChain.keys]
  rw [keys]
  exact ⟨List.nil_prefix, by decide⟩

/-- An accepted mixed-depth gathering needs no repeated compatibility proof.
The canonical factory identifies duplicated cached owners in one target. -/
example {R : Type} [Field R] [LinearOrder R] [DecidableEq R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    (reference : Tower.Model (Tower.Context.ofBase (providerModel.context.finish.extend 2)) R)
    (descriptor : SignDet.Descriptor
      (Tower.Context.ofBase (rationalModel.context.finish.extend 1)).Value Tower.Signature
      (Tower.Context.ofBase (rationalModel.context.finish.extend 1)).sign
      (Tower.Context.ofBase (rationalModel.context.finish.extend 1)).signature)
    (shared : Tower.Shared (providerModel.context.finish.extend 2)
      [(Tower.Context.ofBase (rationalModel.context.finish.extend 1)).adjoin descriptor |>.context,
       Tower.Context.ofBase (rationalModel.context.finish.extend 1),
       (Tower.Context.ofBase (rationalModel.context.finish.extend 1)).adjoin descriptor |>.context])
    (produced : Tower.Shared.gather? (providerModel.context.finish.extend 2)
      [(Tower.Context.ofBase (rationalModel.context.finish.extend 1)).adjoin descriptor |>.context,
       Tower.Context.ofBase (rationalModel.context.finish.extend 1),
       (Tower.Context.ofBase (rationalModel.context.finish.extend 1)).adjoin descriptor |>.context] =
      some shared) :
    ∃ model : Tower.Shared.Model shared (providerModel.staged 2) reference,
      ∀ a : ((Tower.Context.ofBase (rationalModel.context.finish.extend 1)).adjoin
          descriptor).context.Value,
        model.target.value (shared.value 0 a) = model.target.value (shared.value 2 a) := by
  let model := Tower.Shared.Model.ofGather (providerModel.staged 2) reference _ shared produced
  have duplicate := Option.some.inj ((model.canonicalOwners 0).symm.trans (model.canonicalOwners 2))
  refine ⟨model, fun a => ?_⟩
  exact (model.value 0 a).trans ((congrArg (fun original => original.value a) duplicate).trans
    (model.value 2 a).symm)

end Hex.RealClosure.BaseContext.FactoryTests
