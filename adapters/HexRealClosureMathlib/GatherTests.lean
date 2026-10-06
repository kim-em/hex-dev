/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SharedPresentation
public import HexRealRootsMathlib.RealClosed
public import HexOrderedFnMathlib.LiouvilleTests

public section

open scoped List

namespace Hex.RealClosure.BaseContext.GatherTests

open OrderedFn OrderedFn.Oracle
open scoped Hex.OrderedFn.Infinitesimal

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

/-- A real provider history supplies the complete gathering proof for repeated
nested rational owners over a proper real-prefix enlargement. -/
example
    (parent : SignDet.Descriptor (Tower.Context.base (BaseContext.rational registry)).Value
      Tower.Signature (Tower.Context.base (BaseContext.rational registry)).sign
      (Tower.Context.base (BaseContext.rational registry)).signature)
    (child : SignDet.Descriptor
      ((Tower.Context.base (BaseContext.rational registry)).adjoin parent).context.Value
      Tower.Signature
      ((Tower.Context.base (BaseContext.rational registry)).adjoin parent).context.sign
      ((Tower.Context.base (BaseContext.rational registry)).adjoin parent).context.signature) :
    let first := (Tower.Context.base (BaseContext.rational registry)).adjoin parent
    let second := first.context.adjoin child
    ∃ shared, Tower.Shared.gather? providerModel.context.finish
        [second.context, first.context, second.context] = some shared ∧
      ∃ model : Tower.Shared.Model shared providerModel.realization providerModel.towerModel,
        shared.targetToUnion providerModel.towerModel
          (shared.value 0 second.generator + shared.value 1 first.generator) =
          model.toUnion 0 second.generator + model.toUnion 1 first.generator ∧
        model.toUnion 0 (second.embed first.generator) = model.toUnion 1 first.generator := by
  dsimp only
  let first := (Tower.Context.base (BaseContext.rational registry)).adjoin parent
  let second := first.context.adjoin child
  have firstBase : first.context.origin.base =
      PackedContext.pack (BaseContext.rational registry) := by
    rw [Tower.Context.origin_adjoin_base]
    rfl
  have secondBase : second.context.origin.base =
      PackedContext.pack (BaseContext.rational registry) :=
    (congrArg Tower.Origin.base (Tower.Context.origin_adjoin first.context child)).trans
      ((Tower.Origin.snoc_base first.context.origin child).trans firstBase)
  have allowed : (PackedContext.pack (BaseContext.rational registry)).signature.constants <+
      providerModel.context.finish.signature.constants ∧
      (PackedContext.pack (BaseContext.rational registry)).signature.infinitesimals ≤
        providerModel.context.finish.signature.infinitesimals := by
    simp only [PackedContext.signature, BaseContext.rational,
      Context.signature_real, RealContext.keys_rational]
    exact ⟨List.nil_sublist _, Nat.zero_le _⟩
  obtain ⟨shared, produced, ⟨model⟩⟩ :=
    Tower.Shared.gather?_models providerModel.realization providerModel.towerModel
      [second.context, first.context, second.context] (by
        intro source present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        rcases present with rfl | rfl | rfl
        · rw [secondBase]
          exact allowed
        · rw [firstBase]
          exact allowed
        · rw [secondBase]
          exact allowed)
  exact ⟨shared, produced, model,
    model.targetToUnion_add (shared.value 0 second.generator) (shared.value 1 first.generator),
    model.toUnion_embed 1 0 (.selected child second rfl) rfl first.generator⟩



/-- A returned factory model supports registration of the previous shared
context followed by another actual infinitesimal enlargement. Both enlarged
models include canonical owners and coherent caches. -/
example {base : PackedContext registry} {owners : List (Tower.Context registry)}
    {shared : Tower.Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Tower.Context.ofBase base) ℝ}
    (model : Tower.Shared.Model shared following reference)
    (ambient : Ambient (Hex.RationalFn ℝ))
    (again : Ambient (Hex.RationalFn ambient.Carrier)) :
    ∃ first : Tower.SharedEnlargement shared,
      shared.enlarge? = some first ∧
      ∃ firstModel : Tower.Shared.Model first.shared following.infinitesimal
          (Tower.Model.next base reference ambient),
        firstModel.target.value first.parameter = ambient.inclusion Hex.RationalFn.X ∧
        ∃ registered, first.shared.add? shared.input.context = some registered ∧
        ∃ registeredModel : Tower.Shared.Model registered following.infinitesimal
            (Tower.Model.next base reference ambient),
          ∃ second : Tower.SharedEnlargement registered,
            registered.enlarge? = some second ∧
            ∃ secondModel : Tower.Shared.Model second.shared following.infinitesimal.infinitesimal
                (Tower.Model.next base.infinitesimal (Tower.Model.next base reference ambient) again),
              secondModel.target.value second.parameter = again.inclusion Hex.RationalFn.X ∧
              ∀ a, secondModel.target.value (second.previous.value a) =
                Ambient.coefficientHom again (registeredModel.target.value a) := by
  obtain ⟨first, firstProduced, firstModel, firstParameter, _, _⟩ := model.enlarge ambient
  have allowed : shared.input.context.origin.base.signature.constants <+
      base.infinitesimal.signature.constants ∧
      shared.input.context.origin.base.signature.infinitesimals ≤
        base.infinitesimal.signature.infinitesimals := by
    rw [shared.base_eq, PackedContext.infinitesimal_signature]
    exact ⟨List.Sublist.refl _, Nat.le_succ _⟩
  obtain ⟨registered, registeredProduced, ⟨registeredModel⟩⟩ :=
    firstModel.add? shared.input.context allowed
  obtain ⟨second, secondProduced, secondModel, secondParameter, previous, aligned⟩ :=
    registeredModel.enlarge again
  refine ⟨first, firstProduced, firstModel, firstParameter, registered, registeredProduced,
    registeredModel, second, secondProduced, secondModel, secondParameter, ?_⟩
  intro a
  rw [← aligned, previous.value, Tower.Model.liftInfinitesimal_value]

end Hex.RealClosure.BaseContext.GatherTests
