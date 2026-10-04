/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SharedPresentation
public import HexRealRootsMathlib.RealClosed

public section

namespace Hex.RealClosure.Tower.SharedPresentationTests

private def registry : BaseContext.Registry := fun _ => none
private noncomputable def provider := BaseContext.RealPrefix.Model.rational registry
private noncomputable abbrev base := provider.context.finish
private noncomputable abbrev initial := Context.ofBase base

/-- Parent-first and child-first gathering of actual nested roots give the
same union value for the child's stored generator. Both native collections
are produced, and their models come from the rational base factory. -/
example (parent : Root initial) (child : Root parent.context) :
    ∃ first : Shared base [child.context, parent.context],
      Shared.gather? base [child.context, parent.context] = some first ∧
      ∃ second : Shared base [parent.context, child.context],
        Shared.gather? base [parent.context, child.context] = some second ∧
        ∃ firstModel : Shared.Model first provider.realization provider.towerModel,
          ∃ secondModel : Shared.Model second provider.realization provider.towerModel,
            (firstModel.toUnion 0 child.value : ℝ) =
              (secondModel.toUnion 1 child.value : ℝ) ∧
            firstModel.toUnion 1 parent.value =
              firstModel.toUnion 0 (child.embed parent.value) := by
  have parentBase : parent.context.origin.base = base :=
    parent.origin_base.trans (Context.ofBase_origin_base base)
  have childBase : child.context.origin.base = base := child.origin_base.trans parentBase
  have compatible (source : Context registry) (same : source.origin.base = base) :
      source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
    rw [same]
    exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  obtain ⟨first, firstProduced, ⟨firstModel⟩⟩ :=
    Shared.gather?_models provider.realization provider.towerModel [child.context, parent.context]
      (by
        intro source present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        rcases present with rfl | rfl
        · exact compatible _ childBase
        · exact compatible _ parentBase)
  obtain ⟨second, secondProduced, ⟨secondModel⟩⟩ :=
    Shared.gather?_models provider.realization provider.towerModel [parent.context, child.context]
      (by
        intro source present
        simp only [List.mem_cons, List.not_mem_nil, or_false] at present
        rcases present with rfl | rfl
        · exact compatible _ parentBase
        · exact compatible _ childBase)
  refine ⟨first, firstProduced, second, secondProduced, firstModel, secondModel, ?_⟩
  constructor
  · exact congrArg Subtype.val
      (firstModel.toUnion_coherent secondModel 0 1 rfl child.value)
  · exact (firstModel.toUnion_embed 1 0 child rfl parent.value).symm

/-- Registering an actual later root retains all previously computed target
values, including combinations absent from the original owner list. Both
canonical models and the checked transport come from the produced factories. -/
example (parent : Root initial) (child : Root parent.context) :
    ∃ shared : Shared base [parent.context],
      Shared.gather? base [parent.context] = some shared ∧
      ∃ model : Shared.Model shared provider.realization provider.towerModel,
        ∃ packet : Registration shared child.context,
          shared.register? child.context = some packet ∧
            ∃ returned : Shared.Model packet.shared provider.realization provider.towerModel,
              (∀ a, returned.target.value (packet.previous.value a) = model.target.value a) ∧
              ∀ a, packet.shared.targetToUnion provider.towerModel
                  (packet.previous.value (a + a⁻¹)) =
                shared.targetToUnion provider.towerModel (a + a⁻¹) := by
  have parentBase : parent.context.origin.base = base :=
    parent.origin_base.trans (Context.ofBase_origin_base base)
  have childBase : child.context.origin.base = base := child.origin_base.trans parentBase
  have allowed (source : Context registry) (same : source.origin.base = base) :
      source.origin.base.signature.constants <+: base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
    rw [same]
    exact ⟨List.prefix_refl _, Nat.le_refl _⟩
  obtain ⟨shared, produced, ⟨model⟩⟩ :=
    Shared.gather?_models provider.realization provider.towerModel [parent.context] (by
      intro source present
      have equal : source = parent.context := by simpa using present
      subst source
      exact allowed _ parentBase)
  obtain ⟨packet, registered, returned, preserved, union⟩ :=
    model.register?_union child.context (allowed _ childBase)
  exact ⟨shared, produced, model, packet, registered, returned, preserved,
    fun a => union (a + a⁻¹)⟩

end Hex.RealClosure.Tower.SharedPresentationTests
