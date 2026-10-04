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
              (secondModel.toUnion 1 child.value : ℝ) := by
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
  have aligned := Option.some.inj ((firstModel.canonicalOwners 0).symm.trans
    (secondModel.canonicalOwners 1))
  exact (firstModel.toUnion_value 0 child.value).trans
    ((congrArg (fun m : Tower.Model child.context ℝ => m.value child.value) aligned).trans
      (secondModel.toUnion_value 1 child.value).symm)

end Hex.RealClosure.Tower.SharedPresentationTests
