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

/-- The canonical registration and union theorem apply to a value combining
a selected root and values from both infinitesimal stages. The gathering and
registration successes are obtained from the actual provider factory. -/
example (parent : Root initial) (child : Root parent.context)
    (epsilon : (Context.ofBase (base.extend 1)).Value)
    (delta : (Context.ofBase (base.extend 2)).Value) :
    let owners := [parent.context, Context.ofBase (base.extend 1), Context.ofBase (base.extend 2)]
    let following := provider.staged 2
    let reference := following.reference.model
    ∃ shared : Shared (base.extend 2) owners,
      Shared.gather? (base.extend 2) owners = some shared ∧
      ∃ model : Shared.Model shared following reference,
        ∃ packet : Registration shared child.context,
          shared.register? child.context = some packet ∧
          ∃ returned : Shared.Model packet.shared following reference,
            packet.shared.targetToUnion reference
                (packet.previous.value
                  ((shared.value 0 parent.value + shared.value 1 epsilon) * shared.value 2 delta)) =
              shared.targetToUnion reference
                ((shared.value 0 parent.value + shared.value 1 epsilon) * shared.value 2 delta) := by
  dsimp only
  let owners := [parent.context, Context.ofBase (base.extend 1), Context.ofBase (base.extend 2)]
  let following := provider.staged 2
  let reference := following.reference.model
  have baseCompatible (n : Nat) (depth : n ≤ 2) :
      (base.extend n).signature.constants <+: (base.extend 2).signature.constants ∧
      (base.extend n).signature.infinitesimals ≤ (base.extend 2).signature.infinitesimals := by
    simp only [BaseContext.PackedContext.extend_signature]
    exact ⟨List.prefix_refl _, Nat.add_le_add_left depth _⟩
  have parentBase : parent.context.origin.base = base :=
    parent.origin_base.trans (Context.ofBase_origin_base base)
  have childBase : child.context.origin.base = base := child.origin_base.trans parentBase
  have initialCompatible : base.signature.constants <+: (base.extend 2).signature.constants ∧
      base.signature.infinitesimals ≤ (base.extend 2).signature.infinitesimals := by
    simpa only [BaseContext.PackedContext.extend] using baseCompatible 0 (by decide)
  obtain ⟨shared, produced, ⟨model⟩⟩ := Shared.gather?_models following reference owners (by
    intro source present
    simp only [owners, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl
    · rw [parentBase]
      exact initialCompatible
    · rw [Context.ofBase_origin_base]
      exact baseCompatible 1 (by decide)
    · rw [Context.ofBase_origin_base]
      exact baseCompatible 2 (by decide))
  obtain ⟨packet, registered, returned, preserved, union⟩ :=
    model.register?_union child.context (by rw [childBase]; exact initialCompatible)
  exact ⟨shared, produced, model, packet, registered, returned, union _⟩

end Hex.RealClosure.Tower.SharedPresentationTests

namespace Hex.RealClosure.Tower.SharedPresentationTests
open scoped Hex.OrderedFn.Infinitesimal

/-- Enlarge, register a new owner, then enlarge again. The first generated
infinitesimal survives both actual packets in the final canonical model. -/
theorem retain_parameter {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
    {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    {owners : List (Context registry)} {shared : Shared base owners}
    {following : base.Realization} {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference)
    (ambient : Ambient (Hex.RationalFn R)) (source : Context registry)
    (compatible : source.origin.base.signature.constants <+: base.infinitesimal.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.infinitesimal.signature.infinitesimals)
    (nextAmbient : Ambient (Hex.RationalFn ambient.Carrier)) :
    ∃ first : SharedEnlargement shared, shared.enlarge? = some first ∧
      ∃ packet : Registration first.shared source, first.shared.register? source = some packet ∧
        ∃ second : SharedEnlargement packet.shared, packet.shared.enlarge? = some second ∧
          ∃ returned : Shared.Model second.shared following.infinitesimal.infinitesimal
              (Tower.Model.next base.infinitesimal (Tower.Model.next base reference ambient) nextAmbient),
            returned.target.value
                (second.previous.value (packet.previous.value first.parameter)) =
              Ambient.coefficientHom nextAmbient (ambient.inclusion Hex.RationalFn.X) ∧
            returned.target.value second.parameter = nextAmbient.inclusion Hex.RationalFn.X := by
  obtain ⟨first, enlarged, firstModel, parameter, _, _⟩ := model.enlarge ambient
  obtain ⟨packet, registered, registeredModel, preserved⟩ :=
    firstModel.register? source compatible
  obtain ⟨second, enlargedAgain, returned, nextParameter, previous, aligned⟩ :=
    registeredModel.enlarge nextAmbient
  refine ⟨first, enlarged, packet, registered, second, enlargedAgain, returned, ?_, nextParameter⟩
  rw [← aligned, previous.value, Tower.Model.liftInfinitesimal_value, preserved, parameter]

end Hex.RealClosure.Tower.SharedPresentationTests

/-- info: 'Hex.RealClosure.Tower.SharedPresentationTests.retain_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.SharedPresentationTests.retain_parameter
