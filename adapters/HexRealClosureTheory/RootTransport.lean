/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.RootTransport
public import HexRealClosureTheory.TowerRoots

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Both actual inclusions into the moved root's child preserve their complete
source models, and the converted root selects the same ambient value. -/
structure Moved.Model {conversion : Conversion parent} {source : Root parent}
    (moved : Moved conversion source) (original : Model parent K)
    (model : Conversion.Model conversion original) where
  input : Conversion.Model moved.input model.target
  transported : Conversion.Model moved.transported (source.model original)
  input_target : HEq input.target (moved.root.model model.target)
  transported_target : HEq transported.target (moved.root.model model.target)
  root : moved.root.denote model.target = source.denote original

/-- A coefficient point uses identity for the new coefficient inclusion and
the supplied conversion for its complete old context. -/
noncomputable def Moved.Model.point {conversion : Conversion parent}
    {original : Tower.Model parent K} (model : Conversion.Model conversion original)
    (a : parent.Value) : Moved.Model (Moved.point conversion a) original model where
  input := Conversion.Model.identity model.target
  transported := model
  input_target := Conversion.Model.identity_target model.target
  transported_target := HEq.rfl
  root := model.value a

/-- The actual checked descriptor fixes both the converted child model and
the polynomial-packing interpretation of every value in the old child. -/
noncomputable def Moved.Model.selected {conversion : Conversion parent}
    {original : Tower.Model parent K} (model : Conversion.Model conversion original)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (accepted : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (parent.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    Moved.Model (Moved.selected conversion descriptor converted accepted) original model := by
  let binding := SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp accepted)
  exact
    { input := Conversion.Model.includeRoot model.target converted _ rfl
      transported := model.adjoinWith descriptor converted binding
        (conversion.adjoinCached descriptor converted accepted _ rfl)
        (conversion.adjoinCached_spec descriptor converted accepted _ rfl).1
        (conversion.adjoinCached_spec descriptor converted accepted _ rfl).2
      input_target := Conversion.Model.includeRoot_target model.target converted _ rfl
      transported_target := model.adjoinWith_target descriptor converted binding _
        (conversion.adjoinCached_spec descriptor converted accepted _ rfl).1
        (conversion.adjoinCached_spec descriptor converted accepted _ rfl).2
      root := by
        change (model.target.adjoin converted).value
          (conversion.context.adjoin converted).generator =
          (original.adjoin descriptor).value (parent.adjoin descriptor).generator
        rw [model.target.adjoin_generator, original.adjoin_generator]
        exact model.root descriptor converted binding }

/-- Revalidation succeeds for each actual native root and returns semantic
preservation of both entire source contexts. -/
theorem Root.move?_success {conversion : Conversion parent} {original : Model parent K}
    (model : Conversion.Model conversion original) (source : Root parent) :
    ∃ moved, source.move? conversion = some moved ∧ Nonempty (Moved.Model moved original model) := by
  cases source with
  | point a =>
    exact ⟨Moved.point conversion a, Root.move?_point conversion a, ⟨Moved.Model.point model a⟩⟩
  | selected descriptor child built =>
    cases built
    obtain ⟨converted, accepted⟩ := model.descriptor_exists descriptor
    exact ⟨Moved.selected conversion descriptor converted accepted,
      Root.move?_selected conversion descriptor converted accepted,
      ⟨Moved.Model.selected model descriptor converted accepted⟩⟩

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Root.move?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Root.move?_success
