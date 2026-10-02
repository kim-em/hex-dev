/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerRoots

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {parent : Context registry}

/-- A root over converted coefficients, with inclusions of the new
coefficient context and the entire original root context into its actual child.
Semantic preservation is proved for the result returned by `Root.move?`. -/
structure Moved (conversion : Conversion parent) (source : Root parent) : Type 1 where
  root : Root conversion.context
  input : Conversion conversion.context
  input_context : input.context = root.context
  transported : Conversion source.context
  transported_context : transported.context = root.context

/-- Moving a coefficient point retains the converted coefficient context. -/
@[expose] def Moved.point (conversion : Conversion parent) (a : parent.Value) :
    Moved conversion (.point a) :=
  ⟨.point (conversion.value a), Conversion.identity conversion.context,
    (Conversion.identity_spec conversion.context).1, conversion, rfl⟩

/-- Moving a selected root uses the actually validated converted descriptor
and the native packing closure for its original root context. -/
@[expose] def Moved.selected (conversion : Conversion parent)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (accepted : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (parent.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    Moved conversion (Root.ofSelection parent (.selected descriptor)) :=
  let child := conversion.context.adjoin converted
  ⟨.selected converted child rfl,
    Conversion.includeRoot conversion.context converted child rfl,
    (Conversion.includeRoot_spec conversion.context converted child rfl).1,
    conversion.adjoinChecked descriptor converted accepted,
    conversion.adjoinChecked_context descriptor converted accepted⟩

/-- Revalidate a root after converting its coefficients. The returned maps
retain every old value's owner, while permitting transport of the whole old
root context and the current coefficient context into one actual child. -/
@[expose] def Root.move? (conversion : Conversion parent) (source : Root parent) :
    Option (Moved conversion source) := by
  cases source with
  | point a => exact some (Moved.point conversion a)
  | selected descriptor child built =>
    cases built
    exact match accepted : SignDet.Descriptor.validate conversion.context.sign
        conversion.context.signature
        (parent.mapDescriptor conversion.context conversion.value descriptor) with
      | none => none
      | some converted => some (Moved.selected conversion descriptor converted accepted)

theorem Root.move?_point (conversion : Conversion parent) (a : parent.Value) :
    (.point a : Root parent).move? conversion = some (Moved.point conversion a) := rfl

theorem Root.move?_selected (conversion : Conversion parent)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (accepted : SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (parent.mapDescriptor conversion.context conversion.value descriptor) = some converted) :
    (Root.ofSelection parent (.selected descriptor)).move? conversion =
      some (Moved.selected conversion descriptor converted accepted) := by
  simp only [Root.ofSelection, Root.move?]
  split
  · rename_i rejected
    cases rejected.symm.trans accepted
  · rename_i output returned
    have same : output = converted := Option.some.inj (returned.symm.trans accepted)
    cases same
    rfl

end Hex.RealClosure.Tower
