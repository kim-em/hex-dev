/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureTheory.Union
public import HexRealClosureTheory.TowerModel

public section

namespace Hex.RealClosure.Tower.Model

variable {registry : BaseContext.Registry} {context : Tower.Context registry}
variable {B : Type u} {K : Type v}
variable [Field B] [Field K] [LinearOrder K] [Algebra B K]

/-- Restrict an interpreted native tower to the relative algebraic union of
its ambient field. Every context value must be algebraic over the chosen base
algebra map. For base enlargement, that map must agree with the model's
interpretation of native base coefficients. -/
@[expose] noncomputable def restrictUnion (model : Tower.Model context K)
    (algebraic : ∀ a : context.Value, IsAlgebraic B (model.value a)) :
    Tower.Model context (Union.Carrier B K) where
  value := fun a => ⟨model.value a, (Union.mem_iff _).mpr (algebraic a)⟩
  zero_iff := by
    intro a
    constructor
    · intro h
      exact (model.zero_iff a).mp (congrArg Subtype.val h)
    · intro h
      apply Subtype.ext
      exact (model.zero_iff a).mpr h
  one := Subtype.ext model.one
  add := fun a b => Subtype.ext (model.add a b)
  sub := fun a b => Subtype.ext (model.sub a b)
  mul := fun a b => Subtype.ext (model.mul a b)
  nat := fun n => Subtype.ext (model.nat n)
  neg := fun a => Subtype.ext (model.neg a)
  inv := fun a => Subtype.ext (model.inv a)
  div := fun a b => Subtype.ext (model.div a b)
  sign := by
    intro a
    rw [model.sign]
    rfl

@[simp] theorem restrictUnion_value (model : Tower.Model context K)
    (algebraic : ∀ a : context.Value, IsAlgebraic B (model.value a))
    (a : context.Value) :
    ((model.restrictUnion algebraic).value a : K) = model.value a := rfl

end Hex.RealClosure.Tower.Model

/-- info: 'Hex.RealClosure.Tower.Model.restrictUnion' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.restrictUnion

/-- info: 'Hex.RealClosure.Tower.Model.restrictUnion_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.restrictUnion_value
