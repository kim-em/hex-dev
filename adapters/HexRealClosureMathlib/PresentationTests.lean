/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.Presentation

public section

namespace Hex.RealClosure.Tower
variable {registry : BaseContext.Registry} {parent : Context registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
variable (model : Model parent K)

/-- Ordinary imports expose a real closed field of mathematical native classes. -/
example : IsRealClosed (Presentation.Quotient model) := Presentation.realClosed model

example (x : Presentation.Quotient model) : IsAlgebraic model.field x :=
  Presentation.value_algebraic model x

example (suffix : Suffix parent) (a : parent.Value) :
    (Presentation.mk suffix (suffix.embed a)).toValue model =
      algebraMap model.field (Presentation.Quotient model) (model.toValue a) := by
  rw [Presentation.embed_value, Presentation.base_value]

/-- Actual native multiplication and total inversion satisfy cancellation on
classes whenever the executable native sign is nonzero. -/
example (suffix : Suffix parent) (a : suffix.context.Value)
    (nonzero : suffix.context.sign a ≠ 0) :
    (Presentation.mk suffix (a * a⁻¹)).toValue model = 1 := by
  rw [Presentation.toValue_mul, Presentation.toValue_inv]
  apply mul_inv_cancel₀
  intro zero
  apply nonzero
  rw [Presentation.toValue_sign model ⟨suffix, a⟩, zero]
  simp

example (suffix : Suffix parent) :
    (Presentation.mk suffix (0 : suffix.context.Value)⁻¹).toValue model = 0 := by
  rw [Presentation.toValue_inv, Presentation.toValue_zero, inv_zero]

/-- Raw presentations at different depths identify precisely equal values. -/
example (a b c : Presentation parent) (left : a.denote model = b.denote model)
    (right : b.denote model = c.denote model) : a.toValue model = c.toValue model :=
  (Presentation.toValue_eq model a c).mpr (left.trans right)

end Hex.RealClosure.Tower
