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

/-- Representatives from different finite depths can be added and compared
by the executable operations of one common native suffix. -/
example (a b : Presentation parent) :
    ∃ suffix : Suffix parent, ∃ x y : suffix.context.Value,
      (Presentation.mk suffix x).toValue model = a.toValue model ∧
      (Presentation.mk suffix y).toValue model = b.toValue model ∧
      (Presentation.mk suffix (x + y)).toValue model = a.toValue model + b.toValue model ∧
      (suffix.context.equal x y = true ↔ a.toValue model = b.toValue model) := by
  obtain ⟨suffix, stored, same⟩ := Presentation.common_suffix model [a, b]
  obtain ⟨x, rest, rfl, hx, remaining⟩ := List.map_eq_cons_iff.mp same
  obtain ⟨y, tail, rfl, hy, empty⟩ := List.map_eq_cons_iff.mp remaining
  refine ⟨suffix, x, y, hx, hy, ?_, ?_⟩
  · rw [Presentation.toValue_add, hx, hy]
  · rw [Presentation.equal_spec model suffix x y, hx, hy]

/-- Ordinary imports expose the actual refinement producer's coherence. -/
example {descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (a : (parent.adjoin descriptor).context.Value) :
    (Presentation.mk (.root encoding.target .nil)
      (_root_.cast (congrArg Context.Value ((Conversion.refine_spec parent encoding).1.trans
        (congrArg Extension.context (parent.refine encoding).canonical)))
        ((Conversion.refine parent encoding).value a))).toValue model =
      (Presentation.mk (.root descriptor .nil) a).toValue model :=
  Presentation.refined_value model encoding a

example [Algebra.IsAlgebraic model.field K] :
    Function.Surjective (fun a : Presentation parent => a.denote model) :=
  Presentation.denote_surjective model

noncomputable example [Algebra.IsAlgebraic model.field K] :
    Presentation.Quotient model ≃ₐ[model.field] K := Presentation.ambientEquiv model

end Hex.RealClosure.Tower
