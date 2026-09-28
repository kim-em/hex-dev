/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerAlgebraic
public import HexRealClosureMathlib.TowerYun
public import HexRealClosureMathlib.TowerRefinement
public import HexRealClosureMathlib.SelectedRoot

namespace Hex.RealClosure.Tower.Model.Tests

private def registry : BaseContext.Registry := fun _ => none
private abbrev base := Context.base (BaseContext.rational registry)

/-- The rational base uses its actual native operations and the existing
proved rational sign correspondence, through the canonical base wrapper. -/
private noncomputable def rational : Model base ℝ :=
  Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign

section Successive
variable (d₁ : SignDet.Descriptor base.Value Signature base.sign base.signature)
private abbrev first : Extension base d₁ := base.adjoin d₁
private noncomputable abbrev model₁ : Model (first d₁).context ℝ := rational.adjoin d₁
variable (d₂ : SignDet.Descriptor (first d₁).context.Value Signature
  (first d₁).context.sign (first d₁).context.signature)
private abbrev second : Extension (first d₁).context d₂ := (first d₁).context.adjoin d₂
private noncomputable abbrev model₂ : Model (second d₁ d₂).context ℝ := (model₁ d₁).adjoin d₂
variable (d₃ : SignDet.Descriptor (second d₁ d₂).context.Value Signature
  (second d₁ d₂).context.sign (second d₁ d₂).context.signature)
private abbrev third : Extension (second d₁ d₂).context d₃ := (second d₁ d₂).context.adjoin d₃
private noncomputable abbrev model₃ : Model (third d₁ d₂ d₃).context ℝ := (model₂ d₁ d₂).adjoin d₃

/-- Actual explicit inclusions at three root levels preserve the rational base. -/
example (a : base.Value) :
    (model₃ d₁ d₂ d₃).value
      ((third d₁ d₂ d₃).embed ((second d₁ d₂).embed ((first d₁).embed a))) =
      (a.stored : ℝ) := by
  rw [Model.adjoin_embed, Model.adjoin_embed, Model.adjoin_embed]
  exact Model.base_value (BaseContext.rational registry) (Rat.castHom ℝ) ratSign a

example (a : (third d₁ d₂ d₃).context.Value) :
    (model₃ d₁ d₂ d₃).value a⁻¹ = ((model₃ d₁ d₂ d₃).value a)⁻¹ :=
  (model₃ d₁ d₂ d₃).inv a

example (a : (third d₁ d₂ d₃).context.Value) :
    (third d₁ d₂ d₃).context.sign a =
      (SignType.sign ((model₃ d₁ d₂ d₃).value a) : Int) :=
  (model₃ d₁ d₂ d₃).sign a

example (a : (third d₁ d₂ d₃).context.Value) :
    (model₃ d₁ d₂ d₃).value a = 0 ↔ a = 0 :=
  (model₃ d₁ d₂ d₃).zero_iff a

example : (model₃ d₁ d₂ d₃).value (third d₁ d₂ d₃).generator =
    d₃.root (model₂ d₁ d₂).value (model₂ d₁ d₂).zero_iff (model₂ d₁ d₂).one
      (model₂ d₁ d₂).add (model₂ d₁ d₂).sub (model₂ d₁ d₂).mul
      (model₂ d₁ d₂).nat (model₂ d₁ d₂).sign :=
  (model₂ d₁ d₂).adjoin_generator d₃

example : rational.field ≤ (model₃ d₁ d₂ d₃).field :=
  le_trans (rational.adjoin_mono d₁)
    (le_trans ((model₁ d₁).adjoin_mono d₂) ((model₂ d₁ d₂).adjoin_mono d₃))

-- Mathematical values inherit field/order laws; stored expressions keep their
-- ordinary native operations and nominal ownership.
noncomputable example : Field (model₃ d₁ d₂ d₃).field := inferInstance
noncomputable example : LinearOrder (model₃ d₁ d₂ d₃).field := inferInstance
noncomputable example : IsStrictOrderedRing (model₃ d₁ d₂ d₃).field := inferInstance

example (a b : (third d₁ d₂ d₃).context.Value) :
    (model₃ d₁ d₂ d₃).toValue a = (model₃ d₁ d₂ d₃).toValue b ↔
      (model₃ d₁ d₂ d₃).value a = (model₃ d₁ d₂ d₃).value b :=
  (model₃ d₁ d₂ d₃).toValue_equal a b
example (a : (third d₁ d₂ d₃).context.Value) :
    IsAlgebraic (model₂ d₁ d₂).field ((model₃ d₁ d₂ d₃).value a) :=
  (model₂ d₁ d₂).adjoin_algebraic d₃ a

example (a : (model₃ d₁ d₂ d₃).field) :
    IsAlgebraic (model₂ d₁ d₂).field (a : ℝ) :=
  (model₂ d₁ d₂).field_algebraic d₃ a
example (a b : (second d₁ d₂).context.Value) :
    (third d₁ d₂ d₃).context.equal
      ((third d₁ d₂ d₃).embed a) ((third d₁ d₂ d₃).embed b) =
      (second d₁ d₂).context.equal a b :=
  (model₂ d₁ d₂).adjoin_equal d₃ a b

example (a b : base.Value) :
    (third d₁ d₂ d₃).context.compare
      ((third d₁ d₂ d₃).embed ((second d₁ d₂).embed ((first d₁).embed a)))
      ((third d₁ d₂ d₃).embed ((second d₁ d₂).embed ((first d₁).embed b))) =
      base.compare a b := by
  rw [Model.adjoin_compare (model₂ d₁ d₂), Model.adjoin_compare (model₁ d₁),
    Model.adjoin_compare rational]
example (p : DensePoly (third d₁ d₂ d₃).context.Value) :
    Yun.check ((model₃ d₁ d₂ d₃).mapPoly p)
      (Yun.Decomposition.map (model₃ d₁ d₂ d₃).value (model₃ d₁ d₂ d₃).zero_iff
        (Yun.decomposeRaw p)) = true :=
  (model₃ d₁ d₂ d₃).decompose_sound p

example (p : DensePoly (third d₁ d₂ d₃).context.Value) (hd : 0 < p.natDegree)
    (unit : (third d₁ d₂ d₃).context.Value)
    (entries : Array (DensePoly (third d₁ d₂ d₃).context.Value × Nat))
    (hresult : Yun.decomposeRaw p = .factors unit entries)
    (entry : DensePoly (third d₁ d₂ d₃).context.Value × Nat) (he : entry ∈ entries) :
    (DensePoly.gcd entry.1 (DensePoly.derivativeImpl entry.1)).natDegree = 0 :=
  (model₃ d₁ d₂ d₃).decompose_squarefree p hd unit entries hresult entry he

example (p : DensePoly (third d₁ d₂ d₃).context.Value) (hp : p ≠ 0) (x : ℝ)
    (hx : (HexPolyMathlib.toPolynomial ((model₃ d₁ d₂ d₃).mapPoly p)).IsRoot x) :
    ∃ unit entries, Yun.decomposeRaw p = .factors unit entries ∧
      ∃ entry ∈ entries,
        entry.2 = (HexPolyMathlib.toPolynomial ((model₃ d₁ d₂ d₃).mapPoly p)).rootMultiplicity x ∧
          (HexPolyMathlib.toPolynomial ((model₃ d₁ d₂ d₃).mapPoly entry.1)).IsRoot x :=
  (model₃ d₁ d₂ d₃).decompose_root p hp x hx

variable {head : DensePoly (first d₁).context.Value}
variable {lower upper : Endpoint (first d₁).context.Value}
variable (encoding : SignDet.Reencoding d₂ head lower upper)

example (value : (second d₁ d₂).context.Value) :
    ((model₁ d₁).refine encoding).value (((first d₁).context.refine encoding).transport value) =
      (model₂ d₁ d₂).value value :=
  (model₁ d₁).refine_value encoding value

example : ((model₁ d₁).refine encoding).field = (model₂ d₁ d₂).field :=
  (model₁ d₁).refine_field encoding

example (p : DensePoly (second d₁ d₂).context.Value) :
    (((first d₁).context.refine encoding).mapPoly p).natDegree = p.natDegree :=
  (model₁ d₁).refine_degree encoding p

example : ∃ converted, ((first d₁).context.refine encoding).mapDescriptor? d₃ = some converted :=
  (model₁ d₁).refine_descriptor encoding d₃

example (converted : SignDet.Descriptor (((first d₁).context.refine encoding).extension.context.Value)
    Signature (((first d₁).context.refine encoding).extension.context.sign)
    (((first d₁).context.refine encoding).extension.context.signature))
    (hconverted : ((first d₁).context.refine encoding).mapDescriptor? d₃ = some converted)
    (value : (third d₁ d₂ d₃).context.Value) :
    (((model₁ d₁).refine encoding).adjoin converted).value
      (((first d₁).context.refine encoding).mapValue d₃ converted value) =
        (model₃ d₁ d₂ d₃).value value :=
  (model₁ d₁).refine_later encoding d₃ converted hconverted value

end Successive

end Hex.RealClosure.Tower.Model.Tests
