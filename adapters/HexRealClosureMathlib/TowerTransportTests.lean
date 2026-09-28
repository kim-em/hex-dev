/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerTransport
public import HexRealClosureMathlib.SelectedRoot

namespace Hex.RealClosure.Tower.Conversion.Tests

private def registry : BaseContext.Registry := fun _ => none
private abbrev base := Context.base (BaseContext.rational registry)
private noncomputable def rational : Tower.Model base ℝ :=
  Tower.Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign

variable (descriptor : SignDet.Descriptor base.Value Signature base.sign base.signature)
variable {head : DensePoly base.Value} {lower upper : Endpoint base.Value}
variable (encoding : SignDet.Reencoding descriptor head lower upper)
variable (suffix : Suffix (base.adjoin descriptor).context)

/-- Complete reconstruction and interpretation at arbitrary finite depth. -/
example : ∃ result, (Conversion.refine base encoding).extend? suffix = some result ∧
    Nonempty (Conversion.Model result ((rational.adjoin descriptor).extend suffix)) :=
  (Conversion.Model.refine rational encoding).extend_exists suffix

/-- Identity can rebuild an arbitrary suffix without changing root meaning. -/
example (suffix : Suffix base) : ∃ result,
    (Conversion.identity base).extend? suffix = some result ∧
      Nonempty (Conversion.Model result (rational.extend suffix)) :=
  (Conversion.Model.identity rational).extend_exists suffix

example (result : Conversion suffix.context)
    (h : (Conversion.refine base encoding).extend? suffix = some result) :
    Nonempty (Conversion.Model result ((rational.adjoin descriptor).extend suffix)) :=
  ⟨(Conversion.Model.refine rational encoding).extend suffix result h⟩

example {first : Conversion base} (model : Conversion.Model first rational)
    {other : Context registry} (h : base = other) (x : other.Value) :
    (model.cast h).target.value ((first.cast h).value x) =
      (h ▸ rational).value x := (model.cast h).value x

example {first : Conversion base} (left : Conversion.Model first rational)
    {next : Conversion first.context} (right : Conversion.Model next left.target)
    (x : base.Value) : (left.comp right).target.value ((first.comp next).value x) = rational.value x :=
  (left.comp right).value x

/-- Two actual checked definition changes compose with their constructed models. -/
example {nextHead : DensePoly base.Value} {nextLower nextUpper : Endpoint base.Value}
    (following : SignDet.Reencoding encoding.target nextHead nextLower nextUpper) :
    let first := Conversion.refine base encoding
    let same := (Conversion.refine_spec base encoding).1.trans
      (congrArg Extension.context (base.refine encoding).canonical)
    let next := (Conversion.refine base following).cast same.symm
    Nonempty (Conversion.Model (first.comp next) (rational.adjoin descriptor)) := by
  dsimp only
  let left := Conversion.Model.refine rational encoding
  let same := (Conversion.refine_spec base encoding).1.trans
    (congrArg Extension.context (base.refine encoding).canonical)
  have target : left.target = (same.symm ▸ rational.adjoin encoding.target) :=
    eq_of_heq ((Conversion.Model.refine_heq rational encoding).trans
      ((rational.adjoin encoding.target).cast_heq same.symm).symm)
  let right := (Conversion.Model.refine rational following).cast same.symm
  have aligned : Conversion.Model ((Conversion.refine base following).cast same.symm) left.target :=
    target.symm ▸ right
  exact ⟨left.comp aligned⟩

variable (result : Conversion suffix.context)
variable (model : Conversion.Model result ((rational.adjoin descriptor).extend suffix))

example (value : suffix.context.Value) : result.value value = 0 ↔ value = 0 :=
  model.zero value

example (x y : suffix.context.Value) :
    result.context.compare (result.value x) (result.value y) = suffix.context.compare x y :=
  model.compare x y

example : ((rational.adjoin descriptor).extend suffix).field ≤ model.target.field := model.mono

example (p : DensePoly suffix.context.Value) :
    (DensePoly.ofCoeffs (p.toArray.map result.value)).natDegree = p.natDegree := model.degree p

end Hex.RealClosure.Tower.Conversion.Tests
