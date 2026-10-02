/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerTransport
public import HexRealClosureMathlib.SelectedRoot
public import HexRealClosureMathlib.TowerRestriction
public import HexRealClosureMathlib.TowerEnlarge

namespace Hex.RealClosure.Tower.Conversion.Tests

private def registry : BaseContext.Registry := fun _ => none
private abbrev base := Context.base (BaseContext.rational registry)
private noncomputable def rational : Tower.Model base ℝ :=
  Tower.Model.base (BaseContext.rational registry) (Rat.castHom ℝ) ratSign

/-- An arbitrary old model of a rational root tower enlarges without any
agreement premise at its roots or a supplied new-base interpretation. -/
example (suffix : Suffix base) (old : Tower.Model suffix.context ℝ) :
    let ambient := Ambient.infinitesimal ℝ
    ∃ result : Conversion suffix.context, suffix.context.enlarge? = some result ∧
      Nonempty (Conversion.Model result (old.liftInfinitesimal ambient)) :=
  Context.enlarge?_ambient (BaseContext.rational registry) suffix rfl rational old
    (Ambient.infinitesimal ℝ)

/-- The old model may live in a non-real-closed ordered field, while its
reference base interpretation lives independently in the real numbers. -/
example (suffix : Suffix base) (old : Tower.Model suffix.context Rat) :
    let ambient := Ambient.infinitesimal Rat
    ∃ result : Conversion suffix.context, suffix.context.enlarge? = some result ∧
      Nonempty (Conversion.Model result (old.liftInfinitesimal ambient)) :=
  Context.enlarge?_ambient (BaseContext.rational registry) suffix rfl rational old
    (Ambient.infinitesimal Rat)

/-- Every validated rational-root suffix restricts to the relative algebraic union. -/
noncomputable example (suffix : Suffix base) :
    Tower.Model suffix.context (Union.Carrier Rat ℝ) :=
  Tower.Model.baseRestrict (BaseContext.rational registry) (Rat.castHom ℝ)
    ratSign suffix

/-- Restriction retains the prescribed rational map through every root level. -/
noncomputable example (suffix : Suffix base) (a : base.Value) :
    (Tower.Model.baseRestrict (BaseContext.rational registry) (Rat.castHom ℝ)
      ratSign suffix).value (suffix.embed a) =
      algebraMap Rat (Union.Carrier Rat ℝ) a.stored :=
  Tower.Model.baseRestrict_embed (BaseContext.rational registry)
    (Rat.castHom ℝ) ratSign suffix a

/-- Including an old rational value through any validated root suffix retains
the same rational embedding. -/
example (suffix : Suffix base) (a : base.Value) :
    (rational.extend suffix).value (suffix.embed a) = (a.stored : ℝ) := by
  simpa only [rational, Rat.coe_castHom] using
    (Tower.Model.extend_base_embed
      (BaseContext.rational registry) (Rat.castHom ℝ) ratSign suffix a)

/-- The rational base and its infinitesimal extension have compatible models
in the actual ordered algebraic real closure of rational functions. -/
example (suffix : Suffix base) :
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal (BaseContext.rational registry)) suffix,
      (Conversion.infinitesimal (BaseContext.rational registry)).rebuild? suffix =
        some rebuilt := Conversion.Model.rebuild_rational registry suffix

/-- The native rational base embeds in an enlarged ambient over ℝ. -/
noncomputable example :
    let ambient := Ambient.infinitesimal ℝ
    let f : Rat →+* ℝ := Rat.castHom ℝ
    Nonempty (Conversion.Model
      (Conversion.infinitesimal (BaseContext.rational registry))
      (Tower.Model.base (BaseContext.rational registry)
        ((Ambient.coefficientHom ambient).comp f)
        (Conversion.Model.mapped_base_sign f ratSign ambient))) := by
  exact ⟨Conversion.Model.infinitesimalMapped
    (BaseContext.rational registry) (Rat.castHom ℝ) ratSign
    (Ambient.infinitesimal ℝ)⟩

example (suffix : Suffix base) :
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal (BaseContext.rational registry)) suffix,
      (Conversion.infinitesimal (BaseContext.rational registry)).rebuild? suffix =
        some rebuilt :=
  Conversion.Model.rebuild_mapped
    (BaseContext.rational registry) (Rat.castHom ℝ) ratSign suffix

private abbrev nestedBase := (BaseContext.rational registry).infinitesimal

/-- A base that is itself a native rational-function level can be enlarged
through the proved native interpretation of that level. -/
noncomputable example (suffix : Suffix (Context.base nestedBase)) :
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal nestedBase) suffix,
      (Conversion.infinitesimal nestedBase).rebuild? suffix = some rebuilt := by
  classical
  let old := Ambient.infinitesimal Rat
  let f := Ambient.nativeHom HexRationalFnMathlib.ratField_eq old
  exact Conversion.Model.rebuild_mapped nestedBase f
    (fun q => Ambient.nativeHom_sign HexRationalFnMathlib.ratField_eq old q) suffix

variable (descriptor : SignDet.Descriptor base.Value Signature base.sign base.signature)
variable {head : DensePoly base.Value} {lower upper : Endpoint base.Value}
variable (encoding : SignDet.Reencoding descriptor head lower upper)
variable (suffix : Suffix (base.adjoin descriptor).context)

/-- A stored root over ℚ discharges the checked-enlargement theorem. -/
example : ∃ result : Conversion (base.adjoin descriptor).context,
    (base.adjoin descriptor).context.enlarge? = some result := by
  exact Context.enlarge?_exists (BaseContext.rational registry)
    (.root descriptor .nil) rfl
    (Rat.castHom ℝ) ratSign

/-- Every validated rational-root suffix has a checked enlarged conversion. -/
example (roots : Suffix base) :
    ∃ result : Conversion roots.context, roots.context.enlarge? = some result :=
  Context.enlarge?_suffix (BaseContext.rational registry) roots (Rat.castHom ℝ) ratSign

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

/-- The returned suffix has the same ambient interpretation as the final
conversion, so a later semantic conversion can compose with it. -/
example (rebuilt : Rebuilt (Conversion.refine base encoding) suffix) :
    HEq ((Conversion.Model.refine rational encoding).rebuild suffix rebuilt).target
      ((Conversion.Model.refine rational encoding).target.extend rebuilt.suffix) :=
  (Conversion.Model.refine rational encoding).rebuild_target suffix rebuilt

example (rebuilt : Rebuilt (Conversion.refine base encoding) suffix)
    (hr : (Conversion.refine base encoding).rebuild? suffix = some rebuilt)
    (h : (Conversion.refine base encoding).extend? suffix = some rebuilt.result) :
    HEq ((Conversion.Model.refine rational encoding).extend suffix rebuilt.result h).target
      ((Conversion.Model.refine rational encoding).target.extend rebuilt.suffix) :=
  (Conversion.Model.refine rational encoding).extend_target suffix rebuilt hr h

example (rebuilt : Rebuilt (Conversion.refine base encoding) suffix)
    (next : Conversion rebuilt.suffix.context)
    (following : Conversion.Model next
      ((Conversion.Model.refine rational encoding).target.extend rebuilt.suffix)) :
    Nonempty (Conversion.Model (rebuilt.result.comp (next.cast rebuilt.context_eq))
      ((rational.adjoin descriptor).extend suffix)) :=
  ⟨(Conversion.Model.refine rational encoding).rebuildComp suffix rebuilt next following⟩

private theorem second_refine {source : Context registry} (ambient : Tower.Model source ℝ)
    {suffix' : Suffix source}
    {converted : SignDet.Descriptor source.Value Signature source.sign source.signature}
    {rest : Suffix (source.adjoin converted).context}
    (shape : suffix' = .root converted rest)
    {head' : DensePoly source.Value} {lower' upper' : Endpoint source.Value}
    (second : SignDet.Reencoding converted head' lower' upper')
    (next : Conversion rest.context)
    (hn : (Conversion.refine source second).extend? rest = some next) :
    Nonempty (Conversion.Model
      (next.cast (congrArg (fun s : Suffix source => s.context) shape.symm))
      (ambient.extend suffix')) := by
  cases shape
  exact ⟨(Conversion.Model.refine ambient second).extend rest next hn⟩

/-- The shape needed to select that first root follows from the returned
checked trace, rather than from a caller's semantic assumption. -/
example {later : SignDet.Descriptor (base.adjoin descriptor).context.Value Signature
      (base.adjoin descriptor).context.sign (base.adjoin descriptor).context.signature}
    {rest : Suffix ((base.adjoin descriptor).context.adjoin later).context}
    (rebuilt : Rebuilt (Conversion.refine base encoding) (.root later rest)) :
    ∃ converted : SignDet.Descriptor (Conversion.refine base encoding).context.Value Signature
        (Conversion.refine base encoding).context.sign
        (Conversion.refine base encoding).context.signature,
      ∃ tail : Suffix ((Conversion.refine base encoding).context.adjoin converted).context,
        rebuilt.suffix = .root converted tail := rebuilt.root_shape

/-- A checked change of the first rebuilt root extends through the remaining
suffix, then composes with the original conversion. -/
example (rebuilt : Rebuilt (Conversion.refine base encoding) suffix)
    {converted : SignDet.Descriptor (Conversion.refine base encoding).context.Value Signature
      (Conversion.refine base encoding).context.sign
      (Conversion.refine base encoding).context.signature}
    {rest : Suffix ((Conversion.refine base encoding).context.adjoin converted).context}
    (shape : rebuilt.suffix = .root converted rest)
    {head' : DensePoly (Conversion.refine base encoding).context.Value}
    {lower' upper' : Endpoint (Conversion.refine base encoding).context.Value}
    (second : SignDet.Reencoding converted head' lower' upper')
    (next : Conversion rest.context)
    (hn : (Conversion.refine (Conversion.refine base encoding).context second).extend? rest =
      some next) :
    let actual := next.cast (congrArg
      (fun s : Suffix (Conversion.refine base encoding).context => s.context) shape.symm)
    ∃ following : Conversion.Model actual
          ((Conversion.Model.refine rational encoding).target.extend rebuilt.suffix),
        HEq ((Conversion.Model.refine rational encoding).rebuildComp suffix rebuilt actual following).target
          following.target := by
  let first := Conversion.Model.refine rational encoding
  obtain ⟨following⟩ := second_refine first.target shape second next hn
  exact ⟨following, first.rebuildComp_target suffix rebuilt _ following⟩

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
