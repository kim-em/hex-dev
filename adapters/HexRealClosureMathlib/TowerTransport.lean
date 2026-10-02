/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerTransport
public import HexRealClosureMathlib.TowerRefinement
public import HexRealClosureMathlib.TowerAlgebraic
public import HexRealClosureMathlib.Ambient

public section

namespace Hex.RealClosure.Tower.Model

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]

/-- Interpret the original finite suffix through its actual validated roots. -/
@[expose] noncomputable def extend {source : Context registry}
    (original : Model source K) (suffix : Suffix source) : Model suffix.context K :=
  match suffix with
  | .nil => original
  | .root descriptor rest => (original.adjoin descriptor).extend rest

/-- The actual embeddings through a validated suffix preserve each original
mathematical value. -/
theorem extend_embed {source : Context registry} (model : Model source K)
    (suffix : Suffix source) :
    ∀ a : source.Value, (model.extend suffix).value (suffix.embed a) = model.value a := by
  induction suffix with
  | nil => intro a; rfl
  | @root parent descriptor rest ih =>
    intro a
    exact (ih (model.adjoin descriptor) ((parent.adjoin descriptor).embed a)).trans
      (model.adjoin_embed descriptor a)

/-- Agreement with a coefficient-field map survives every selected-root
extension in a validated suffix. -/
theorem extend_base_agree {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (model : Model (Context.base base) K)
    (agree : ∀ a : (Context.base base).Value, model.value a = f a.stored)
    (suffix : Suffix (Context.base base)) (a : (Context.base base).Value) :
    (model.extend suffix).value (suffix.embed a) = f a.stored := by
  rw [model.extend_embed suffix a]
  exact agree a

/-- A canonical base embedding agrees with the model at every validated
root depth. -/
theorem extend_base_embed {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (suffix : Suffix (Context.base base)) (a : (Context.base base).Value) :
    ((Model.base base f hsign).extend suffix).value (suffix.embed a) = f a.stored := by
  exact extend_base_agree base f (Model.base base f hsign)
    (Model.base_value base f hsign) suffix a

/-- Algebraicity over a fixed base persists through every validated root in a
finite suffix, with no irreducibility hypothesis on its defining polynomials. -/
theorem extend_algebraic_over {B : Type v} [Field B] [Algebra B K]
    {source : Context registry} (model : Model source K) (suffix : Suffix source)
    (halgebraic : ∀ a : source.Value, IsAlgebraic B (model.value a)) :
    ∀ a : suffix.context.Value, IsAlgebraic B ((model.extend suffix).value a) := by
  induction suffix with
  | nil => exact halgebraic
  | root descriptor rest ih =>
    exact ih (model.adjoin descriptor)
      (model.adjoin_algebraic_over descriptor halgebraic)

/-- The final image field of a validated suffix is algebraic over the same base. -/
theorem extend_field_algebraic_over {B : Type v} [Field B] [Algebra B K]
    {source : Context registry} (model : Model source K) (suffix : Suffix source)
    (halgebraic : ∀ a : source.Value, IsAlgebraic B (model.value a))
    (a : (model.extend suffix).field) : IsAlgebraic B (a : K) := by
  obtain ⟨x, hx⟩ := a.property
  rw [← hx]
  exact model.extend_algebraic_over suffix halgebraic x

/-- Starting with the canonical base model makes every finite selected-root
suffix algebraic over its original coefficient field. -/
theorem extend_base_algebraic {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (suffix : Suffix (Context.base base)) :
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := f.toAlgebra
    ∀ a : suffix.context.Value,
      IsAlgebraic B (((Model.base base f hsign).extend suffix).value a) := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  letI : Algebra B K := f.toAlgebra
  exact (Model.base base f hsign).extend_algebraic_over suffix
    (Model.base_algebraic base f hsign)

/-- The full image field of a finite tower over its canonical base is
algebraic over that base. -/
theorem extend_base_field_algebraic {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (base : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (suffix : Suffix (Context.base base)) :
    letI : Field B := HexPolyMathlib.fieldOfGrind
    letI : Algebra B K := f.toAlgebra
    ∀ a : ((Model.base base f hsign).extend suffix).field,
      IsAlgebraic B (a : K) := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  letI : Algebra B K := f.toAlgebra
  intro a
  exact (Model.base base f hsign).extend_field_algebraic_over suffix
    (Model.base_algebraic base f hsign) a

/-- Interpret the entire old tower in a supplied ordered algebraic real
closure of the old ambient field's infinitesimal extension. -/
@[expose] noncomputable def liftInfinitesimal {source : Context registry} {R : Type u}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]
    (ambient : Ambient (Hex.RationalFn R))
    (model : Model source R) : Model source ambient.Carrier :=
  model.map (Ambient.coefficientHom ambient)
    (Ambient.coefficientHom_strictMono ambient)

@[simp] theorem liftInfinitesimal_value {source : Context registry} {R : Type u}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]
    (ambient : Ambient (Hex.RationalFn R)) (model : Model source R)
    (a : source.Value) :
    (model.liftInfinitesimal ambient).value a =
      Ambient.coefficientHom ambient (model.value a) :=
  model.map_value _ _ a

/-- The semantic new infinitesimal is below every positive interpreted old
tower value in the common enlarged ambient field. -/
theorem liftInfinitesimal_X_lt {source : Context registry} {R : Type u}
    [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]
    (ambient : Ambient (Hex.RationalFn R)) (model : Model source R)
    (a : source.Value) (positive : 0 < model.value a) :
    ambient.inclusion (Hex.RationalFn.X : Hex.RationalFn R) <
      (model.liftInfinitesimal ambient).value a := by
  rw [liftInfinitesimal_value]
  exact Ambient.X_lt_coefficient ambient _ positive

end Hex.RealClosure.Tower.Model

namespace Hex.RealClosure.Tower.Conversion

variable {registry : BaseContext.Registry} {K : Type u}
variable [Field K] [LinearOrder K]
variable {source : Context registry}

/-- Interpret a native conversion relative to the original model. This
companion witness is never an argument of an executable constructor. -/
structure Model (conversion : Conversion source)
    (original : Hex.RealClosure.Tower.Model source K) where
  target : Hex.RealClosure.Tower.Model conversion.context K
  value : ∀ x, target.value (conversion.value x) = original.value x

namespace Model

open HexRealRootsMathlib Hex.SignDet

variable {conversion : Conversion source}
variable {original : Hex.RealClosure.Tower.Model source K}
variable (model : Model conversion original)

include model in
/-- Native canonical zero is preserved and reflected at every conversion step. -/
theorem zero (x : source.Value) : conversion.value x = 0 ↔ x = 0 := by
  rw [← model.target.zero_iff, model.value, original.zero_iff]

/-- Normalized coefficient conversion is the shared zero-reflecting map. -/
theorem map_dense (p : DensePoly source.Value) :
    DensePoly.ofCoeffs (p.toArray.map conversion.value) =
      DensePoly.Interpret.map conversion.value model.zero p := by
  have h := DensePoly.Interpret.map_ofCoeffs conversion.value model.zero p.toArray
  rw [DensePoly.ofCoeffs_toArray] at h
  exact h.symm

include model in
/-- The actual converted dense polynomial retains its source degree. -/
theorem degree (p : DensePoly source.Value) :
    (DensePoly.ofCoeffs (p.toArray.map conversion.value)).natDegree = p.natDegree := by
  rw [model.map_dense]
  exact DensePoly.Interpret.map_degree _ _ p

/-- Actual converted values include the whole original mathematical field. -/
theorem mono : original.field ≤ model.target.field := by
  rintro x ⟨value, rfl⟩
  exact ⟨conversion.value value, model.value value⟩

variable [DecidableEq K]

/-- Native coefficient conversion preserves the complete ambient polynomial. -/
theorem polynomial (p : DensePoly source.Value) :
    HexPolyMathlib.Interpret.interpret model.target.value model.target.zero_iff
      (DensePoly.ofCoeffs (p.toArray.map conversion.value)) =
    HexPolyMathlib.Interpret.interpret original.value original.zero_iff p := by
  apply Polynomial.ext
  intro i
  rw [HexPolyMathlib.Interpret.coeff_interpret,
    HexPolyMathlib.Interpret.coeff_interpret, model.map_dense,
    DensePoly.Interpret.map_coeff, model.value]

omit [DecidableEq K] in
private theorem cast_value {context other : Context registry} (h : context = other)
    (original : Hex.RealClosure.Tower.Model context K)
    {A : Type} (f : A → context.Value) (g : A → other.Value) (hg : HEq g f) (x : A) :
    (h ▸ original).value (g x) = original.value (f x) := by
  cases h
  cases eq_of_heq hg
  rfl

omit [DecidableEq K] in
/-- Identity interprets every value in the unchanged source model. -/
noncomputable def identity (original : Hex.RealClosure.Tower.Model source K) :
    Model (Conversion.identity source) original where
  target := (Conversion.identity_spec source).1.symm ▸ original
  value x := by
    rw [cast_value _ _ _ _ (Conversion.identity_spec source).2]
    rfl

omit [DecidableEq K] in
/-- An enlarged base model compatible with the native constant embedding
interprets the checked base conversion. -/
noncomputable def infinitesimal {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (context : BaseContext.Context registry B sign)
    (old : Hex.RealClosure.Tower.Model (Context.base context) K)
    (new : Hex.RealClosure.Tower.Model (Context.base context.infinitesimal) K)
    (compatible : ∀ value : BaseContext.Element context,
      new.value value.embed = old.value value) :
    Model (Conversion.infinitesimal context) old := by
  have spec := Conversion.infinitesimal_spec context
  exact
    { target := spec.1.symm ▸ new
      value := by
        intro value
        rw [cast_value _ _ _ _ spec.2]
        exact compatible value }

omit [DecidableEq K] in
/-- Compatible interpretations of the old field and its infinitesimal
rational-function extension give the semantic base conversion. -/
noncomputable def infinitesimalHom {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (context : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* K)
    (g : letI : Field (Hex.RationalFn B) := HexPolyMathlib.fieldOfGrind;
      Hex.RationalFn B →+* K)
    (hOld : ∀ a, sign a = (SignType.sign (f a) : Int))
    (hNew : ∀ q, Hex.OrderedFn.Infinitesimal.sign sign q =
      (SignType.sign (g q) : Int))
    (hcomp : ∀ a, g (Hex.RationalFn.C a) = f a) :
    Model (Conversion.infinitesimal context)
      (Hex.RealClosure.Tower.Model.base context f hOld) :=
  infinitesimal context (Hex.RealClosure.Tower.Model.base context f hOld)
    (Hex.RealClosure.Tower.Model.base context.infinitesimal g hNew) (by
      intro value
      simp only [Hex.RealClosure.Tower.Model.base_value,
        BaseContext.Element.stored_embed]
      exact hcomp value.stored)

omit [DecidableEq K] in
/-- Reconcile both source ownership and its interpretation by context equality. -/
noncomputable def cast {other : Context registry} (h : source = other) :
    Model (conversion.cast h) (h ▸ original) := by
  cases h
  exact model

omit [DecidableEq K] in
private theorem cast_target_proof {other : Context registry} (h : source = other) :
    HEq (model.cast h).target model.target := by
  cases h
  rfl

omit [DecidableEq K] in
/-- Changing source ownership leaves the actual target interpretation intact. -/
theorem cast_target {other : Context registry} (h : source = other) :
    HEq (model.cast h).target model.target := model.cast_target_proof h

omit [DecidableEq K] in
private theorem target_cast_original {context : Context registry}
    {left right : Hex.RealClosure.Tower.Model context K}
    {next : Conversion context} (h : left = right) (following : Model next right) :
    HEq (h.symm ▸ following).target following.target := by
  cases h
  rfl

omit [DecidableEq K] in
/-- Compose semantic witnesses for the actual two native conversions. -/
noncomputable def comp {next : Conversion conversion.context}
    (following : Model next model.target) : Model (conversion.comp next) original where
  target := (conversion.comp_spec next).1.symm ▸ following.target
  value x := by
    rw [cast_value _ _ _ _ (conversion.comp_spec next).2]
    exact (following.value (conversion.value x)).trans (model.value x)

omit [DecidableEq K] in
/-- Composition retains the second conversion's target interpretation. -/
theorem comp_target {next : Conversion conversion.context}
    (following : Model next model.target) :
    HEq (model.comp following).target following.target := by
  unfold comp
  exact following.target.cast_heq (conversion.comp_spec next).1.symm

variable [IsStrictOrderedRing K] [IsRealClosed K]

/-- Start a semantic conversion at the actual checked refinement. The witness
supplies the target model and preservation for every source-owned value. -/
noncomputable def refine {parent : Context registry}
    (original : Hex.RealClosure.Tower.Model parent K)
    {descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper) :
    Model (Conversion.refine parent encoding) (original.adjoin descriptor) where
  target := (Conversion.refine_spec parent encoding).1.symm ▸ original.refine encoding
  value x := by
    rw [cast_value _ _ _ _ (Conversion.refine_spec parent encoding).2]
    exact original.refine_value encoding x

/-- The actual target interpretation agrees with the canonical reencoded-root model. -/
theorem refine_heq {parent : Context registry}
    (original : Hex.RealClosure.Tower.Model parent K)
    {descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper) :
    HEq (refine original encoding).target (original.adjoin encoding.target) := by
  unfold refine
  exact ((original.refine encoding).cast_heq _).trans (original.refine_heq encoding)

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem endpoint (point : Endpoint source.Value) :
    (point.map conversion.value).map model.target.value = point.map original.value := by
  cases point <;> simp only [Endpoint.map, model.value]

omit [IsStrictOrderedRing K] [IsRealClosed K] in
private theorem domain (p : DensePoly source.Value) (lower upper : Endpoint source.Value) :
    HexSturmMathlib.Domain model.target.value model.target.zero_iff
      (DensePoly.ofCoeffs (p.toArray.map conversion.value))
      (lower.map conversion.value) (upper.map conversion.value) ↔
    HexSturmMathlib.Domain original.value original.zero_iff p lower upper := by
  unfold HexSturmMathlib.Domain
  rw [model.polynomial]
  cases lower <;> cases upper <;>
    simp only [Endpoint.map, HexSturmMathlib.EndpointLt, HexSturmMathlib.Nonvanishing, model.value]

variable (descriptor : SignDet.Descriptor source.Value Signature source.sign source.signature)

omit [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K] in
include model in
private theorem wellFormed :
    (source.mapDescriptor conversion.context conversion.value descriptor).wellFormed = true := by
  have hw := (SignDet.RawDescriptor.check_eq descriptor.accepted).1
  unfold Context.mapDescriptor SignDet.RawDescriptor.wellFormed
  rw [model.degree]
  exact hw

include model in
/-- Revalidation of every later descriptor succeeds under value-preserving
native conversion, with fresh context bindings and formal derivative signs. -/
theorem descriptor_exists :
    ∃ converted, SignDet.Descriptor.validate conversion.context.sign conversion.context.signature
      (source.mapDescriptor conversion.context conversion.value descriptor) = some converted := by
  obtain ⟨hw, hctx, hc, hcount⟩ := SignDet.RawDescriptor.check_eq descriptor.accepted
  have hdom := descriptor.evidence.check_domain original.value original.zero_iff original.one
    original.add original.sub original.mul original.nat _ original.sign _ _ _ _ _ hc
  have hone := descriptor.evidence.count_roots original.value original.zero_iff original.one
    original.add original.sub original.mul original.nat _ original.sign _ _ _ _ _ hc descriptor.raw.signs
  have hlookup := descriptor.evidence.table_lookup hc descriptor.raw.signs
  have hcard := hone.symm.trans (hlookup.symm.trans hcount)
  apply (SignDet.Descriptor.validate_success_formal model.target.value model.target.zero_iff
    model.target.one model.target.add model.target.sub model.target.mul model.target.nat
    model.target.neg model.target.inv _ model.target.sign _ _).mpr
  refine ⟨rfl, model.wellFormed descriptor, (model.domain _ _ _).mpr hdom, ?_⟩
  simp only [Context.mapDescriptor, model.polynomial, model.endpoint]
  convert hcard using 2
  apply Finset.filter_congr
  intro x hx
  simp only [signsAt]
  rw [descriptor.raw.querySigns original.value original.zero_iff original.nat original.mul hw x]

include model in
/-- Every later native conversion succeeds; callers supply no replay premise. -/
theorem adjoin_exists : ∃ result, conversion.adjoin? descriptor = some result :=
  conversion.adjoin_exists descriptor (model.descriptor_exists descriptor)

/-- A later descriptor with the converted operands selects the same root. -/
theorem root (converted : SignDet.Descriptor conversion.context.Value Signature
    conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor) :
    converted.root model.target.value model.target.zero_iff model.target.one model.target.add
      model.target.sub model.target.mul model.target.nat model.target.sign =
    descriptor.root original.value original.zero_iff original.one original.add original.sub
      original.mul original.nat original.sign := by
  obtain ⟨hx, hs⟩ := converted.root_spec model.target.value model.target.zero_iff
    model.target.one model.target.add model.target.sub model.target.mul model.target.nat model.target.sign
  apply descriptor.root_unique original.value original.zero_iff original.one original.add
    original.sub original.mul original.nat original.sign
  · rw [binding] at hx
    dsimp only [Context.mapDescriptor] at hx
    simpa only [model.polynomial, model.endpoint] using hx
  · rw [descriptor.derivatives_at original.value original.zero_iff original.mul original.nat]
    rw [converted.derivatives_at model.target.value model.target.zero_iff model.target.mul model.target.nat] at hs
    rw [binding] at hs
    dsimp only [Context.mapDescriptor] at hs
    simpa only [model.polynomial] using hs

/-- Interpret a later conversion using its actual converted descriptor and
packing closure. This form keeps the target model tied to that descriptor. -/
noncomputable def adjoinWith
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor)
    (result : Conversion (source.adjoin descriptor).context)
    (context : result.context = (conversion.context.adjoin converted).context)
    (values : HEq result.value (fun x => conversion.context.ofPoly converted
      (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value)))) :
    Model result (original.adjoin descriptor) := by
  refine ⟨context.symm ▸ model.target.adjoin converted, ?_⟩
  intro x
  rw [cast_value _ _ _ _ values, model.target.adjoin_ofPoly, model.polynomial,
    model.target.adjoin_generator, model.root descriptor converted binding,
    original.adjoin_value descriptor x, original.adjoin_generator]

/-- The explicit converted descriptor also fixes the new ambient model. -/
theorem adjoinWith_target
    (converted : SignDet.Descriptor conversion.context.Value Signature
      conversion.context.sign conversion.context.signature)
    (binding : converted.raw = source.mapDescriptor conversion.context conversion.value descriptor)
    (result : Conversion (source.adjoin descriptor).context)
    (context : result.context = (conversion.context.adjoin converted).context)
    (values : HEq result.value (fun x => conversion.context.ofPoly converted
      (DensePoly.ofCoeffs ((source.polynomial descriptor x).toArray.map conversion.value)))) :
    HEq (model.adjoinWith descriptor converted binding result context values).target
      (model.target.adjoin converted) := by
  unfold adjoinWith
  exact (model.target.adjoin converted).cast_heq context.symm

/-- Interpret the actual returned later conversion. This preserves every
stored value and can be applied again at the next root level. -/
noncomputable def adjoin (result : Conversion (source.adjoin descriptor).context)
    (h : conversion.adjoin? descriptor = some result) : Model result (original.adjoin descriptor) := by
  let spec := conversion.adjoin_spec descriptor result h
  let converted := Classical.choose spec
  exact model.adjoinWith descriptor converted (Classical.choose_spec spec).1 result
    (Classical.choose_spec spec).2.1 (Classical.choose_spec spec).2.2

private theorem extend_cast_heq {left right : Context registry} (h : left = right)
    (target : Hex.RealClosure.Tower.Model right K) (suffix : Suffix left) :
    HEq ((h.symm ▸ target).extend suffix) (target.extend (h ▸ suffix)) := by
  cases h
  rfl

/-- Interpret the exact rebuilt suffix in the target model of the starting
conversion, while preserving the old final values. -/
private theorem align_exists {suffix : Suffix source} {result : Conversion suffix.context}
    {converted : Suffix conversion.context}
    (trace : Rebuilds conversion suffix result converted) :
    ∃ witness : Model result (original.extend suffix),
      HEq witness.target (model.target.extend converted) := by
  induction trace with
  | nil initial =>
    exact ⟨model, HEq.rfl⟩
  | root initial descriptor rest converted h tail ih =>
    let next := initial.adjoinChecked descriptor converted h
    let binding := SignDet.Descriptor.build_raw (SignDet.Descriptor.validate_eq_some.mp h)
    let step := model.adjoinWith descriptor converted binding next
      (initial.adjoinChecked_context descriptor converted h)
      (initial.adjoinChecked_value descriptor converted h)
    obtain ⟨witness, hw⟩ := ih step
    refine ⟨witness, ?_⟩
    have ht := model.adjoinWith_target descriptor converted binding next
      (initial.adjoinChecked_context descriptor converted h)
      (initial.adjoinChecked_value descriptor converted h)
    have hc := initial.adjoinChecked_context descriptor converted h
    have cast_target := (model.target.adjoin converted).cast_heq hc.symm
    have heq : step.target = (hc.symm ▸ model.target.adjoin converted) :=
      eq_of_heq (ht.trans cast_target.symm)
    rw [heq] at hw
    refine hw.trans ?_
    simpa only [Hex.RealClosure.Tower.Model.extend, Suffix.context] using
      (extend_cast_heq hc (model.target.adjoin converted) _)

include model in
/-- Recursive rebuilding succeeds for every finite validated suffix and
preserves every source-owned value in the actual final native conversion. -/
theorem extend_exists (suffix : Suffix source) :
    ∃ result, conversion.extend? suffix = some result ∧
      Nonempty (Model result (original.extend suffix)) := by
  induction suffix with
  | nil => exact ⟨conversion, conversion.extend_nil, ⟨model⟩⟩
  | root descriptor rest ih =>
    obtain ⟨next, hnext⟩ := model.adjoin_exists descriptor
    obtain ⟨result, hresult, preserved⟩ := ih (model.adjoin descriptor next hnext)
    refine ⟨result, ?_, preserved⟩
    rw [conversion.extend_root, hnext]
    exact hresult

include model in
/-- Rebuilding a validated suffix also returns all converted descriptors. -/
theorem rebuild_exists (suffix : Suffix source) :
    ∃ rebuilt : Rebuilt conversion suffix, conversion.rebuild? suffix = some rebuilt := by
  obtain ⟨result, hresult, _⟩ := model.extend_exists suffix
  have h := conversion.rebuild_result suffix
  rw [hresult] at h
  cases hr : conversion.rebuild? suffix with
  | none =>
    simp only [Option.map, hr] at h
    cases h
  | some rebuilt => exact ⟨rebuilt, rfl⟩

/-- A compatible enlarged base model makes rebuilding every validated
algebraic suffix succeed, retaining the converted descriptors. -/
theorem rebuild_infinitesimal {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (context : BaseContext.Context registry B sign)
    (old : Hex.RealClosure.Tower.Model (Context.base context) K)
    (new : Hex.RealClosure.Tower.Model (Context.base context.infinitesimal) K)
    (compatible : ∀ value : BaseContext.Element context,
      new.value value.embed = old.value value)
    (suffix : Suffix (Context.base context)) :
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal context) suffix,
      (Conversion.infinitesimal context).rebuild? suffix = some rebuilt :=
  (infinitesimal context old new compatible).rebuild_exists suffix

open scoped Hex.OrderedFn.Infinitesimal in
/-- Every validated finite suffix over ℚ rebuilds after adjoining an
infinitesimal, using the ordered algebraic real closure of ℚ(ε). -/
theorem rebuild_rational (registry : BaseContext.Registry)
    (suffix : Suffix (Context.base (BaseContext.rational registry))) :
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal (BaseContext.rational registry)) suffix,
      (Conversion.infinitesimal (BaseContext.rational registry)).rebuild? suffix =
        some rebuilt := by
  let wide := Ambient.infinitesimal Rat
  letI : Field wide.Carrier := wide.field
  letI : LinearOrder wide.Carrier := wide.order
  letI : IsStrictOrderedRing wide.Carrier := wide.ordered
  let g := Ambient.nativeHom HexRationalFnMathlib.ratField_eq wide
  have hOld (a : Rat) : Hex.OrderedFn.orderSign a =
      (SignType.sign ((Rat.castHom wide.Carrier) a) : Int) := by
    rw [Rat.cast_strictMono.sign_comp,
      Hex.OrderedFn.Infinitesimal.orderSign_eq]
  have hNew (q : Hex.RationalFn Rat) :
      Hex.OrderedFn.Infinitesimal.sign Hex.OrderedFn.orderSign q =
        (SignType.sign (g q) : Int) :=
    Ambient.nativeHom_sign HexRationalFnMathlib.ratField_eq wide q
  have hcomp (a : Rat) : g (Hex.RationalFn.C a) = (Rat.castHom wide.Carrier) a := by
    rw [Ambient.nativeHom_C]
    change (Ambient.coefficientHom wide) a =
      (Rat.castHom wide.Carrier) a
    simp
  exact (infinitesimalHom (BaseContext.rational registry)
    (Rat.castHom wide.Carrier) g hOld hNew hcomp).rebuild_exists suffix

/-- Interpret the final conversion using the exact rebuilt suffix, while
preserving every old value in the original ambient field. -/
noncomputable def rebuild (suffix : Suffix source)
    (rebuilt : Rebuilt conversion suffix) :
    Model rebuilt.result (original.extend suffix) :=
  Classical.choose (model.align_exists rebuilt.checked)

/-- The semantic target of the final conversion is the model obtained by
interpreting its returned validated suffix from the starting target model. -/
theorem rebuild_target (suffix : Suffix source) (rebuilt : Rebuilt conversion suffix) :
    HEq (model.rebuild suffix rebuilt).target
      (model.target.extend rebuilt.suffix) :=
  Classical.choose_spec (model.align_exists rebuilt.checked)

private theorem extend_aligned (suffix : Suffix source) (result : Conversion suffix.context)
    (h : conversion.extend? suffix = some result) :
    ∃ witness : Model result (original.extend suffix),
      ∃ rebuilt : Rebuilt conversion suffix,
        conversion.rebuild? suffix = some rebuilt ∧
          HEq witness.target (model.target.extend rebuilt.suffix) := by
  obtain ⟨rebuilt, hr⟩ := model.rebuild_exists suffix
  have same : rebuilt.result = result := by
    have mapped := congrArg (Option.map Rebuilt.result) hr
    rw [conversion.rebuild_result suffix, h] at mapped
    exact Option.some.inj (by simpa only [Option.map_some] using mapped.symm)
  subst result
  exact ⟨model.rebuild suffix rebuilt, rebuilt, hr, model.rebuild_target suffix rebuilt⟩

/-- Interpret a particular result returned by recursive reconstruction using
the same checked suffix model as `rebuild`. -/
noncomputable def extend (suffix : Suffix source) (result : Conversion suffix.context)
    (h : conversion.extend? suffix = some result) : Model result (original.extend suffix) :=
  Classical.choose (model.extend_aligned suffix result h)

/-- The ordinary traversal uses the target interpretation of the actual
descriptor-retaining traversal. -/
theorem extend_target (suffix : Suffix source)
    (rebuilt : Rebuilt conversion suffix)
    (hr : conversion.rebuild? suffix = some rebuilt)
    (h : conversion.extend? suffix = some rebuilt.result) :
    HEq (model.extend suffix rebuilt.result h).target
      (model.target.extend rebuilt.suffix) := by
  obtain ⟨actual, output, alignment⟩ :=
    Classical.choose_spec (model.extend_aligned suffix rebuilt.result h)
  have same : actual = rebuilt := Option.some.inj (output.symm.trans hr)
  subst actual
  exact alignment

/-- Compose a later semantic conversion with the rebuilt tower. The context
equality and model alignment discharge the ownership change automatically. -/
noncomputable def rebuildComp (suffix : Suffix source)
    (rebuilt : Rebuilt conversion suffix)
    (next : Conversion rebuilt.suffix.context)
    (following : Model next (model.target.extend rebuilt.suffix)) :
    Model (rebuilt.result.comp (next.cast rebuilt.context_eq))
      (original.extend suffix) := by
  let first := model.rebuild suffix rebuilt
  let right := following.cast rebuilt.context_eq
  have cast_target := (model.target.extend rebuilt.suffix).cast_heq rebuilt.context_eq
  have target_eq : first.target =
      (rebuilt.context_eq ▸ model.target.extend rebuilt.suffix) :=
    eq_of_heq ((model.rebuild_target suffix rebuilt).trans cast_target.symm)
  exact first.comp (target_eq.symm ▸ right)

/-- A composed later conversion retains the later target model, so further
checked refinements can use it without recovering an arbitrary witness. -/
theorem rebuildComp_target (suffix : Suffix source)
    (rebuilt : Rebuilt conversion suffix)
    (next : Conversion rebuilt.suffix.context)
    (following : Model next (model.target.extend rebuilt.suffix)) :
    HEq (model.rebuildComp suffix rebuilt next following).target following.target := by
  let first := model.rebuild suffix rebuilt
  let right := following.cast rebuilt.context_eq
  have cast_target := (model.target.extend rebuilt.suffix).cast_heq rebuilt.context_eq
  have target_eq : first.target =
      (rebuilt.context_eq ▸ model.target.extend rebuilt.suffix) :=
    eq_of_heq ((model.rebuild_target suffix rebuilt).trans cast_target.symm)
  exact (first.comp_target (target_eq.symm ▸ right)).trans
    ((target_cast_original target_eq right).trans (following.cast_target rebuilt.context_eq))

omit [IsStrictOrderedRing K] [IsRealClosed K] in
include model in
/-- Native semantic equality results are preserved throughout conversion. -/
theorem equal (x y : source.Value) :
    conversion.context.equal (conversion.value x) (conversion.value y) = source.equal x y := by
  rw [model.target.equal_spec, original.equal_spec, model.value, model.value]

omit [IsRealClosed K] in
include model in
/-- Native ordered comparison results are preserved throughout conversion. -/
theorem compare (x y : source.Value) :
    conversion.context.compare (conversion.value x) (conversion.value y) = source.compare x y := by
  rw [model.target.compare_spec, original.compare_spec, model.value, model.value]

end Model
end Hex.RealClosure.Tower.Conversion

namespace Hex.RealClosure.Tower.Conversion.Model

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {R : Type u}
variable [Field R] [LinearOrder R] [IsStrictOrderedRing R] [DecidableEq R]

/-- The old base embedding retains its prescribed sign after inclusion as
constants in the enlarged semantic field. -/
theorem mapped_base_sign {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* R)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (ambient : Ambient (Hex.RationalFn R)) (a : B) :
    sign a = (SignType.sign (Ambient.coefficientHom ambient (f a)) : Int) := by
  rw [hsign]
  exact (congrArg (fun s : SignType => (s : Int))
    ((Ambient.coefficientHom_strictMono ambient).sign_comp (f a))).symm

/-- The mapped native `B(δ)` and the old base field have compatible canonical
models inside one ordered algebraic real closure of `R(δ)`. -/
noncomputable def infinitesimalMapped {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (context : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* R)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (ambient : Ambient (Hex.RationalFn R)) :
    letI : Field B := HexPolyMathlib.fieldOfGrind
    Model (Conversion.infinitesimal context)
      (Hex.RealClosure.Tower.Model.base context
        ((Ambient.coefficientHom ambient).comp f)
        (mapped_base_sign f hsign ambient)) := by
  letI : Field B := HexPolyMathlib.fieldOfGrind
  have compatible : Field.toGrindField (K := B) = ‹Lean.Grind.Field B› :=
    HexPolyMathlib.toGrind_fieldOfGrind
  let old := (Ambient.coefficientHom ambient).comp f
  let new := Ambient.mappedNativeHom compatible f ambient
  have hOld (a : B) : sign a = (SignType.sign (old a) : Int) :=
    mapped_base_sign f hsign ambient a
  have hNew (q : Hex.RationalFn B) :
      Hex.OrderedFn.Infinitesimal.sign sign q =
        (SignType.sign (new q) : Int) :=
    Ambient.mappedNativeHom_sign compatible f sign hsign ambient q
  have hcomp (a : B) : new (Hex.RationalFn.C a) = old a :=
    Ambient.mappedNativeHom_C compatible f ambient a
  exact infinitesimalHom context old new hOld hNew hcomp

/-- Every finite validated root suffix over a sign-compatible base embeds
through the common enlarged ambient field and rebuilds successfully. -/
theorem rebuild_mapped {B : Type} [Lean.Grind.Field B] [DecidableEq B]
    {sign : B → Int} (context : BaseContext.Context registry B sign)
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* R)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int))
    (suffix : Suffix (Context.base context)) :
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal context) suffix,
      (Conversion.infinitesimal context).rebuild? suffix = some rebuilt :=
  (infinitesimalMapped context f hsign (Ambient.infinitesimal R)).rebuild_exists suffix

end Hex.RealClosure.Tower.Conversion.Model

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.infinitesimalMapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.infinitesimalMapped

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.rebuild_mapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.rebuild_mapped

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.zero

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.degree' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.degree

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.polynomial' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.polynomial

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.mono

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.refine' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.refine

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.adjoin_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.adjoin_exists

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.adjoin' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.adjoin

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.adjoinWith' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.adjoinWith

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.extend_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.extend_exists

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.compare' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.compare

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.identity' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.identity
/--
info: 'Hex.RealClosure.Tower.Conversion.Model.comp' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.comp
/--
info: 'Hex.RealClosure.Tower.Conversion.Model.equal' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.equal
/--
info: 'Hex.RealClosure.Tower.Conversion.Model.root' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.root
/--
info: 'Hex.RealClosure.Tower.Conversion.Model.descriptor_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.descriptor_exists
/--
info: 'Hex.RealClosure.Tower.Conversion.Model.extend' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.extend

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.extend_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.extend_target

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.rebuild_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.rebuild_exists

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.rebuild' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.rebuild

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.rebuild_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.rebuild_target

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.rebuildComp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.rebuildComp

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.rebuildComp_target' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.rebuildComp_target

/--
info: 'Hex.RealClosure.Tower.Conversion.Model.cast' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.cast

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.refine_heq' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.refine_heq

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.infinitesimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Conversion.Model.infinitesimal

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.rebuild_infinitesimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Conversion.Model.rebuild_infinitesimal

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.infinitesimalHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Conversion.Model.infinitesimalHom

/-- info: 'Hex.RealClosure.Tower.Conversion.Model.rebuild_rational' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Conversion.Model.rebuild_rational

/-- info: 'Hex.RealClosure.Tower.Model.liftInfinitesimal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.liftInfinitesimal

/-- info: 'Hex.RealClosure.Tower.Model.liftInfinitesimal_X_lt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Model.liftInfinitesimal_X_lt

/-- info: 'Hex.RealClosure.Tower.Model.extend_algebraic_over' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.extend_algebraic_over

/-- info: 'Hex.RealClosure.Tower.Model.extend_field_algebraic_over' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.extend_field_algebraic_over

/-- info: 'Hex.RealClosure.Tower.Model.extend_base_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.extend_base_algebraic

/-- info: 'Hex.RealClosure.Tower.Model.extend_base_field_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.extend_base_field_algebraic

/-- info: 'Hex.RealClosure.Tower.Model.extend_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.extend_embed

/-- info: 'Hex.RealClosure.Tower.Model.extend_base_agree' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.extend_base_agree

/-- info: 'Hex.RealClosure.Tower.Model.extend_base_embed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Model.extend_base_embed
