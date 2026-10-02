/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerEnlarge
public import HexRealClosureMathlib.TowerTransport
public import HexRealClosureMathlib.TowerNaturality

public section

namespace Hex.RealClosure.Tower

universe u

variable {registry : BaseContext.Registry}

/-- A compatible semantic model of the new base extends through the stored
root suffix. Every old value has the same interpretation after conversion. -/
theorem Context.enlarge?_model {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    (target_eq : suffix.context = context)
    {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
    [IsStrictOrderedRing K] [IsRealClosed K]
    (old : Tower.Model (Context.base base) K)
    (model : Conversion.Model (Conversion.infinitesimal base) old) :
    ∃ result : Conversion context, context.enlarge? = some result ∧
      Nonempty (Conversion.Model result (target_eq ▸ old.extend suffix)) := by
  obtain ⟨result, hresult, ⟨preserved⟩⟩ := model.extend_exists suffix
  refine ⟨result.cast target_eq, ?_, ⟨preserved.cast target_eq⟩⟩
  rw [Context.enlarge?_eq base suffix target_eq, hresult]
  rfl

/-- Checked enlargement preserves the canonical interpretation of every
value in a supplied validated root suffix. -/
theorem Context.enlarge?_suffix_model
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
    [IsStrictOrderedRing K] [IsRealClosed K]
    (old : Tower.Model (Context.base base) K)
    (model : Conversion.Model (Conversion.infinitesimal base) old) :
    ∃ result : Conversion suffix.context,
      suffix.context.enlarge? = some result ∧
        Nonempty (Conversion.Model result (old.extend suffix)) := by
  exact Context.enlarge?_model base suffix rfl old model

/-- Checked enlargement preserves an arbitrary lawful old tower model.
Only agreement on the initial base is supplied; agreement at every root
level follows from the actual native operations and descriptor constraints. -/
theorem Context.enlarge?_preserves
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
    [IsStrictOrderedRing K] [IsRealClosed K]
    (initial : Tower.Model (Context.base base) K)
    (old : Tower.Model suffix.context K)
    (compatible : ∀ a, old.value (suffix.embed a) = initial.value a)
    (model : Conversion.Model (Conversion.infinitesimal base) initial) :
    ∃ result : Conversion suffix.context, suffix.context.enlarge? = some result ∧
      Nonempty (Conversion.Model result old) := by
  have identified := initial.extend_unique suffix old compatible
  rw [identified]
  exact Context.enlarge?_suffix_model base suffix initial model

/-- An ordered ambient embedding of any compatible old tower model is
preserved by the actual checked enlargement in the larger real closed field. -/
theorem Context.enlarge?_mapped
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {R : Type u} {K : Type v}
    [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [LinearOrder K] [DecidableEq K] [IsStrictOrderedRing K] [IsRealClosed K]
    (initial : Tower.Model (Context.base base) R) (old : Tower.Model suffix.context R)
    (compatible : ∀ a, old.value (suffix.embed a) = initial.value a)
    (embedding : R →+* K) (ordered : StrictMono embedding)
    (model : Conversion.Model (Conversion.infinitesimal base) (initial.map embedding ordered)) :
    ∃ result : Conversion suffix.context, suffix.context.enlarge? = some result ∧
      Nonempty (Conversion.Model result (old.map embedding ordered)) := by
  apply Context.enlarge?_preserves base suffix (initial.map embedding ordered)
    (old.map embedding ordered) _ model
  intro a
  change embedding (old.value (suffix.embed a)) = embedding (initial.value a)
  rw [compatible]

open scoped Hex.OrderedFn.Infinitesimal in
/-- An arbitrary old model extends through checked enlargement in an actual
ordered algebraic ambient over its infinitesimal rational-function field.
The source base interpretation is extracted from the old model; no agreement
at later roots or compatible new-base model is supplied by the caller. -/
theorem Context.enlarge?_ambient
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
    [IsStrictOrderedRing R] [IsRealClosed R]
    (reference : Tower.Model (Context.base base) R)
    (old : Tower.Model suffix.context R)
    (ambient : Ambient (Hex.RationalFn R)) :
    ∃ result : Conversion suffix.context, suffix.context.enlarge? = some result ∧
      Nonempty (Conversion.Model result (old.liftInfinitesimal ambient)) := by
  letI : DecidableEq ambient.Carrier := Classical.decEq _
  let initial := reference.pullback (reference.extend suffix) old suffix.embed
    (reference.extend_embed suffix)
  let f := initial.baseHom base
  have hsign : ∀ a, sign a = (SignType.sign (f a) : Int) := by
    intro a
    exact initial.sign (⟨a⟩ : BaseContext.Element base)
  let model := Conversion.Model.infinitesimalMapped base f hsign ambient
  have same : Tower.Model.base base ((Ambient.coefficientHom ambient).comp f)
      (Conversion.Model.mapped_base_sign f hsign ambient) =
        initial.map (Ambient.coefficientHom ambient)
          (Ambient.coefficientHom_strictMono ambient) := by
    apply Tower.Model.value_ext
    intro a
    change BaseContext.Element base at a
    rw [Tower.Model.base_value base ((Ambient.coefficientHom ambient).comp f)
      (Conversion.Model.mapped_base_sign f hsign ambient) a]
    change Ambient.coefficientHom ambient (f a.stored) =
      Ambient.coefficientHom ambient (initial.value a)
    exact congrArg (Ambient.coefficientHom ambient) (Tower.Model.baseHom_value base initial a)
  have converted : Conversion.Model (Conversion.infinitesimal base)
      (initial.map (Ambient.coefficientHom ambient)
        (Ambient.coefficientHom_strictMono ambient)) := same ▸ model
  exact Context.enlarge?_mapped base suffix initial old (fun _ => rfl)
    (Ambient.coefficientHom ambient) (Ambient.coefficientHom_strictMono ambient) converted

/-- The checked result uses the supplied enlarged base interpretation and
the actual rebuilt descriptors at every later root. -/
theorem Context.enlarge?_aligned
    {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    (target_eq : suffix.context = context)
    {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
    [IsStrictOrderedRing K] [IsRealClosed K]
    (old : Tower.Model (Context.base base) K)
    (model : Conversion.Model (Conversion.infinitesimal base) old) :
    ∃ rebuilt : Rebuilt (Conversion.infinitesimal base) suffix,
      (Conversion.infinitesimal base).rebuild? suffix = some rebuilt ∧
        context.enlarge? = some (rebuilt.result.cast target_eq) ∧
        ∃ witness : Conversion.Model (rebuilt.result.cast target_eq)
            (target_eq ▸ old.extend suffix),
          HEq witness.target (model.target.extend rebuilt.suffix) := by
  obtain ⟨rebuilt, hrebuilt⟩ := model.rebuild_exists suffix
  have hresult : (Conversion.infinitesimal base).extend? suffix =
      some rebuilt.result := by
    rw [← Conversion.rebuild_result, hrebuilt]
    rfl
  have henlarge : context.enlarge? = some (rebuilt.result.cast target_eq) := by
    rw [Context.enlarge?_eq base suffix target_eq, hresult]
    rfl
  let witness := (model.extend suffix rebuilt.result hresult).cast target_eq
  have halign : HEq witness.target (model.target.extend rebuilt.suffix) :=
    (model.extend suffix rebuilt.result hresult).cast_target target_eq |>.trans
      (model.extend_target suffix rebuilt hrebuilt hresult)
  exact ⟨rebuilt, hrebuilt, henlarge,
    ⟨witness, halign⟩⟩

/-- A sign-compatible interpretation of the extracted staged base makes
checked enlargement succeed for its stored root suffix. -/
theorem Context.enlarge?_exists {context : Context registry}
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    (target_eq : suffix.context = context)
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq R]
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* R)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int)) :
    ∃ result : Conversion context, context.enlarge? = some result := by
  let model := Conversion.Model.infinitesimalMapped base f hsign
    (Ambient.infinitesimal R)
  obtain ⟨result, hresult, _⟩ :=
    Context.enlarge?_model base suffix target_eq _ model
  exact ⟨result, hresult⟩

/-- Checked enlargement succeeds at any finite algebraic depth over a staged
base with a sign-compatible ordered-field interpretation. -/
theorem Context.enlarge?_suffix
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (base : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base base))
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [DecidableEq R]
    (f : letI : Field B := HexPolyMathlib.fieldOfGrind; B →+* R)
    (hsign : ∀ a, sign a = (SignType.sign (f a) : Int)) :
    ∃ result : Conversion suffix.context,
      suffix.context.enlarge? = some result := by
  let model := Conversion.Model.infinitesimalMapped base f hsign
    (Ambient.infinitesimal R)
  obtain ⟨result, hresult, _⟩ :=
    Context.enlarge?_suffix_model base suffix _ model
  exact ⟨result, hresult⟩

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_model

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_suffix_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_suffix_model

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_aligned' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_aligned

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_exists' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_exists

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_suffix

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_preserves' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_preserves

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_mapped' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_mapped

/-- info: 'Hex.RealClosure.Tower.Context.enlarge?_ambient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Hex.RealClosure.Tower.Context.enlarge?_ambient
