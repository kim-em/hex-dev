/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerEnlarge
public import HexRealClosureMathlib.TowerTransport

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
