/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.LiveContext
public import HexRealClosureMathlib.TowerInclusion
public import HexRealClosureMathlib.TowerEnlargeOrder

public section

namespace Hex.RealClosure.Tower

open scoped Hex.OrderedFn.Infinitesimal

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {owners : List (Context registry)}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R]
variable {S : Type v} [Field S] [LinearOrder S] [DecidableEq S]
variable [IsStrictOrderedRing S] [IsRealClosed S]

/-- A coherent interpretation of all retained original owners. Each model
uses its actual checked inclusion and the same shared target interpretation. -/
inductive Inclusions.Models {destination : Context registry}
    (target : Tower.Model destination R) :
    {contexts : List (Context registry)} → Inclusions destination contexts → Type (max 1 u) where
  | nil : Inclusions.Models target .nil
  | cons {source : Context registry} {rest : List (Context registry)}
      {head : Inclusion source destination} {tail : Inclusions destination rest}
      (original : Tower.Model source R) (model : Inclusion.Model head original)
      (aligned : model.target = target) (later : Inclusions.Models target tail) :
      Inclusions.Models target (.cons head tail)

/-- Carry all original interpretations through one later checked inclusion.
Every resulting map uses that inclusion's actual common target model. -/
noncomputable def Inclusions.Models.extend {source destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions source contexts}
    {target : Tower.Model source R} (models : Inclusions.Models target maps)
    {next : Inclusion source destination} (following : Inclusion.Model next target) :
    Inclusions.Models following.target (maps.extend next) := by
  induction models with
  | nil => exact .nil
  | cons original model aligned later ih =>
    cases aligned
    exact .cons original (model.comp following) (model.comp_target following) ih

/-- Append one newly registered owner's checked interpretation to the same
common target without changing any earlier original owner. -/
noncomputable def Inclusions.Models.snoc {destination source : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {target : Tower.Model destination R} (models : Inclusions.Models target maps)
    {next : Inclusion source destination} (original : Tower.Model source R)
    (model : Inclusion.Model next original) (aligned : model.target = target) :
    Inclusions.Models target (maps.snoc next) := by
  induction models with
  | nil => exact .cons original model aligned .nil
  | cons previous checked same later ih => exact .cons previous checked same ih

/-- Lift all retained interpretations through one actual ordered embedding. -/
noncomputable def Inclusions.Models.map {destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {target : Tower.Model destination R} (models : Inclusions.Models target maps)
    {L : Type w} [Field L] [LinearOrder L]
    (embedding : R →+* L) (ordered : StrictMono embedding) :
    Inclusions.Models (target.map embedding ordered) maps := by
  induction models with
  | nil => exact .nil
  | cons original model aligned later ih =>
    refine .cons (original.map embedding ordered) (model.map embedding ordered) ?_ ih
    exact (model.map_target embedding ordered).trans
      (congrArg (fun m => m.map embedding ordered) aligned)

/-- Retrieve an original owner's model and its alignment with the actual
common target model. -/
noncomputable def Inclusions.Models.get {destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {target : Tower.Model destination R} (models : Inclusions.Models target maps)
    (index : Fin contexts.length) :
    Σ original : Tower.Model contexts[index] R,
      {model : Inclusion.Model (maps.get index) original // model.target = target} := by
  induction models with
  | nil => nomatch index
  | cons original model aligned later ih =>
    rcases index with ⟨index, valid⟩
    cases index with
    | zero => exact ⟨original, model, aligned⟩
    | succ n => exact ih ⟨n, Nat.lt_of_succ_lt_succ valid⟩

/-- Later inclusion preserves every original owner's model, with the same
order of indices as the immutable owner collection. -/
theorem Inclusions.Models.extend_original {source destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions source contexts}
    {target : Tower.Model source R} (models : Inclusions.Models target maps)
    {next : Inclusion source destination} (following : Inclusion.Model next target)
    (index : Fin contexts.length) :
    ((models.extend following).get index).1 = (models.get index).1 := by
  induction models with
  | nil => nomatch index
  | cons original model aligned later ih =>
    cases aligned
    rcases index with ⟨index, valid⟩
    cases index with
    | zero =>
      simp only [Inclusions.Models.extend, Inclusions.Models.get]
      rfl
    | succ n => exact ih ⟨n, Nat.lt_of_succ_lt_succ valid⟩

/-- Lifting a coherent family retains each original owner with exactly the
same ordered field embedding, in its original index position. -/
theorem Inclusions.Models.map_original {destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {target : Tower.Model destination R} (models : Inclusions.Models target maps)
    {L : Type w} [Field L] [LinearOrder L]
    (embedding : R →+* L) (ordered : StrictMono embedding)
    (index : Fin contexts.length) :
    ((models.map embedding ordered).get index).1 =
      (models.get index).1.map embedding ordered := by
  induction models with
  | nil => nomatch index
  | cons original model aligned later ih =>
    rcases index with ⟨index, valid⟩
    cases index with
    | zero => rfl
    | succ n => exact ih ⟨n, Nat.lt_of_succ_lt_succ valid⟩

/-- Each retained original value has its original interpretation in the one
common target model. -/
theorem Inclusions.Models.value {destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {target : Tower.Model destination R} (models : Inclusions.Models target maps)
    (index : Fin contexts.length) (a : (contexts[index]).Value) :
    target.value ((maps.get index).value a) = (models.get index).1.value a := by
  let entry := models.get index
  exact (congrArg (fun m : Tower.Model destination R =>
    m.value ((maps.get index).value a)) entry.2.property).symm.trans (entry.2.val.value a)

/-- Every polynomial shares its owner's checked coefficient interpretation. -/
theorem Inclusions.Models.polynomial {destination : Context registry}
    {contexts : List (Context registry)} {maps : Inclusions destination contexts}
    {target : Tower.Model destination R} (models : Inclusions.Models target maps)
    (index : Fin contexts.length) (p : (contexts[index]).Poly) :
    HexPolyMathlib.Interpret.interpret target.value target.zero_iff
      ((maps.get index).polynomial p) =
    HexPolyMathlib.Interpret.interpret (models.get index).1.value
      (models.get index).1.zero_iff p := by
  let entry := models.get index
  exact (congrArg (fun m : Tower.Model destination R =>
    HexPolyMathlib.Interpret.interpret m.value m.zero_iff
      ((maps.get index).polynomial p)) entry.2.property).symm.trans (entry.2.val.polynomial p)

/-- Enlarge the actual shared target, retaining its interpretation in an
ordered algebraic ambient over the old field's infinitesimal extension. The
declared base's reference model supplies existence of the native inclusion
laws; every old target value is interpreted through the prescribed ambient
embedding. No root alignment or compatible new-base model is supplied. -/
theorem Shared.enlarge?_model (shared : Shared base owners)
    (witness : Tower.Model (Context.ofBase base) S)
    (old : Tower.Model shared.input.context R)
    (ambient : Ambient (Hex.RationalFn R)) :
    ∃ enlarged : SharedEnlargement shared,
      shared.enlarge? = some enlarged ∧
        Nonempty (Inclusion.Model enlarged.previous (old.liftInfinitesimal ambient)) := by
  cases origin_eq : shared.input.context.origin with
  | pack original suffix source_eq =>
    have packed_eq : BaseContext.PackedContext.pack original = base :=
      (Suffix.origin_base original suffix).symm.trans
        ((congrArg (fun context => context.origin.base) source_eq).trans shared.base_eq)
    have same_base : Context.ofBase base = Context.base original :=
      (congrArg Context.ofBase packed_eq).symm.trans rfl
    have reference : Tower.Model (Context.base original) S := same_base ▸ witness
    obtain ⟨converted, produced, ⟨model⟩⟩ :=
      Context.enlarge?_ambient original suffix source_eq reference old ambient
    have success : shared.enlarge?.isSome = true := by
      rw [shared.enlarge?_isSome, produced]
      rfl
    obtain ⟨enlarged, enlarged_eq⟩ := Option.isSome_iff_exists.mp success
    have same : enlarged.previous.conversion = converted := by
      have exact_conversion := shared.enlarge?_conversion
      rw [enlarged_eq, Option.map_some, produced] at exact_conversion
      exact Option.some.inj exact_conversion
    exact ⟨enlarged, enlarged_eq, ⟨⟨same.symm ▸ model⟩⟩⟩

/-- The collection's parameter is the actual infinitesimal of the prescribed
ambient. Its interpretation and every old value use the same returned model. -/
theorem Shared.enlarge?_parameter (shared : Shared base owners)
    (witness : Tower.Model (Context.ofBase base) S)
    (old : Tower.Model shared.input.context R)
    (ambient : Ambient (Hex.RationalFn R)) :
    ∃ enlarged : SharedEnlargement shared,
      shared.enlarge? = some enlarged ∧
        ∃ model : Inclusion.Model enlarged.previous (old.liftInfinitesimal ambient),
          model.target.value enlarged.parameter = ambient.inclusion Hex.RationalFn.X := by
  cases origin_eq : shared.input.context.origin with
  | pack original suffix source_eq =>
    have packed_eq : BaseContext.PackedContext.pack original = base :=
      (Suffix.origin_base original suffix).symm.trans
        ((congrArg (fun context => context.origin.base) source_eq).trans shared.base_eq)
    have same_base : Context.ofBase base = Context.base original :=
      (congrArg Context.ofBase packed_eq).symm.trans rfl
    have reference : Tower.Model (Context.base original) S := same_base ▸ witness
    obtain ⟨rebuilt, produced, model, _, parameter, _, _⟩ :=
      Context.enlargeWithParameter?_model original suffix source_eq reference old ambient
    have success : shared.enlarge?.isSome = true := by
      have exact_packet := congrArg Option.isSome shared.enlarge?_checked
      simpa only [Option.isSome_map, produced, Option.isSome_some] using exact_packet
    obtain ⟨enlarged, enlarged_eq⟩ := Option.isSome_iff_exists.mp success
    have same : enlarged.checked = rebuilt.enlargement original source_eq := by
      have exact_packet := shared.enlarge?_checked
      rw [enlarged_eq, Option.map_some, produced] at exact_packet
      exact Option.some.inj exact_packet
    let converted : Conversion.Model enlarged.checked.conversion
        (old.liftInfinitesimal ambient) := (congrArg Enlargement.conversion same).symm ▸ model
    have transport : ∀ (packet : Enlargement shared.input.context)
        (h : packet = rebuilt.enlargement original source_eq),
        let transported : Conversion.Model packet.conversion
          (old.liftInfinitesimal ambient) := (congrArg Enlargement.conversion h).symm ▸ model
        transported.target.value packet.parameter = ambient.inclusion Hex.RationalFn.X := by
      intro packet h
      cases h
      exact parameter
    have interpreted : converted.target.value enlarged.checked.parameter =
        ambient.inclusion Hex.RationalFn.X := transport enlarged.checked same
    let inclusion : Inclusion.Model enlarged.previous (old.liftInfinitesimal ambient) :=
      ⟨converted⟩
    refine ⟨enlarged, enlarged_eq, inclusion, ?_⟩
    have aligned : HEq inclusion.target converted.target := inclusion.target_heq
    exact (Tower.Model.value_cast enlarged.context_eq converted.target inclusion.target
      aligned enlarged.checked.parameter).trans interpreted

/-- The shared producer carries all original interpretations into its one
enlarged target. The new parameter and every owner use that same target model. -/
theorem Shared.enlarge?_models (shared : Shared base owners)
    (witness : Tower.Model (Context.ofBase base) S)
    (old : Tower.Model shared.input.context R)
    (models : Inclusions.Models old shared.maps)
    (ambient : Ambient (Hex.RationalFn R)) :
    ∃ enlarged : SharedEnlargement shared,
      shared.enlarge? = some enlarged ∧
        ∃ model : Inclusion.Model enlarged.previous (old.liftInfinitesimal ambient),
          model.target.value enlarged.parameter = ambient.inclusion Hex.RationalFn.X ∧
          (∃ following : Inclusions.Models model.target enlarged.shared.maps,
            ∀ index : Fin owners.length, (following.get index).1 =
              (models.get index).1.liftInfinitesimal ambient) ∧
          ∀ (index : Fin owners.length) (a : (owners[index]).Value),
            model.target.value (enlarged.shared.value index a) =
              Ambient.coefficientHom ambient ((models.get index).1.value a) := by
  obtain ⟨enlarged, produced, model, parameter⟩ :=
    shared.enlarge?_parameter witness old ambient
  refine ⟨enlarged, produced, model, parameter, ?_, ?_⟩
  · let lifted : Inclusions.Models (old.liftInfinitesimal ambient) shared.maps :=
      models.map (Ambient.coefficientHom ambient) (Ambient.coefficientHom_strictMono ambient)
    rw [shared.enlarge?_maps enlarged produced]
    refine ⟨lifted.extend model, ?_⟩
    intro index
    rw [Inclusions.Models.extend_original]
    simpa only [lifted, Model.liftInfinitesimal] using
      models.map_original (Ambient.coefficientHom ambient)
        (Ambient.coefficientHom_strictMono ambient) index
  · intro index a
    rw [shared.enlarge?_value enlarged produced, model.value, Model.liftInfinitesimal_value]
    exact congrArg (Ambient.coefficientHom ambient) (models.value index a)

private theorem sign_cast {left right : Context registry} (same : left = right)
    (a : left.Value) :
    right.sign (_root_.cast (congrArg Context.Value same) a) = left.sign a := by
  cases same
  rfl

private theorem sign_sub_cast {left right : Context registry} (same : left = right)
    (a b : left.Value) :
    right.sign (_root_.cast (congrArg Context.Value same) a -
      _root_.cast (congrArg Context.Value same) b) = left.sign (a - b) := by
  cases same
  rfl

/-- A reference interpretation of the declared base suffices for the shared
producer's native positive parameter, smaller than every old positive value. -/
theorem Shared.enlarge?_ordered (shared : Shared base owners)
    (witness : Tower.Model (Context.ofBase base) S) :
    ∃ enlarged : SharedEnlargement shared,
      shared.enlarge? = some enlarged ∧
        enlarged.shared.input.context.sign enlarged.parameter = 1 ∧
        ∀ a, shared.input.context.sign a = 1 → enlarged.shared.input.context.sign
          (enlarged.parameter - enlarged.previous.value a) = -1 := by
  cases origin_eq : shared.input.context.origin with
  | pack original suffix source_eq =>
    have packed_eq : BaseContext.PackedContext.pack original = base :=
      (Suffix.origin_base original suffix).symm.trans
        ((congrArg (fun context => context.origin.base) source_eq).trans shared.base_eq)
    have same_base : Context.ofBase base = Context.base original :=
      (congrArg Context.ofBase packed_eq).symm.trans rfl
    have reference : Tower.Model (Context.base original) S := same_base ▸ witness
    obtain ⟨checked, produced, positive, small⟩ :=
      Context.enlargeWithParameter?_ordered original suffix source_eq reference
    have success : shared.enlarge?.isSome = true := by
      have exact_packet := congrArg Option.isSome shared.enlarge?_checked
      simpa only [Option.isSome_map, produced, Option.isSome_some] using exact_packet
    obtain ⟨enlarged, enlarged_eq⟩ := Option.isSome_iff_exists.mp success
    have same : enlarged.checked = checked := by
      have exact_packet := shared.enlarge?_checked
      rw [enlarged_eq, Option.map_some, produced] at exact_packet
      exact Option.some.inj exact_packet
    have parameter_sign : enlarged.checked.conversion.context.sign
        enlarged.checked.parameter = 1 := same.symm ▸ positive
    have smaller : ∀ a, shared.input.context.sign a = 1 →
        enlarged.checked.conversion.context.sign
          (enlarged.checked.parameter - enlarged.checked.conversion.value a) = -1 :=
      same.symm ▸ small
    refine ⟨enlarged, enlarged_eq, ?_, ?_⟩
    · exact (sign_cast enlarged.context_eq enlarged.checked.parameter).trans parameter_sign
    · intro a positive_a
      exact (sign_sub_cast enlarged.context_eq enlarged.checked.parameter
        (enlarged.checked.conversion.value a)).trans (smaller a positive_a)

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_model

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_parameter' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_parameter

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_ordered

/-- info: 'Hex.RealClosure.Tower.Inclusions.Models.extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusions.Models.extend

/-- info: 'Hex.RealClosure.Tower.Inclusions.Models.value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusions.Models.value

/-- info: 'Hex.RealClosure.Tower.Inclusions.Models.polynomial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusions.Models.polynomial

/-- info: 'Hex.RealClosure.Tower.Inclusions.Models.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusions.Models.map

/-- info: 'Hex.RealClosure.Tower.Shared.enlarge?_models' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.enlarge?_models

/-- info: 'Hex.RealClosure.Tower.Inclusions.Models.snoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusions.Models.snoc

/-- info: 'Hex.RealClosure.Tower.Inclusions.Models.extend_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusions.Models.extend_original

/-- info: 'Hex.RealClosure.Tower.Inclusions.Models.map_original' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusions.Models.map_original
