/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.TowerCoverage
public import HexRealClosureMathlib.RootCollection
public import Mathlib.Data.Quot
public import Mathlib.Algebra.Field.TransferInstance
public import Mathlib.Order.Lattice
public import Mathlib.Algebra.Order.Ring.InjSurj

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {parent : Context registry}

/-- A stored value in a finite validated algebraic tower over a fixed native
coefficient context. The suffix retains every selected descriptor in order. -/
structure Presentation (parent : Context registry) : Type 1 where
  suffix : Suffix parent
  value : suffix.context.Value

variable {K : Type u} [Field K] [LinearOrder K] [DecidableEq K]
variable [IsStrictOrderedRing K] [IsRealClosed K]

/-- Interpret every level using its actual native selected-root model. -/
@[expose] noncomputable def Presentation.denote (a : Presentation parent)
    (model : Model parent K) : K := (model.extend a.suffix).value a.value

/-- Every finite native presentation is algebraic over the entire input field. -/
theorem Presentation.algebraic (a : Presentation parent) (model : Model parent K) :
    IsAlgebraic model.field (a.denote model) := by
  apply model.extend_algebraic_over a.suffix _ a.value
  intro x
  have h := isAlgebraic_algebraMap (A := K) (model.toValue x)
  rw [Subfield.algebraMap_ofSubfield] at h
  change IsAlgebraic model.field ((model.toValue x : model.field) : K) at h
  rwa [model.coe_toValue x] at h

/-- Include a native presentation in the prescribed relative algebraic union. -/
@[expose] noncomputable def Presentation.toUnion (a : Presentation parent)
    (model : Model parent K) : Union.Carrier model.field K :=
  ⟨a.denote model, (Union.mem_iff _).mpr (a.algebraic model)⟩

/-- Any value in an actual root context gives a finite native presentation. -/
def Root.presentation (root : Root parent) (a : root.context.Value) : Presentation parent := by
  cases root with
  | point value => exact ⟨.nil, a⟩
  | selected descriptor extension built =>
    cases built
    exact ⟨.root descriptor .nil, a⟩

theorem Root.presentation_denote (root : Root parent) (a : root.context.Value)
    (model : Model parent K) :
    (root.presentation a).denote model = (root.model model).value a := by
  cases root with
  | point value => rfl
  | selected descriptor extension built => cases built; rfl

/-- Complete native root production covers the union, without selecting an
arbitrary chain or asking callers to supply a root-coverage hypothesis. -/
theorem Presentation.toUnion_surjective (model : Model parent K) :
    Function.Surjective (fun a : Presentation parent => a.toUnion model) := by
  intro x
  obtain ⟨p, out, produced, entry, member, value⟩ := model.union_coverage x
  refine ⟨entry.root.presentation entry.root.value, ?_⟩
  apply Subtype.ext
  exact (entry.root.presentation_denote _ model).trans value

/-- Presentations are identified by their values under the fixed compatible
base interpretation and its actual selected-root extensions. -/
@[expose] def Presentation.setoid (model : Model parent K) : Setoid (Presentation parent) where
  r a b := a.denote model = b.denote model
  iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

/-- The semantic union of all finite native presentations. -/
abbrev Presentation.Quotient (model : Model parent K) : Type 1 :=
  _root_.Quotient (Presentation.setoid model)

/-- The quotient embeds in the relative algebraic union. -/
@[expose] noncomputable def Presentation.inclusion (model : Model parent K) :
    Presentation.Quotient model → Union.Carrier model.field K :=
  _root_.Quotient.lift (fun a => a.toUnion model) (fun _ _ h => Subtype.ext h)

theorem Presentation.inclusion_mk (model : Model parent K) (a : Presentation parent) :
    inclusion model (_root_.Quotient.mk (setoid model) a) = a.toUnion model := rfl

theorem Presentation.inclusion_bijective (model : Model parent K) :
    Function.Bijective (inclusion model) := by
  constructor
  · intro a b
    induction a using _root_.Quotient.inductionOn with
    | h a =>
      induction b using _root_.Quotient.inductionOn with
      | h b =>
        intro same
        apply _root_.Quotient.sound
        exact congrArg Subtype.val same
  · intro x
    obtain ⟨a, value⟩ := toUnion_surjective model x
    exact ⟨_root_.Quotient.mk (setoid model) a, value⟩

/-- Native compatible presentations and the algebraic union have exactly the
same mathematical values. Arithmetic and order are transported through this
equivalence; no field laws are asserted on raw syntax. -/
@[expose] noncomputable def Presentation.equiv (model : Model parent K) :
    Presentation.Quotient model ≃ Union.Carrier model.field K :=
  Equiv.ofBijective (inclusion model) (inclusion_bijective model)

noncomputable instance (model : Model parent K) : Field (Presentation.Quotient model) :=
  (Presentation.equiv model).field

noncomputable instance (model : Model parent K) : DecidableEq (Presentation.Quotient model) :=
  Classical.decEq _

noncomputable instance (model : Model parent K) : LinearOrder (Presentation.Quotient model) :=
  (Presentation.equiv model).linearOrder

/-- The identification preserves the transferred field operations. -/
@[expose] noncomputable def Presentation.ringEquiv (model : Model parent K) :
    Presentation.Quotient model ≃+* Union.Carrier model.field K :=
  (Presentation.equiv model).ringEquiv

noncomputable instance (model : Model parent K) :
    Algebra model.field (Presentation.Quotient model) :=
  ((Presentation.ringEquiv model).symm.toRingHom.comp
    (algebraMap model.field (Union.Carrier model.field K))).toAlgebra

/-- The identification retains the prescribed inclusion of the input field. -/
@[expose] noncomputable def Presentation.algEquiv (model : Model parent K) :
    Presentation.Quotient model ≃ₐ[model.field] Union.Carrier model.field K :=
  { Presentation.ringEquiv model with
    commutes' := fun _ => (Presentation.ringEquiv model).apply_symm_apply _ }

/-- Every identified presentation value is algebraic over the input field,
using its prescribed base map into the quotient. -/
theorem Presentation.value_algebraic (model : Model parent K) (x : Presentation.Quotient model) :
    IsAlgebraic model.field x := by
  have h := (Union.algebraic ((Presentation.algEquiv model) x)).algHom
    (Presentation.algEquiv model).symm.toAlgHom
  simpa only [AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] using h

instance (model : Model parent K) : IsStrictOrderedRing (Presentation.Quotient model) :=
  Function.Injective.isStrictOrderedRing
    (Presentation.ringEquiv model) (map_zero _) (map_one _) (map_add _) (map_mul _)
    Iff.rfl Iff.rfl

/-- The quotient inherits exactly the order of the prescribed ambient union. -/
theorem Presentation.inclusion_lt (model : Model parent K) (a b : Presentation.Quotient model) :
    inclusion model a < inclusion model b ↔ a < b := Iff.rfl

/-- The union of all compatible finite native presentations is real closed. -/
theorem Presentation.realClosed (model : Model parent K) :
    IsRealClosed (Presentation.Quotient model) := by
  let e := Presentation.ringEquiv model
  exact IsRealClosed.of_linearOrderedField
    (fun {x} nonnegative => by
      have mapped : e 0 ≤ e x := nonnegative
      rw [map_zero] at mapped
      obtain ⟨r, square⟩ := Union.square mapped
      refine ⟨e.symm r, e.injective ?_⟩
      rw [map_mul, e.apply_symm_apply]
      exact square)
    (fun {p} odd => by
      have mapped : Odd (p.map e.toRingHom).natDegree := by
        rwa [Polynomial.natDegree_map_eq_of_injective e.injective]
      obtain ⟨x, root⟩ := Union.odd_root mapped
      refine ⟨e.symm x, ?_⟩
      apply e.injective
      change e.toRingHom (p.eval (e.symm x)) = e.toRingHom 0
      rw [map_zero, ← Polynomial.eval₂_at_apply e.toRingHom]
      change p.eval₂ e.toRingHom (e (e.symm x)) = 0
      rw [e.apply_symm_apply]
      simpa only [Polynomial.IsRoot.def, Polynomial.eval_map] using root)

/-- Map a stored finite-tower value to its mathematical class. -/
@[expose] noncomputable def Presentation.toValue (a : Presentation parent)
    (model : Model parent K) : Presentation.Quotient model :=
  _root_.Quotient.mk (Presentation.setoid model) a

/-- Exactly equal denotations, rather than equal raw syntax, define a class. -/
theorem Presentation.toValue_eq (model : Model parent K) (a b : Presentation parent) :
    a.toValue model = b.toValue model ↔ a.denote model = b.denote model :=
  _root_.Quotient.eq

/-- The quotient's prescribed base map is the actual native coefficient value. -/
theorem Presentation.base_value (model : Model parent K) (a : parent.Value) :
    (Presentation.mk (Suffix.nil : Suffix parent) a).toValue model =
      algebraMap model.field (Presentation.Quotient model) (model.toValue a) := by
  apply (Presentation.algEquiv model).injective
  rw [AlgEquiv.commutes]
  apply Subtype.ext
  rfl

/-- Native inclusion through any finite suffix retains the same mathematical class. -/
theorem Presentation.embed_value (model : Model parent K) (suffix : Suffix parent)
    (a : parent.Value) :
    (Presentation.mk suffix (suffix.embed a)).toValue model =
      (Presentation.mk (Suffix.nil : Suffix parent) a).toValue model :=
  (Presentation.toValue_eq model _ _).mpr (model.extend_embed suffix a)

/-- A checked compatible native conversion identifies the old and converted
stored presentations. The actual target model remains aligned with its suffix. -/
theorem Presentation.converted_value (model : Model parent K) (left right : Suffix parent)
    (conversion : Conversion left.context) (target_eq : conversion.context = right.context)
    (realization : Conversion.Model conversion (model.extend left))
    (aligned : HEq realization.target (model.extend right)) (a : left.context.Value) :
    (Presentation.mk right (_root_.cast (congrArg Context.Value target_eq)
      (conversion.value a))).toValue model = (Presentation.mk left a).toValue model := by
  apply (Presentation.toValue_eq model _ _).mpr
  change (model.extend right).value (_root_.cast (congrArg Context.Value target_eq)
    (conversion.value a)) = (model.extend left).value a
  rw [Tower.Model.value_cast target_eq realization.target (model.extend right)
    aligned.symm, realization.value]

theorem Presentation.toValue_zero (model : Model parent K) (suffix : Suffix parent) :
    (Presentation.mk suffix 0).toValue model = 0 := by
  apply (Presentation.ringEquiv model).injective
  rw [map_zero]
  apply Subtype.ext
  exact ((model.extend suffix).zero_iff 0).mpr rfl

theorem Presentation.toValue_one (model : Model parent K) (suffix : Suffix parent) :
    (Presentation.mk suffix 1).toValue model = 1 := by
  apply (Presentation.ringEquiv model).injective
  rw [map_one]
  apply Subtype.ext
  exact (model.extend suffix).one

/-- Actual finite-tower addition descends to the union field. -/
theorem Presentation.toValue_add (model : Model parent K) (suffix : Suffix parent)
    (a b : suffix.context.Value) :
    (Presentation.mk suffix (a + b)).toValue model =
      (Presentation.mk suffix a).toValue model + (Presentation.mk suffix b).toValue model := by
  apply (Presentation.ringEquiv model).injective
  rw [map_add]
  apply Subtype.ext
  exact (model.extend suffix).add a b

/-- Actual finite-tower multiplication descends to the union field. -/
theorem Presentation.toValue_mul (model : Model parent K) (suffix : Suffix parent)
    (a b : suffix.context.Value) :
    (Presentation.mk suffix (a * b)).toValue model =
      (Presentation.mk suffix a).toValue model * (Presentation.mk suffix b).toValue model := by
  apply (Presentation.ringEquiv model).injective
  rw [map_mul]
  apply Subtype.ext
  exact (model.extend suffix).mul a b

theorem Presentation.toValue_neg (model : Model parent K) (suffix : Suffix parent)
    (a : suffix.context.Value) :
    (Presentation.mk suffix (-a)).toValue model = -(Presentation.mk suffix a).toValue model := by
  apply (Presentation.ringEquiv model).injective
  rw [map_neg]
  apply Subtype.ext
  exact (model.extend suffix).neg a

theorem Presentation.toValue_sub (model : Model parent K) (suffix : Suffix parent)
    (a b : suffix.context.Value) :
    (Presentation.mk suffix (a - b)).toValue model =
      (Presentation.mk suffix a).toValue model - (Presentation.mk suffix b).toValue model := by
  apply (Presentation.ringEquiv model).injective
  rw [map_sub]
  apply Subtype.ext
  exact (model.extend suffix).sub a b

/-- Actual total native inversion, including zero, descends to the union field. -/
theorem Presentation.toValue_inv (model : Model parent K) (suffix : Suffix parent)
    (a : suffix.context.Value) :
    (Presentation.mk suffix a⁻¹).toValue model = ((Presentation.mk suffix a).toValue model)⁻¹ := by
  apply (Presentation.ringEquiv model).injective
  rw [map_inv₀]
  apply Subtype.ext
  exact (model.extend suffix).inv a

theorem Presentation.toValue_div (model : Model parent K) (suffix : Suffix parent)
    (a b : suffix.context.Value) :
    (Presentation.mk suffix (a / b)).toValue model =
      (Presentation.mk suffix a).toValue model / (Presentation.mk suffix b).toValue model := by
  apply (Presentation.ringEquiv model).injective
  rw [map_div₀]
  apply Subtype.ext
  exact (model.extend suffix).div a b

theorem Presentation.toValue_nat (model : Model parent K) (suffix : Suffix parent) (n : Nat) :
    (Presentation.mk suffix (n : suffix.context.Value)).toValue model = n := by
  apply (Presentation.ringEquiv model).injective
  rw [map_natCast]
  apply Subtype.ext
  exact (model.extend suffix).nat n

/-- Order uses the actual interpreted native values at any two finite depths. -/
theorem Presentation.toValue_lt (model : Model parent K) (a b : Presentation parent) :
    a.toValue model < b.toValue model ↔ a.denote model < b.denote model := Iff.rfl

/-- Native signs agree with the order on the identified mathematical classes. -/
theorem Presentation.toValue_sign (model : Model parent K) (a : Presentation parent) :
    a.suffix.context.sign a.value = (SignType.sign (a.toValue model) : Int) := by
  rw [(model.extend a.suffix).sign]
  change (SignType.sign ((Presentation.ringEquiv model).toRingHom (a.toValue model)) : Int) = _
  have ordered : StrictMono (Presentation.ringEquiv model).toRingHom := fun _ _ h => h
  exact congrArg (fun s : SignType => (s : Int)) (ordered.sign_comp _)

/-- Any finite list of presentation values occurs together in one actual native
collection. Complete root production supplies the selected algebraic values;
the collection's computed inclusions preserve their order and meanings. -/
theorem Presentation.common_values (model : Model parent K) (values : List (Presentation parent)) :
    ∃ roots : List (Root parent),
      roots.map (fun root => root.denote model) = values.map (fun value => value.denote model) ∧
      ∃ realization : Collection.Model (parent.collect roots) model,
        (parent.collect roots).values.map realization.input.target.value =
          values.map (fun value => value.denote model) := by
  have represented : ∃ roots : List (Root parent),
      roots.map (fun root => root.denote model) = values.map (fun value => value.denote model) := by
    induction values with
    | nil => exact ⟨[], rfl⟩
    | cons value rest ih =>
      obtain ⟨p, out, produced, entry, member, same⟩ :=
        model.algebraic_root (value.denote model) (value.algebraic model)
      obtain ⟨roots, meanings⟩ := ih
      change entry.root.denote model = value.denote model at same
      exact ⟨entry.root :: roots, by simp only [List.map_cons, same, meanings]⟩
  obtain ⟨roots, meanings⟩ := represented
  obtain ⟨realization⟩ := (Context.collect_success model roots).2
  refine ⟨roots, meanings, realization, ?_⟩
  rw [realization.values, Context.collect_sources model, meanings]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Presentation.toUnion_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.toUnion_surjective

/-- info: 'Hex.RealClosure.Tower.Presentation.inclusion_bijective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.inclusion_bijective

/-- info: 'Hex.RealClosure.Tower.Presentation.realClosed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.realClosed

/-- info: 'Hex.RealClosure.Tower.Presentation.toValue_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.toValue_inv

/-- info: 'Hex.RealClosure.Tower.Presentation.toValue_sign' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.toValue_sign

/-- info: 'Hex.RealClosure.Tower.Presentation.common_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.common_values

/-- info: 'Hex.RealClosure.Tower.Presentation.value_algebraic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.value_algebraic

/-- info: 'Hex.RealClosure.Tower.Presentation.converted_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.converted_value

/-- info: 'Hex.RealClosure.Tower.Presentation.base_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.base_value

/-- info: 'Hex.RealClosure.Tower.Presentation.toValue_add' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.toValue_add

/-- info: 'Hex.RealClosure.Tower.Presentation.toValue_mul' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.toValue_mul
