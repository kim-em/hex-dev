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

/-- Actual checked reencoding identifies the old and refined native values.
The producer's target alignment is discharged by its refinement theorem. -/
theorem Presentation.refined_value (model : Model parent K)
    {descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (a : (parent.adjoin descriptor).context.Value) :
    (Presentation.mk (.root encoding.target .nil)
      (_root_.cast (congrArg Context.Value ((Conversion.refine_spec parent encoding).1.trans
        (congrArg Extension.context (parent.refine encoding).canonical)))
        ((Conversion.refine parent encoding).value a))).toValue model =
      (Presentation.mk (.root descriptor .nil) a).toValue model :=
  Presentation.converted_value model (.root descriptor .nil) (.root encoding.target .nil)
    (Conversion.refine parent encoding) ((Conversion.refine_spec parent encoding).1.trans
      (congrArg Extension.context (parent.refine encoding).canonical))
    (Conversion.Model.refine model encoding) (Conversion.Model.refine_heq model encoding) a

/-- Refining a root and rebuilding every later validated level preserves the
old final value class, using the actual producer's model alignment throughout. -/
theorem Presentation.refined_suffix (model : Model parent K)
    {descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature}
    {head : DensePoly parent.Value} {lower upper : Endpoint parent.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (suffix : Suffix (parent.adjoin descriptor).context)
    (rebuilt : Rebuilt (Conversion.refine parent encoding) suffix)
    (a : suffix.context.Value) :
    let same := (Conversion.refine_spec parent encoding).1.trans
      (congrArg Extension.context (parent.refine encoding).canonical)
    let right : Suffix parent := .root encoding.target (same ▸ rebuilt.suffix)
    (Presentation.mk right (_root_.cast (congrArg Context.Value
      (rebuilt.context_eq.symm.trans (Suffix.cast_context same rebuilt.suffix).symm))
      (rebuilt.result.value a))).toValue model =
        (Presentation.mk (.root descriptor suffix) a).toValue model := by
  dsimp only
  let same := (Conversion.refine_spec parent encoding).1.trans
    (congrArg Extension.context (parent.refine encoding).canonical)
  let first := Conversion.Model.refine model encoding
  exact Presentation.converted_value model (.root descriptor suffix)
    (.root encoding.target (same ▸ rebuilt.suffix)) rebuilt.result
    (rebuilt.context_eq.symm.trans (Suffix.cast_context same rebuilt.suffix).symm)
    (first.rebuild suffix rebuilt)
    ((first.rebuild_target suffix rebuilt).trans
      (Model.extend_heq same first.target (model.adjoin encoding.target)
        (Conversion.Model.refine_heq model encoding) rebuilt.suffix)) a

/-- Prefix a native presentation with an earlier validated suffix. Context
casts remain inside this constructor. -/
@[expose] def Presentation.prepend (first : Suffix parent)
    (a : Presentation first.context) : Presentation parent :=
  ⟨first.append a.suffix,
    _root_.cast (congrArg Context.Value (first.append_context a.suffix).symm) a.value⟩

/-- Prefixing a presentation composes its actual native interpretation. -/
theorem Presentation.prepend_denote (model : Model parent K) (first : Suffix parent)
    (a : Presentation first.context) :
    (a.prepend first).denote model = a.denote (model.extend first) := by
  exact Model.value_cast (first.append_context a.suffix).symm
    ((model.extend first).extend a.suffix) (model.extend (first.append a.suffix))
    (model.extend_append first a.suffix) a.value

/-- Reencode a selected root at any position and retain every reconstructed
later level. The returned presentation includes the original preceding suffix. -/
@[expose] def Presentation.refine (first : Suffix parent)
    {descriptor : SignDet.Descriptor first.context.Value Signature
      first.context.sign first.context.signature}
    {head : DensePoly first.context.Value} {lower upper : Endpoint first.context.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (later : Suffix (first.context.adjoin descriptor).context)
    (rebuilt : Rebuilt (Conversion.refine first.context encoding) later)
    (a : later.context.Value) : Presentation parent :=
  let same := (Conversion.refine_spec first.context encoding).1.trans
    (congrArg Extension.context (first.context.refine encoding).canonical)
  let right : Suffix first.context := .root encoding.target (same ▸ rebuilt.suffix)
  (Presentation.mk right (_root_.cast (congrArg Context.Value
    (rebuilt.context_eq.symm.trans (Suffix.cast_context same rebuilt.suffix).symm))
    (rebuilt.result.value a))).prepend first

/-- Actual refinement at an arbitrary root position preserves the original
presentation class, including all preceding and reconstructed later levels. -/
theorem Presentation.refined_at (model : Model parent K) (first : Suffix parent)
    {descriptor : SignDet.Descriptor first.context.Value Signature
      first.context.sign first.context.signature}
    {head : DensePoly first.context.Value} {lower upper : Endpoint first.context.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (later : Suffix (first.context.adjoin descriptor).context)
    (rebuilt : Rebuilt (Conversion.refine first.context encoding) later)
    (a : later.context.Value) :
    (Presentation.refine first encoding later rebuilt a).toValue model =
      ((Presentation.mk (.root descriptor later) a).prepend first).toValue model := by
  apply (Presentation.toValue_eq model _ _).mpr
  rw [Presentation.refine, Presentation.prepend_denote, Presentation.prepend_denote]
  exact (Presentation.toValue_eq (model.extend first) _ _).mp
    (Presentation.refined_suffix (model.extend first) encoding later rebuilt a)

/-- Reconstruct the requested later levels once and package the actual refined
presentation. Invalid reconstruction is reported at this checked boundary. -/
@[expose] def Presentation.refine? (first : Suffix parent)
    {descriptor : SignDet.Descriptor first.context.Value Signature
      first.context.sign first.context.signature}
    {head : DensePoly first.context.Value} {lower upper : Endpoint first.context.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (later : Suffix (first.context.adjoin descriptor).context)
    (a : later.context.Value) : Option (Presentation parent) :=
  ((Conversion.refine first.context encoding).rebuild? later).map
    (fun rebuilt => Presentation.refine first encoding later rebuilt a)

/-- Valid native refinement succeeds at every position and retains the original
class; no target-alignment or reconstruction witness is supplied by the caller. -/
theorem Presentation.refine?_success (model : Model parent K) (first : Suffix parent)
    {descriptor : SignDet.Descriptor first.context.Value Signature
      first.context.sign first.context.signature}
    {head : DensePoly first.context.Value} {lower upper : Endpoint first.context.Value}
    (encoding : SignDet.Reencoding descriptor head lower upper)
    (later : Suffix (first.context.adjoin descriptor).context) (a : later.context.Value) :
    ∃ result, Presentation.refine? first encoding later a = some result ∧
      result.toValue model = ((Presentation.mk (.root descriptor later) a).prepend first).toValue model := by
  obtain ⟨rebuilt, returned⟩ :=
    (Conversion.Model.refine (model.extend first) encoding).rebuild_exists later
  refine ⟨Presentation.refine first encoding later rebuilt a, ?_,
    Presentation.refined_at model first encoding later rebuilt a⟩
  simp only [Presentation.refine?, returned, Option.map_some]

/-- Executable equality in a common native suffix is precisely equality of
its mathematical value classes. -/
theorem Presentation.equal_spec (model : Model parent K) (suffix : Suffix parent)
    (a b : suffix.context.Value) :
    suffix.context.equal a b = true ↔
      (Presentation.mk suffix a).toValue model = (Presentation.mk suffix b).toValue model := by
  rw [Presentation.toValue_eq]
  rw [(model.extend suffix).equal_spec]
  exact decide_eq_true_iff

/-- If the ambient field is algebraic over the input field, finite native
presentations cover every ambient value. -/
theorem Presentation.denote_surjective (model : Model parent K)
    [Algebra.IsAlgebraic model.field K] :
    Function.Surjective (fun a : Presentation parent => a.denote model) := by
  intro x
  obtain ⟨p, out, produced, entry, member, same⟩ :=
    model.algebraic_root x (Algebra.IsAlgebraic.isAlgebraic x)
  exact ⟨entry.root.presentation entry.root.value,
    (entry.root.presentation_denote _ model).trans same⟩

/-- When the ambient field is algebraic over the prescribed input, the
identification with it preserves both field operations and the original base map. -/
@[expose] noncomputable def Presentation.ambientEquiv (model : Model parent K)
    [Algebra.IsAlgebraic model.field K] : Presentation.Quotient model ≃ₐ[model.field] K :=
  AlgEquiv.ofBijective
    ((Union.inclusion (B := model.field) (R := K)).comp
      (Presentation.algEquiv model).toAlgHom) (by
    constructor
    · exact Subtype.val_injective.comp (Presentation.inclusion_bijective model).1
    · intro x
      obtain ⟨a, same⟩ := Presentation.denote_surjective model x
      exact ⟨a.toValue model, same⟩)

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

/-- Finitely many algebraic ambient values occur together in an actual
validated native suffix. Each step uses the complete native root producer. -/
theorem Presentation.algebraic_values (model : Model parent K) (values : List K)
    (algebraic : ∀ x ∈ values, IsAlgebraic model.field x) :
    ∃ suffix : Suffix parent, ∃ stored : List suffix.context.Value,
      stored.map (model.extend suffix).value = values := by
  induction values generalizing parent with
  | nil => exact ⟨.nil, [], rfl⟩
  | cons x rest ih =>
    obtain ⟨p, out, produced, entry, member, same⟩ :=
      model.algebraic_root x (algebraic x List.mem_cons_self)
    have remaining : ∀ y ∈ rest, IsAlgebraic model.field y :=
      fun y member => algebraic y (List.mem_cons_of_mem x member)
    rcases entry with ⟨root, multiplicity⟩
    cases root with
    | point value =>
      obtain ⟨suffix, stored, meanings⟩ := ih model remaining
      refine ⟨suffix, suffix.embed value :: stored, ?_⟩
      simp only [List.map_cons, model.extend_embed, meanings]
      exact congrArg (fun y => y :: rest) same
    | selected descriptor extension built =>
      cases built
      have included : model.field ≤ (model.adjoin descriptor).field := by
        rintro y ⟨a, ha⟩
        exact ⟨(parent.adjoin descriptor).embed a,
          (model.adjoin_embed descriptor a).trans ha⟩
      let : Algebra model.field (model.adjoin descriptor).field :=
        (Subfield.inclusion included).toAlgebra
      let : IsScalarTower model.field (model.adjoin descriptor).field K :=
        .of_algebraMap_eq fun _ => rfl
      have child : ∀ y ∈ rest, IsAlgebraic (model.adjoin descriptor).field y :=
        fun y member => (remaining y member).extendScalars (Subfield.inclusion included).injective
      obtain ⟨suffix, stored, meanings⟩ := ih (model.adjoin descriptor) child
      refine ⟨.root descriptor suffix,
        suffix.embed (parent.adjoin descriptor).generator :: stored, ?_⟩
      change ((suffix.embed (parent.adjoin descriptor).generator :: stored).map
        ((model.adjoin descriptor).extend suffix).value) = x :: rest
      simp only [List.map_cons, Model.extend_embed, meanings]
      exact congrArg (fun y => y :: rest) same

/-- Presentations at arbitrary finite depths have representatives in one
validated suffix, with the same mathematical classes in the original order. -/
theorem Presentation.common_suffix (model : Model parent K) (values : List (Presentation parent)) :
    ∃ suffix : Suffix parent, ∃ stored : List suffix.context.Value,
      stored.map (fun a => (Presentation.mk suffix a).toValue model) =
        values.map (fun a => a.toValue model) := by
  obtain ⟨suffix, stored, meanings⟩ := Presentation.algebraic_values model
    (values.map (fun a => a.denote model)) (by
      intro x member
      obtain ⟨a, member, rfl⟩ := List.mem_map.mp member
      exact a.algebraic model)
  refine ⟨suffix, stored, ?_⟩
  apply (List.map_injective_iff.mpr (Presentation.inclusion_bijective model).1)
  apply (List.map_injective_iff.mpr Subtype.val_injective)
  simpa only [List.map_map, Function.comp_def, Presentation.inclusion_mk,
    Presentation.toValue, Presentation.toUnion, Presentation.denote] using meanings

/-- Any finite list has an actual native collection whose collected values
denote the same ambient values. Complete root production supplies the algebraic values;
the collection's computed inclusions preserve their order and meanings. -/
theorem Presentation.common_values (model : Model parent K) (values : List (Presentation parent)) :
    ∃ roots : List (Root parent),
      (∀ root ∈ roots, ∃ p : DensePoly parent.Value, ∃ out,
        parent.roots p = .finite out ∧ ∃ entry ∈ out, entry.root = root) ∧
      roots.map (fun root => root.denote model) = values.map (fun value => value.denote model) ∧
      ∃ realization : Collection.Model (parent.collect roots) model,
        (parent.collect roots).values.map realization.input.target.value =
          values.map (fun value => value.denote model) := by
  have represented : ∃ roots : List (Root parent),
      (∀ root ∈ roots, ∃ p : DensePoly parent.Value, ∃ out,
        parent.roots p = .finite out ∧ ∃ entry ∈ out, entry.root = root) ∧
      roots.map (fun root => root.denote model) = values.map (fun value => value.denote model) := by
    induction values with
    | nil => exact ⟨[], fun _ member => False.elim (List.not_mem_nil member), rfl⟩
    | cons value rest ih =>
      obtain ⟨p, out, produced, entry, member, same⟩ :=
        model.algebraic_root (value.denote model) (value.algebraic model)
      obtain ⟨roots, provenance, meanings⟩ := ih
      change entry.root.denote model = value.denote model at same
      refine ⟨entry.root :: roots, ?_, by simp only [List.map_cons, same, meanings]⟩
      intro root present
      rcases List.mem_cons.mp present with equal | present
      · subst root
        exact ⟨p, out, produced, entry, member, rfl⟩
      · exact provenance root present
  obtain ⟨roots, provenance, meanings⟩ := represented
  obtain ⟨realization⟩ := (Context.collect_success model roots).2
  refine ⟨roots, provenance, meanings, realization, ?_⟩
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

/-- info: 'Hex.RealClosure.Tower.Presentation.refined_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.refined_value

/-- info: 'Hex.RealClosure.Tower.Presentation.refined_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.refined_suffix

/-- info: 'Hex.RealClosure.Tower.Presentation.equal_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.equal_spec

/-- info: 'Hex.RealClosure.Tower.Presentation.denote_surjective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.denote_surjective

/-- info: 'Hex.RealClosure.Tower.Presentation.algebraic_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.algebraic_values

/-- info: 'Hex.RealClosure.Tower.Presentation.common_suffix' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.common_suffix

/-- info: 'Hex.RealClosure.Tower.Presentation.ambientEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.ambientEquiv

/-- info: 'Hex.RealClosure.Tower.Presentation.prepend_denote' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.prepend_denote

/-- info: 'Hex.RealClosure.Tower.Presentation.refined_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.refined_at

/-- info: 'Hex.RealClosure.Tower.Presentation.refine?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Presentation.refine?_success
