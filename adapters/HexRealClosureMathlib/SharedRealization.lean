/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.NativeRealization
public import HexRealClosureMathlib.LiveRequest
public import HexRealClosureMathlib.TransportInventory
public import HexRealClosureMathlib.ModelInventory

public section

open scoped List
open scoped Hex.OrderedFn.Infinitesimal

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}
variable {K : Type} [Field K] [LinearOrder K] [DecidableEq K]

namespace Inclusion.Model

variable {source target : Context registry} {inclusion : Inclusion source target}
variable {original : Tower.Model source K} (model : Inclusion.Model inclusion original)

/-- The original value field is included in the actual shared target field.
Membership uses the retained native inclusion, including its selected roots. -/
noncomputable def fieldHom : original.field →+* model.target.field :=
  Subfield.inclusion (by
    rintro a ⟨value, rfl⟩
    exact ⟨inclusion.value value, model.value value⟩)

omit [DecidableEq K] in
/-- The field inclusion agrees with the executable map on every stored value. -/
theorem fieldHom_value (a : source.Value) :
    model.fieldHom (original.toValue a) = model.target.toValue (inclusion.value a) := by
  apply Subtype.ext
  exact (model.value a).symm

/-- Restrict the same ordinary reader to an original owner. This is agreement
of total readers, including the fallback outside their common domain. -/
theorem read_comap (interpretation : CoefficientMap model.target.field ℝ) (a : source.Value) :
    original.read (interpretation.comap model.fieldHom) a =
      model.target.read interpretation (inclusion.value a) := by
  rw [Tower.Model.read_apply, CoefficientMap.comap_map, model.fieldHom_value,
    Tower.Model.read_apply]

/-- Owner membership is exactly membership of its transported semantic value. -/
theorem domain_comap (interpretation : CoefficientMap model.target.field ℝ) (a : source.Value) :
    original.domain (interpretation.comap model.fieldHom) a ↔
      model.target.domain interpretation (inclusion.value a) := by
  rw [Tower.Model.domain_iff, CoefficientMap.comap_domain, model.fieldHom_value,
    Tower.Model.domain_iff]

end Inclusion.Model

variable {base : BaseContext.PackedContext registry} {owners : List (Context registry)}

omit [DecidableEq K] in
private theorem read_zero [IsStrictOrderedRing K] {context : Context registry}
    (model : Tower.Model context K) (interpretation : CoefficientMap model.field ℝ)
    (a : context.Value) (domain : model.domain interpretation a)
    (sign : (SignType.sign (model.read interpretation a) : Int) = context.sign a) :
    model.read interpretation a = 0 ↔ a = 0 := by
  have data := model.inventory_agreement interpretation [a]
    (fun x member => by cases List.mem_singleton.mp member; exact domain)
    (fun x member => by cases List.mem_singleton.mp member; exact sign)
  exact (data a (List.mem_singleton.mpr rfl)).2.2

/-- The finite images of every owner's requested operands, in request order. -/
def Shared.inventory (shared : Shared base owners)
    (values : (index : Fin owners.length) → List (owners[index]).Value) :
    List shared.input.context.Value :=
  (List.finRange owners.length).flatMap fun index => (values index).map (shared.value index)

theorem Shared.mem_inventory (shared : Shared base owners)
    (values : (index : Fin owners.length) → List (owners[index]).Value)
    (index : Fin owners.length) (a : (owners[index]).Value) (member : List.Mem a (values index)) :
    shared.value index a ∈ shared.inventory values := by
  apply List.mem_flatMap.mpr
  exact ⟨index, List.mem_finRange index, List.mem_map.mpr ⟨a, member, rfl⟩⟩

namespace Shared.Model

variable [IsStrictOrderedRing K] [IsRealClosed K]

variable {shared : Shared base owners} {following : base.Realization}
variable {reference : Tower.Model (Context.ofBase base) K}
variable (model : Shared.Model shared following reference)

/-- All original value fields enter the same target through their factory maps. -/
noncomputable def ownerHom (index : Fin owners.length) :
    (model.owners.get index).1.field →+* model.target.field :=
  Subfield.inclusion (by
    rintro a ⟨value, rfl⟩
    exact ⟨shared.value index value, model.value index value⟩)

theorem ownerHom_value (index : Fin owners.length) (a : (owners[index]).Value) :
    model.ownerHom index ((model.owners.get index).1.toValue a) =
      model.target.toValue (shared.value index a) := by
  apply Subtype.ext
  exact (model.value index a).symm

/-- Every original owner uses the restriction of one ordinary interpretation. -/
noncomputable def ownerRead (interpretation : CoefficientMap model.target.field ℝ)
    (index : Fin owners.length) : (owners[index]).Value → ℝ :=
  (model.owners.get index).1.read (interpretation.comap (model.ownerHom index))

def ownerDomain (interpretation : CoefficientMap model.target.field ℝ)
    (index : Fin owners.length) : (owners[index]).Value → Prop :=
  (model.owners.get index).1.domain (interpretation.comap (model.ownerHom index))

theorem ownerRead_apply (interpretation : CoefficientMap model.target.field ℝ)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    model.ownerRead interpretation index a =
      model.target.read interpretation (shared.value index a) := by
  unfold ownerRead
  rw [Tower.Model.read_apply, CoefficientMap.comap_map, model.ownerHom_value,
    Tower.Model.read_apply]

theorem ownerDomain_iff (interpretation : CoefficientMap model.target.field ℝ)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    model.ownerDomain interpretation index a ↔
      model.target.domain interpretation (shared.value index a) := by
  unfold ownerDomain
  rw [Tower.Model.domain_iff, CoefficientMap.comap_domain, model.ownerHom_value,
    Tower.Model.domain_iff]

/-- Original arithmetic is preserved on the pulled-back domain, even though
native inclusions need not preserve unreduced syntax literally. -/
theorem owner_closed (interpretation : CoefficientMap model.target.field ℝ)
    (index : Fin owners.length) :
    Transport.Closed (model.ownerRead interpretation index)
      (model.ownerDomain interpretation index) :=
  (model.owners.get index).1.closed _

/-- Simultaneously realize all finite original-owner requests in one ordinary
interpretation. Canonical owner models, arithmetic domains and sign agreement
come from the actual gather factory. No independent owner realization or
caller-supplied agreement is used. This is relative semantic specialization,
not the direct accepted finite-replay exporter contract. -/
theorem realize (values : (index : Fin owners.length) → List (owners[index]).Value)
    (extra : List shared.input.context.Value := []) :
    ∃ interpretation : CoefficientMap model.target.field ℝ,
      (∀ index, Transport.Closed (model.ownerRead interpretation index)
        (model.ownerDomain interpretation index)) ∧
      (∀ index a, a ∈ values index →
        model.ownerDomain interpretation index a ∧
          (SignType.sign (model.ownerRead interpretation index a) : Int) = (owners[index]).sign a) ∧
      (∀ a ∈ extra, model.target.domain interpretation a ∧
        (SignType.sign (model.target.read interpretation a) : Int) = shared.input.context.sign a) ∧
      (∀ i j a b, model.target.value (shared.value i a) = model.target.value (shared.value j b) →
        model.ownerRead interpretation i a = model.ownerRead interpretation j b) ∧
      (∀ a r, shared.input.context.origin.RealValue (shared.base_eq.symm ▸ following) a r →
        model.target.domain interpretation a ∧ model.target.read interpretation a = r) := by
  obtain ⟨interpretation, finite, real⟩ :=
    shared.input.context.realize (shared.base_eq.symm ▸ following) model.target
      (shared.inventory values ++ extra)
  refine ⟨interpretation, model.owner_closed interpretation, ?_, ?_, ?_, real⟩
  · intro index a member
    obtain ⟨domain, sign⟩ := finite _
      (List.mem_append_left _ (shared.mem_inventory values index a member))
    refine ⟨(model.ownerDomain_iff interpretation index a).mpr domain, ?_⟩
    rw [model.ownerRead_apply]
    exact sign.trans ((model.owners.get index).2.val.sign a)
  · intro a member
    exact finite a (List.mem_append_right _ member)
  · intro i j a b same
    rw [model.ownerRead_apply, model.ownerRead_apply, Tower.Model.read_apply,
      Tower.Model.read_apply, (model.target.toValue_equal _ _).mpr same]

end Shared.Model

/-- Realize an actual native gather without a supplied ambient model. Every
owner uses the same ordinary reader through its retained checked inclusion.
Arithmetic holds on the pulled-back domains; mathematical equality and all
requested signs are coherent across owners. -/
theorem Shared.realize_values (shared : Shared base owners) (following : base.Realization)
    (produced : Shared.gather? base owners = some shared)
    (values : (index : Fin owners.length) → List (owners[index]).Value) :
    ∃ read : shared.input.context.Value → ℝ, ∃ domain : shared.input.context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ index, Transport.Closed (fun a => read (shared.value index a))
        (fun a => domain (shared.value index a))) ∧
      (∀ index a, a ∈ values index → domain (shared.value index a) ∧
        (SignType.sign (read (shared.value index a)) : Int) = (owners[index]).sign a ∧
        (read (shared.value index a) = 0 ↔ a = 0)) ∧
      (∀ i j a b, shared.input.context.equal (shared.value i a) (shared.value j b) = true →
        read (shared.value i a) = read (shared.value j b)) ∧
      (∀ a r, shared.input.context.origin.RealValue (shared.base_eq.symm ▸ following) a r →
        domain a ∧ read a = r) := by
  classical
  let reference := following.reference
  let model := Shared.Model.ofGather following reference.model owners shared produced
  obtain ⟨interpretation, closed, finite, _, coherent, real⟩ := model.realize values
  refine ⟨model.target.read interpretation, model.target.domain interpretation,
    model.target.closed interpretation, ?_, ?_, ?_, real⟩
  · intro index
    have reads : model.ownerRead interpretation index =
        fun a => model.target.read interpretation (shared.value index a) :=
      funext (model.ownerRead_apply interpretation index)
    have domains : model.ownerDomain interpretation index =
        fun a => model.target.domain interpretation (shared.value index a) :=
      funext fun a => propext (model.ownerDomain_iff interpretation index a)
    rw [← reads, ← domains]
    exact closed index
  · intro index a member
    obtain ⟨domain, sign⟩ := finite index a member
    exact ⟨(model.ownerDomain_iff interpretation index a).mp domain,
      (model.ownerRead_apply interpretation index a) ▸ sign, by
        rw [← model.ownerRead_apply]
        exact read_zero (model.owners.get index).1 _ a domain sign⟩
  · intro i j a b equal
    rw [model.target.equal_spec] at equal
    have same := of_decide_eq_true equal
    simpa only [model.ownerRead_apply] using coherent i j a b same

namespace Live

/-- Every requested value and polynomial coefficient, together with every
coefficient reached by the retained descriptor's actual finite replay. -/
@[expose] def Frame.inventory {owner : Context registry} (frame : Frame owner) : List owner.Value :=
  frame.values ++ frame.polynomials.flatMap Transport.Inventory.coefficients ++
    frame.descriptors.flatMap fun descriptor =>
      Transport.Inventory.descriptor descriptor.raw descriptor.evidence

/-- Enumerate original operands at the exact positions retained by gathering. -/
@[expose] def Request.inventory (request : Request registry) (index : Fin request.owners.length) :
    List (request.owners[index]).Value :=
  (request.frame ⟨index.val, by simpa only [Request.owners, List.length_map] using index.isLt⟩).inventory

/-- One ordinary reader simultaneously preserves the full finite operand and
replay inventories of an actual gathered collection. Domains and arithmetic
are pulled back through its original owner maps; caller provider coefficients
stay fixed. The symbolic reference is constructed internally. -/
theorem Collection.realize {request : Request registry} (collection : Collection base request)
    (following : base.Realization) (produced : request.gather? base = some collection) :
    ∃ read : collection.shared.input.context.Value → ℝ,
      ∃ domain : collection.shared.input.context.Value → Prop,
      Transport.Closed read domain ∧
      (∀ index, Transport.Closed (fun a => read (collection.shared.value index a))
        (fun a => domain (collection.shared.value index a))) ∧
      (∀ index a, a ∈ request.inventory index → domain (collection.shared.value index a) ∧
        (SignType.sign (read (collection.shared.value index a)) : Int) =
          (request.owners[index]).sign a ∧
        (read (collection.shared.value index a) = 0 ↔ a = 0)) ∧
      (∀ i j a b, collection.shared.input.context.equal
          (collection.shared.value i a) (collection.shared.value j b) = true →
        read (collection.shared.value i a) = read (collection.shared.value j b)) ∧
      (∀ a r, collection.shared.input.context.origin.RealValue
          (collection.shared.base_eq.symm ▸ following) a r → domain a ∧ read a = r) :=
  collection.shared.realize_values following
    (Request.gather?_shared base request collection produced) request.inventory

/-- Specialize an actual enlargement at one ordinary interpretation for its
original owner inventories, requested old and fresh values and new parameter.
The old reader is the pullback through the returned predecessor inclusion.
The previous canonical model can come from gathering or any earlier enlargement.
The next infinitesimal ambient is constructed internally; this remains the
relative semantic route. -/
theorem Enlargement.realize_model [IsStrictOrderedRing K] [IsRealClosed K]
    {request : Request registry} {original : Collection base request}
    {following : base.Realization} {reference : Tower.Model (Context.ofBase base) K}
    (result : Enlargement original) (old : Shared.Model original.shared following reference)
    (produced : original.enlarge? = some result)
    (values : List original.shared.input.context.Value)
    (fresh : List result.collection.shared.input.context.Value := []) :
    ∃ read : result.collection.shared.input.context.Value → ℝ,
      ∃ domain : result.collection.shared.input.context.Value → Prop,
      Transport.Closed read domain ∧
      Transport.Closed (fun a => read (result.previous.value a))
        (fun a => domain (result.previous.value a)) ∧
      (∀ a ∈ values, domain (result.previous.value a) ∧
        (SignType.sign (read (result.previous.value a)) : Int) = original.shared.input.context.sign a) ∧
      (∀ index a, a ∈ request.inventory index →
        domain (result.collection.shared.value index a) ∧
        (SignType.sign (read (result.collection.shared.value index a)) : Int) =
          (request.owners[index]).sign a ∧
        (read (result.collection.shared.value index a) = 0 ↔ a = 0)) ∧
      (∀ a ∈ fresh, domain a ∧
        (SignType.sign (read a) : Int) = result.collection.shared.input.context.sign a ∧
        (read a = 0 ↔ a = 0)) ∧
      (∀ a b, result.collection.shared.input.context.equal a b = true → read a = read b) ∧
      (∀ a r, result.collection.shared.input.context.origin.RealValue
        (result.collection.shared.base_eq.symm ▸ following.infinitesimal) a r →
        domain a ∧ read a = r) ∧
      domain result.parameter ∧
      0 < read result.parameter := by
  classical
  let ambient := Ambient.ofField (Hex.RationalFn K)
  let returned := result.model old ambient produced
  have parameterSign : result.collection.shared.input.context.sign result.parameter = 1 := by
    rw [returned.target.sign]
    change (SignType.sign ((result.model old ambient produced).target.value result.parameter) : Int) = 1
    rw [result.model_parameter old ambient produced, ambient.inclusion_sign]
    simp [Hex.OrderedFn.Infinitesimal.X_pos]
  obtain ⟨previous, aligned⟩ := result.model_previous old ambient produced
  let lifted := old.target.liftInfinitesimal ambient
  have preserved (a : original.shared.input.context.Value) :
      returned.target.value (result.previous.value a) = lifted.value a := by
    rw [← aligned]
    exact previous.value a
  let embedding : lifted.field →+* returned.target.field :=
    Subfield.inclusion (by
      rintro a ⟨value, rfl⟩
      exact ⟨result.previous.value value, preserved value⟩)
  have embeddingValue (a : original.shared.input.context.Value) :
      embedding (lifted.toValue a) = returned.target.toValue (result.previous.value a) :=
    Subtype.ext (preserved a).symm
  let extra := values.map result.previous.value ++ result.parameter :: fresh
  obtain ⟨interpretation, _, finite, additional, _, real⟩ := returned.realize request.inventory extra
  have reads : lifted.read (interpretation.comap embedding) =
      fun a => returned.target.read interpretation (result.previous.value a) := by
    funext a
    rw [Tower.Model.read_apply, CoefficientMap.comap_map, embeddingValue, Tower.Model.read_apply]
  have domains : lifted.domain (interpretation.comap embedding) =
      fun a => returned.target.domain interpretation (result.previous.value a) := by
    funext a
    apply propext
    rw [Tower.Model.domain_iff, CoefficientMap.comap_domain, embeddingValue, Tower.Model.domain_iff]
  refine ⟨returned.target.read interpretation, returned.target.domain interpretation,
    returned.target.closed interpretation, ?_, ?_, ?_, ?_, ?_, real, ?_, ?_⟩
  · rw [← reads, ← domains]
    exact lifted.closed _
  · intro a member
    obtain ⟨domain, sign⟩ := additional _
      (List.mem_append_left _ (List.mem_map.mpr ⟨a, member, rfl⟩))
    exact ⟨domain, sign.trans (previous.sign a)⟩
  · intro index a member
    obtain ⟨domain, sign⟩ := finite index a member
    exact ⟨(returned.ownerDomain_iff interpretation index a).mp domain,
      (returned.ownerRead_apply interpretation index a) ▸ sign, by
        rw [← returned.ownerRead_apply]
        exact read_zero (returned.owners.get index).1 _ a domain sign⟩
  · intro a member
    obtain ⟨domain, sign⟩ := additional a
      (List.mem_append_right _ (List.mem_cons_of_mem _ member))
    exact ⟨domain, sign, read_zero returned.target interpretation a domain sign⟩
  · intro a b equal
    rw [returned.target.equal_spec] at equal
    rw [Tower.Model.read_apply, Tower.Model.read_apply,
      (returned.target.toValue_equal a b).mpr (of_decide_eq_true equal)]
  · exact (additional result.parameter
      (List.mem_append_right _ (List.mem_cons_self ..))).1
  · have sign := (additional result.parameter
      (List.mem_append_right _ (List.mem_cons_self ..))).2
    rw [parameterSign] at sign
    have realSign : SignType.sign (returned.target.read interpretation result.parameter) = 1 := by
      cases value : SignType.sign (returned.target.read interpretation result.parameter) <;> simp_all
    exact sign_eq_one_iff.mp realSign

/-- Specialize an actual first enlargement without a caller-supplied model.
The canonical starting model is constructed from the actual gather and provider
history. Further enlargements use `realize_model` with their factory models. -/
theorem Enlargement.realize {request : Request registry} {original : Collection base request}
    (result : Enlargement original) (following : base.Realization)
    (gathered : request.gather? base = some original)
    (produced : original.enlarge? = some result)
    (values : List original.shared.input.context.Value)
    (fresh : List result.collection.shared.input.context.Value := []) :
    ∃ read : result.collection.shared.input.context.Value → ℝ,
      ∃ domain : result.collection.shared.input.context.Value → Prop,
      Transport.Closed read domain ∧
      Transport.Closed (fun a => read (result.previous.value a))
        (fun a => domain (result.previous.value a)) ∧
      (∀ a ∈ values, domain (result.previous.value a) ∧
        (SignType.sign (read (result.previous.value a)) : Int) = original.shared.input.context.sign a) ∧
      (∀ index a, a ∈ request.inventory index →
        domain (result.collection.shared.value index a) ∧
        (SignType.sign (read (result.collection.shared.value index a)) : Int) =
          (request.owners[index]).sign a ∧
        (read (result.collection.shared.value index a) = 0 ↔ a = 0)) ∧
      (∀ a ∈ fresh, domain a ∧
        (SignType.sign (read a) : Int) = result.collection.shared.input.context.sign a ∧
        (read a = 0 ↔ a = 0)) ∧
      (∀ a b, result.collection.shared.input.context.equal a b = true → read a = read b) ∧
      (∀ a r, result.collection.shared.input.context.origin.RealValue
        (result.collection.shared.base_eq.symm ▸ following.infinitesimal) a r →
        domain a ∧ read a = r) ∧
      domain result.parameter ∧
      0 < read result.parameter := by
  classical
  let reference := following.reference
  let old := original.model following reference.model gathered
  exact result.realize_model old produced values fresh

end Live

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Inclusion.Model.fieldHom' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.Model.fieldHom

/-- info: 'Hex.RealClosure.Tower.Inclusion.Model.read_comap' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.Model.read_comap

/-- info: 'Hex.RealClosure.Tower.Shared.Model.realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.realize

/-- info: 'Hex.RealClosure.Tower.Shared.realize_values' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.realize_values

/-- info: 'Hex.RealClosure.Tower.Live.Collection.realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Collection.realize

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.realize

/-- info: 'Hex.RealClosure.Tower.Live.Enlargement.realize_model' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.Enlargement.realize_model
