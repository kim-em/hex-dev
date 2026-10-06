/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.SharedPresentation
public import HexRealClosureMathlib.CacheGather
public import HexRealClosureMathlib.Presentation

public section

open scoped List

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {R : Type u} [Field R] [LinearOrder R] [DecidableEq R]
variable [IsStrictOrderedRing R] [IsRealClosed R]
variable {reader : OwnerReader registry R}

private theorem Origin.presentation_denote {context : Context registry}
    (origin : Origin context) (sameBase : origin.base = base)
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R)
    (target : Tower.Model context R)
    (produced : origin.model? following reference = some target) (a : context.Value) :
    (_root_.cast (congrArg (fun base => Presentation (Context.ofBase base)) sameBase)
      (origin.presentation a)).denote reference = target.value a := by
  cases origin with
  | pack original suffix same =>
    change BaseContext.PackedContext.pack original = base at sameBase
    cases sameBase
    cases same
    have factory := Origin.model?_pack original suffix rfl following reference
    have baseFactory : (Context.base original).model? following reference = some reference :=
      Context.model?_base following reference
    rw [baseFactory] at factory
    dsimp only [Option.map] at factory
    rw [produced] at factory
    have aligned := Option.some.inj factory
    change (reference.extend suffix).value a = target.value a
    rw [aligned]
    rfl

/-- The target presentation interprets every actual computed shared value. -/
theorem Shared.Model.targetPresentation_denote {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    [reader.Agrees following reference]
    (model : Shared.Model (reader := reader) shared following reference) (a : shared.input.context.Value) :
    (shared.targetPresentation a).denote reference = model.target.value a := by
  have produced := model.canonical
  rw [OwnerReader.Agrees.read_eq (following := following) (reference := reference) shared.input.context shared.base_eq] at produced
  rw [Context.model?_origin] at produced
  exact shared.input.context.origin.presentation_denote shared.base_eq following reference
    model.target produced a

/-- A gathered owner's finite presentation has exactly its original value in
all canonical selected-root extensions of the declared base interpretation. -/
theorem Shared.Model.presentation_denote {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    [reader.Agrees following reference]
    (model : Shared.Model (reader := reader) shared following reference)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    (shared.presentation index a).denote reference = (model.owners.get index).1.value a := by
  exact (model.targetPresentation_denote (shared.value index a)).trans (model.value index a)

/-- Map any actual computed shared value to the prescribed algebraic union. -/
@[expose] noncomputable def Shared.targetToUnion {owners : List (Context registry)}
    (shared : Shared base owners) (reference : Tower.Model (Context.ofBase base) R)
    (a : shared.input.context.Value) : Union.Carrier reference.field R :=
  (shared.targetPresentation a).toUnion reference

/-- The target union map uses the canonical selected-root interpretation. -/
theorem Shared.Model.targetToUnion_value {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    [reader.Agrees following reference]
    (model : Shared.Model (reader := reader) shared following reference) (a : shared.input.context.Value) :
    (shared.targetToUnion reference a : R) = model.target.value a :=
  model.targetPresentation_denote a

/-- The target map is the prescribed algebraic equivalence on native classes. -/
theorem Shared.algEquiv_target {owners : List (Context registry)}
    (shared : Shared base owners) (reference : Tower.Model (Context.ofBase base) R)
    (a : shared.input.context.Value) :
    Presentation.algEquiv reference ((shared.targetPresentation a).toValue reference) =
      shared.targetToUnion reference a := rfl

/-- A gathered value enters the prescribed algebraic union through its actual
finite native presentation, retaining its selected embedding. -/
@[expose] noncomputable def Shared.Model.toUnion {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    {reader : OwnerReader registry R}
    (_model : Shared.Model (reader := reader) shared following reference)
    (index : Fin owners.length) (a : (owners[index]).Value) : Union.Carrier reference.field R :=
  (shared.presentation index a).toUnion reference

/-- The union value is the original owner's interpreted value. -/
theorem Shared.Model.toUnion_value {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    [reader.Agrees following reference]
    (model : Shared.Model (reader := reader) shared following reference)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    (model.toUnion index a : R) = (model.owners.get index).1.value a :=
  model.presentation_denote index a

/-- The owner map is the algebraic equivalence on its actual native class. -/
theorem Shared.Model.algEquiv_toValue {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    [reader.Agrees following reference]
    (model : Shared.Model (reader := reader) shared following reference)
    (index : Fin owners.length) (a : (owners[index]).Value) :
    Presentation.algEquiv reference ((shared.presentation index a).toValue reference) =
      model.toUnion index a := rfl

private theorem factory_value_cast {left right : Context registry}
    (same : left = right)
    (original : Tower.Model left R) (other : Tower.Model right R)
    (first : reader.read left = some original)
    (second : reader.read right = some other) (a : left.Value) :
    original.value a = other.value (_root_.cast (congrArg Context.Value same) a) := by
  cases same
  have aligned : original = other := Option.some.inj (first.symm.trans second)
  cases aligned
  rfl

/-- An original value has the same union image in any two successful gathers,
even when it appears at different positions and the target towers differ. -/
theorem Shared.Model.toUnion_coherent
    {firstOwners secondOwners : List (Context registry)}
    {first : Shared base firstOwners} {second : Shared base secondOwners}
    {following : base.Realization} {reference : Tower.Model (Context.ofBase base) R}
    [reader.Agrees following reference]
    (firstModel : Shared.Model (reader := reader) first following reference)
    (secondModel : Shared.Model (reader := reader) second following reference)
    (i : Fin firstOwners.length) (j : Fin secondOwners.length)
    (same : firstOwners[i] = secondOwners[j]) (a : (firstOwners[i]).Value) :
    firstModel.toUnion i a =
      secondModel.toUnion j (_root_.cast (congrArg Context.Value same) a) := by
  apply Subtype.ext
  rw [firstModel.toUnion_value, secondModel.toUnion_value]
  exact factory_value_cast same (firstModel.owners.get i).1
    (secondModel.owners.get j).1 (firstModel.canonicalOwners i)
    (secondModel.canonicalOwners j) a

/-- Register another live context while retaining every value already computed
in the shared target and its image in the same prescribed algebraic union. -/
theorem Shared.Model.add?_union {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants <+ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ result, shared.add? source = some result ∧
      ∃ returned : Shared.Model result following reference,
        ∃ previous : Inclusion shared.input.context result.input.context,
          (∀ a, returned.target.value (previous.value a) = model.target.value a) ∧
          ∀ a, result.targetToUnion reference (previous.value a) =
            shared.targetToUnion reference a := by
  obtain ⟨result, produced, returned, previous, preserved⟩ :=
    model.add?_transport source compatible
  refine ⟨result, produced, returned, previous, preserved, fun a => ?_⟩
  apply Subtype.ext
  rw [returned.targetToUnion_value, model.targetToUnion_value, preserved]

/-- The registration packet transports all already computed target values
into the same algebraic union through its actual retained runtime inclusion. -/
theorem Shared.Model.register?_union {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (source : Context registry)
    (compatible : source.origin.base.signature.constants <+ base.signature.constants ∧
      source.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals) :
    ∃ packet : Registration shared source,
      shared.register? source = some packet ∧
        ∃ returned : Shared.Model packet.shared following reference,
          (∀ a, returned.target.value (packet.previous.value a) = model.target.value a) ∧
          ∀ a, packet.shared.targetToUnion reference (packet.previous.value a) =
            shared.targetToUnion reference a := by
  obtain ⟨packet, produced, returned, preserved⟩ := model.register? source compatible
  refine ⟨packet, produced, returned, preserved, fun a => ?_⟩
  apply Subtype.ext
  rw [returned.targetToUnion_value, model.targetToUnion_value, preserved]

section TargetOperations
variable {owners : List (Context registry)} {shared : Shared base owners}
variable {following : base.Realization} {reference : Tower.Model (Context.ofBase base) R}
variable [reader.Agrees following reference]
variable (model : Shared.Model (reader := reader) shared following reference)
include model

/-- The union map preserves target add after values from different owners are combined. -/
theorem Shared.Model.targetToUnion_add (a b : shared.input.context.Value) :
    shared.targetToUnion reference (a + b) =
      shared.targetToUnion reference a + shared.targetToUnion reference b := by
  apply Subtype.ext
  change (shared.targetToUnion reference (a + b) : R) =
    (shared.targetToUnion reference a : R) + (shared.targetToUnion reference b : R)
  rw [model.targetToUnion_value, model.targetToUnion_value, model.targetToUnion_value]
  exact model.target.add a b

/-- The union map preserves target sub after values from different owners are combined. -/
theorem Shared.Model.targetToUnion_sub (a b : shared.input.context.Value) :
    shared.targetToUnion reference (a - b) =
      shared.targetToUnion reference a - shared.targetToUnion reference b := by
  apply Subtype.ext
  change (shared.targetToUnion reference (a - b) : R) =
    (shared.targetToUnion reference a : R) - (shared.targetToUnion reference b : R)
  rw [model.targetToUnion_value, model.targetToUnion_value, model.targetToUnion_value]
  exact model.target.sub a b

/-- The union map preserves target mul after values from different owners are combined. -/
theorem Shared.Model.targetToUnion_mul (a b : shared.input.context.Value) :
    shared.targetToUnion reference (a * b) =
      shared.targetToUnion reference a * shared.targetToUnion reference b := by
  apply Subtype.ext
  change (shared.targetToUnion reference (a * b) : R) =
    (shared.targetToUnion reference a : R) * (shared.targetToUnion reference b : R)
  rw [model.targetToUnion_value, model.targetToUnion_value, model.targetToUnion_value]
  exact model.target.mul a b

/-- The union map preserves target div after values from different owners are combined. -/
theorem Shared.Model.targetToUnion_div (a b : shared.input.context.Value) :
    shared.targetToUnion reference (a / b) =
      shared.targetToUnion reference a / shared.targetToUnion reference b := by
  apply Subtype.ext
  change (shared.targetToUnion reference (a / b) : R) =
    (shared.targetToUnion reference a : R) / (shared.targetToUnion reference b : R)
  rw [model.targetToUnion_value, model.targetToUnion_value, model.targetToUnion_value]
  exact model.target.div a b

/-- The union map preserves target neg. -/
theorem Shared.Model.targetToUnion_neg (a : shared.input.context.Value) :
    shared.targetToUnion reference (-a) = - (shared.targetToUnion reference a) := by
  apply Subtype.ext
  change (shared.targetToUnion reference (-a) : R) = - (shared.targetToUnion reference a : R)
  rw [model.targetToUnion_value, model.targetToUnion_value]
  exact model.target.neg a

/-- The union map preserves target inv. -/
theorem Shared.Model.targetToUnion_inv (a : shared.input.context.Value) :
    shared.targetToUnion reference (a⁻¹) = (shared.targetToUnion reference a)⁻¹ := by
  apply Subtype.ext
  change (shared.targetToUnion reference (a⁻¹) : R) = (shared.targetToUnion reference a : R)⁻¹
  rw [model.targetToUnion_value, model.targetToUnion_value]
  exact model.target.inv a

/-- Target zero maps to the zero of the prescribed union. -/
theorem Shared.Model.targetToUnion_zero : shared.targetToUnion reference 0 = 0 := by
  apply Subtype.ext
  change (shared.targetToUnion reference 0 : R) = 0
  rw [model.targetToUnion_value]
  exact (model.target.zero_iff 0).mpr rfl

/-- Target one maps to the unit of the prescribed union. -/
theorem Shared.Model.targetToUnion_one : shared.targetToUnion reference 1 = 1 := by
  apply Subtype.ext
  change (shared.targetToUnion reference 1 : R) = 1
  rw [model.targetToUnion_value]
  exact model.target.one

/-- Equality of combined values is equality of their union images. -/
theorem Shared.Model.targetToUnion_equal (a b : shared.input.context.Value) :
    shared.input.context.equal a b =
      decide (shared.targetToUnion reference a = shared.targetToUnion reference b) := by
  rw [model.target.equal_spec]
  have equal : shared.targetToUnion reference a = shared.targetToUnion reference b ↔
      (shared.targetToUnion reference a : R) = (shared.targetToUnion reference b : R) :=
    Subtype.ext_iff
  simp only [equal, model.targetToUnion_value]

/-- The shared target retains the prescribed coefficient-field embedding. -/
theorem Shared.Model.targetToUnion_base (a : (Context.ofBase base).Value) :
    shared.targetToUnion reference (shared.input.value a) =
      algebraMap reference.field (Union.Carrier reference.field R) (reference.toValue a) := by
  apply Subtype.ext
  change (shared.targetToUnion reference (shared.input.value a) : R) =
    ((reference.toValue a : reference.field) : R)
  rw [model.targetToUnion_value, model.input, reference.coe_toValue]

/-- Target comparison agrees with the order in the algebraic union. -/
theorem Shared.Model.targetToUnion_compare (a b : shared.input.context.Value) :
    shared.input.context.compare a b =
      if shared.targetToUnion reference a < shared.targetToUnion reference b then Ordering.lt
      else if shared.targetToUnion reference a = shared.targetToUnion reference b
        then Ordering.eq else Ordering.gt := by
  rw [model.target.compare_spec]
  have equal : shared.targetToUnion reference a = shared.targetToUnion reference b ↔
      (shared.targetToUnion reference a : R) = (shared.targetToUnion reference b : R) :=
    Subtype.ext_iff
  change _ = if (shared.targetToUnion reference a : R) <
      (shared.targetToUnion reference b : R) then Ordering.lt
    else if shared.targetToUnion reference a = shared.targetToUnion reference b
      then Ordering.eq else Ordering.gt
  simp only [equal, model.targetToUnion_value]

/-- Target signs agree with the signs of the same union values. -/
theorem Shared.Model.targetToUnion_sign (a : shared.input.context.Value) :
    shared.input.context.sign a = (SignType.sign (shared.targetToUnion reference a) : Int) := by
  rw [model.target.sign]
  change _ = (SignType.sign (shared.targetToUnion reference a : R) : Int)
  rw [model.targetToUnion_value]

end TargetOperations

section Operations
variable {owners : List (Context registry)} {shared : Shared base owners}
variable {following : base.Realization} {reference : Tower.Model (Context.ofBase base) R}
variable [reader.Agrees following reference]
variable (model : Shared.Model (reader := reader) shared following reference) (index : Fin owners.length)

/-- The checked union map preserves native addition. -/
theorem Shared.Model.toUnion_add (a b : (owners[index]).Value) :
    model.toUnion index (a + b) = model.toUnion index a + model.toUnion index b := by
  apply Subtype.ext
  change (model.toUnion index (a + b) : R) =
    (model.toUnion index a : R) + (model.toUnion index b : R)
  rw [model.toUnion_value, model.toUnion_value, model.toUnion_value]
  exact (model.owners.get index).1.add a b

/-- The checked union map preserves native subtraction. -/
theorem Shared.Model.toUnion_sub (a b : (owners[index]).Value) :
    model.toUnion index (a - b) = model.toUnion index a - model.toUnion index b := by
  apply Subtype.ext
  change (model.toUnion index (a - b) : R) =
    (model.toUnion index a : R) - (model.toUnion index b : R)
  rw [model.toUnion_value, model.toUnion_value, model.toUnion_value]
  exact (model.owners.get index).1.sub a b

/-- The checked union map preserves native multiplication. -/
theorem Shared.Model.toUnion_mul (a b : (owners[index]).Value) :
    model.toUnion index (a * b) = model.toUnion index a * model.toUnion index b := by
  apply Subtype.ext
  change (model.toUnion index (a * b) : R) =
    (model.toUnion index a : R) * (model.toUnion index b : R)
  rw [model.toUnion_value, model.toUnion_value, model.toUnion_value]
  exact (model.owners.get index).1.mul a b

/-- The checked union map preserves native division. -/
theorem Shared.Model.toUnion_div (a b : (owners[index]).Value) :
    model.toUnion index (a / b) = model.toUnion index a / model.toUnion index b := by
  apply Subtype.ext
  change (model.toUnion index (a / b) : R) =
    (model.toUnion index a : R) / (model.toUnion index b : R)
  rw [model.toUnion_value, model.toUnion_value, model.toUnion_value]
  exact (model.owners.get index).1.div a b

/-- The checked union map preserves native negation. -/
theorem Shared.Model.toUnion_neg (a : (owners[index]).Value) :
    model.toUnion index (-a) = -model.toUnion index a := by
  apply Subtype.ext
  change (model.toUnion index (-a) : R) = - (model.toUnion index a : R)
  rw [model.toUnion_value, model.toUnion_value]
  exact (model.owners.get index).1.neg a

/-- The checked union map preserves native total inversion. -/
theorem Shared.Model.toUnion_inv (a : (owners[index]).Value) :
    model.toUnion index (a⁻¹) = (model.toUnion index a)⁻¹ := by
  apply Subtype.ext
  change (model.toUnion index (a⁻¹) : R) = (model.toUnion index a : R)⁻¹
  rw [model.toUnion_value, model.toUnion_value]
  exact (model.owners.get index).1.inv a

/-- Canonical zero enters the actual zero of the union field. -/
theorem Shared.Model.toUnion_zero : model.toUnion index 0 = 0 := by
  apply Subtype.ext
  change (model.toUnion index 0 : R) = 0
  rw [model.toUnion_value]
  exact ((model.owners.get index).1.zero_iff 0).mpr rfl

/-- Native one enters the unit of the union field. -/
theorem Shared.Model.toUnion_one : model.toUnion index 1 = 1 := by
  apply Subtype.ext
  change (model.toUnion index 1 : R) = 1
  rw [model.toUnion_value]
  exact (model.owners.get index).1.one

/-- Native mathematical equality is equality of the corresponding union values. -/
theorem Shared.Model.toUnion_equal (a b : (owners[index]).Value) :
    (owners[index]).equal a b = decide (model.toUnion index a = model.toUnion index b) := by
  rw [(model.owners.get index).1.equal_spec]
  have equal : model.toUnion index a = model.toUnion index b ↔
      (model.toUnion index a : R) = (model.toUnion index b : R) := Subtype.ext_iff
  simp only [equal, model.toUnion_value]

/-- Native comparison uses the order of the same union values. -/
theorem Shared.Model.toUnion_compare (a b : (owners[index]).Value) :
    (owners[index]).compare a b =
      if model.toUnion index a < model.toUnion index b then Ordering.lt
      else if model.toUnion index a = model.toUnion index b then Ordering.eq else Ordering.gt := by
  rw [(model.owners.get index).1.compare_spec]
  have equal : model.toUnion index a = model.toUnion index b ↔
      (model.toUnion index a : R) = (model.toUnion index b : R) := Subtype.ext_iff
  change _ = if (model.toUnion index a : R) < (model.toUnion index b : R) then Ordering.lt
    else if model.toUnion index a = model.toUnion index b then Ordering.eq else Ordering.gt
  simp only [equal, model.toUnion_value]

end Operations

/-- The actual root model extends any factory-derived compatible parent. -/
theorem Root.model?_ofModel {parent : Context registry} (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) (root : Root parent)
    (original : Tower.Model parent R)
    (produced : parent.model? following reference = some original) :
    root.context.model? following reference = some (root.model original) := by
  exact (OwnerReader.ordered following reference).root_model root original produced

/-- Native root contexts use their canonical owner-factory interpretation. -/
theorem Root.model?_factory (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) (root : Root (Context.ofBase base)) :
    root.context.model? following reference = some (root.model reference) := by
  exact root.model?_ofModel following reference reference (Context.model?_base following reference)

/-- A child owner's checked coefficient embedding has the same union image
as the original parent value, including across proper base inclusions. -/
theorem Shared.Model.toUnion_embed {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    [reader.Agrees following reference]
    (model : Shared.Model (reader := reader) shared following reference)
    (i j : Fin owners.length) (root : Root owners[i]) (same : root.context = owners[j])
    (a : (owners[i]).Value) :
    model.toUnion j (_root_.cast (congrArg Context.Value same) (root.embed a)) =
      model.toUnion i a := by
  apply Subtype.ext
  have produced := reader.root_model root (model.owners.get i).1 (model.canonicalOwners i)
  exact (model.toUnion_value j _).trans
    ((factory_value_cast same (root.model (model.owners.get i).1)
      (model.owners.get j).1 produced (model.canonicalOwners j) (root.embed a)).symm.trans
        ((root.embed_value (model.owners.get i).1 a).trans (model.toUnion_value i a).symm))

/-- Every element of the prescribed union is represented by an actual native
root producer entry and by its checked inclusion into an actual shared target. -/
theorem Shared.union_coverage (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R) (x : Union.Carrier reference.field R) :
    ∃ p : (Context.ofBase base).Poly, ∃ out,
      (Context.ofBase base).roots p = .finite out ∧ ∃ entry ∈ out,
        ∃ shared : Shared base [entry.root.context],
          Shared.gather? base [entry.root.context] = some shared ∧
            ∃ model : Shared.Model shared following reference,
              (model.toUnion 0 entry.root.value : R) = x := by
  obtain ⟨p, out, produced, entry, member, meaning⟩ := reference.union_coverage x
  have compatible : entry.root.context.origin.base.signature.constants <+
      base.signature.constants ∧
      entry.root.context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
    rw [entry.root.origin_base, Context.ofBase_origin_base]
    exact ⟨List.Sublist.refl _, Nat.le_refl _⟩
  obtain ⟨shared, sharedProduced, ⟨model⟩⟩ :=
    Shared.gather?_models following reference [entry.root.context]
      (fun source present => by
        have same : source = entry.root.context := List.mem_singleton.mp present
        subst source
        exact compatible)
  refine ⟨p, out, produced, entry, member, shared, sharedProduced, model, ?_⟩
  have ownerFactory : entry.root.context.model? following reference =
      some (model.owners.get 0).1 := by
    exact model.canonicalOwners 0
  have aligned := Option.some.inj (ownerFactory.symm.trans
    (entry.root.model?_factory following reference))
  exact (model.toUnion_value 0 entry.root.value).trans
    ((congrArg (fun m : Tower.Model entry.root.context R => m.value entry.root.value) aligned).trans meaning)

/-- An existing gathering can add any element of the algebraic union through
an actual root-producer owner. Every retained original owner keeps its image. -/
theorem Shared.Model.union_extend {owners : List (Context registry)}
    {shared : Shared base owners} {following : base.Realization}
    {reference : Tower.Model (Context.ofBase base) R}
    (model : Shared.Model shared following reference) (x : Union.Carrier reference.field R) :
    ∃ p : (Context.ofBase base).Poly, ∃ out,
      (Context.ofBase base).roots p = .finite out ∧ ∃ entry ∈ out,
        ∃ added : Shared base (owners ++ [entry.root.context]),
          shared.add? entry.root.context = some added ∧
          ∃ next : Shared.Model added following reference,
            (∃ (j : Fin (owners ++ [entry.root.context]).length)
              (same : entry.root.context = (owners ++ [entry.root.context])[j]),
              (next.toUnion j (_root_.cast (congrArg Context.Value same) entry.root.value) : R) = x) ∧
            ∀ (i : Fin owners.length) (a : (owners[i]).Value),
              ∃ (j : Fin (owners ++ [entry.root.context]).length)
                (same : owners[i] = (owners ++ [entry.root.context])[j]),
                next.toUnion j (_root_.cast (congrArg Context.Value same) a) = model.toUnion i a := by
  obtain ⟨p, out, produced, entry, member, meaning⟩ := reference.union_coverage x
  have compatible : entry.root.context.origin.base.signature.constants <+
      base.signature.constants ∧
      entry.root.context.origin.base.signature.infinitesimals ≤ base.signature.infinitesimals := by
    rw [entry.root.origin_base, Context.ofBase_origin_base]
    exact ⟨List.Sublist.refl _, Nat.le_refl _⟩
  obtain ⟨added, addedProduced, ⟨next⟩⟩ := model.add? entry.root.context compatible
  refine ⟨p, out, produced, entry, member, added, addedProduced, next, ?_, ?_⟩
  · let j : Fin (owners ++ [entry.root.context]).length := ⟨owners.length, by simp⟩
    have same : entry.root.context = (owners ++ [entry.root.context])[j] := by simp [j]
    refine ⟨j, same, ?_⟩
    exact (next.toUnion_value j _).trans
      ((factory_value_cast same (entry.root.model reference)
        (next.owners.get j).1 (entry.root.model?_factory following reference)
        (next.canonicalOwners j) entry.root.value).symm.trans meaning)
  · intro i a
    let j : Fin (owners ++ [entry.root.context]).length :=
      ⟨i.val, by simp only [List.length_append, List.length_singleton]; omega⟩
    have same : owners[i] = (owners ++ [entry.root.context])[j] := by
      simp only [j, Fin.getElem_fin, List.getElem_append_left i.isLt]
    exact ⟨j, same, (model.toUnion_coherent next i j same a).symm⟩

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Shared.union_coverage' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.union_coverage

/-- info: 'Hex.RealClosure.Tower.Shared.Model.toUnion_compare' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.toUnion_compare

/-- info: 'Hex.RealClosure.Tower.Shared.Model.targetToUnion_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.targetToUnion_inv

/-- info: 'Hex.RealClosure.Tower.Shared.Model.toUnion_coherent' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.toUnion_coherent

/-- info: 'Hex.RealClosure.Tower.Shared.Model.union_extend' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.union_extend

/-- info: 'Hex.RealClosure.Tower.Shared.Model.add?_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.add?_union

/-- info: 'Hex.RealClosure.Tower.Shared.Model.register?_union' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Shared.Model.register?_union
