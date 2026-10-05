/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.SharedRealization

public section

open scoped List
open scoped Hex.OrderedFn.Infinitesimal

namespace Hex.RealClosure.Tower.Live.RealizationTests

variable {registry : BaseContext.Registry} {base : BaseContext.PackedContext registry}
variable {request : Request registry} {original : Collection base request}

/-- Public callers obtain one positive real parameter and simultaneous old
sum/product signs and the sign of an old operand minus the new parameter
after actual enlargement. No model, ambient field, separate
owner reader, or arithmetic agreement is supplied. The old native context may
contain any stored algebraic suffix over any number of infinitesimal stages. -/
theorem enlarge_arithmetic (result : Enlargement original) (following : base.Realization)
    (gathered : request.gather? base = some original)
    (produced : original.enlarge? = some result)
    (a b : original.shared.input.context.Value) :
    ∃ x y epsilon : ℝ, 0 < epsilon ∧
      (SignType.sign x : Int) = original.shared.input.context.sign a ∧
      (SignType.sign y : Int) = original.shared.input.context.sign b ∧
      (SignType.sign (x + y) : Int) = original.shared.input.context.sign (a + b) ∧
      (SignType.sign (x * y) : Int) = original.shared.input.context.sign (a * b) ∧
      (SignType.sign (x - epsilon) : Int) = result.collection.shared.input.context.sign
        (result.previous.value a - result.parameter) := by
  obtain ⟨read, domain, data⟩ :=
    result.realize following gathered produced [a, b, a + b, a * b]
      [result.previous.value a - result.parameter]
  have targetClosed := data.closed
  have closed := data.previousClosed
  have finite := data.finite
  have fresh := data.additional
  have parameter := data.parameter
  have positive := data.positive
  have left := finite a (by simp)
  have right := finite b (by simp)
  have sum := finite (a + b) (by simp)
  have product := finite (a * b) (by simp)
  have difference := fresh (result.previous.value a - result.parameter) (by simp)
  refine ⟨read (result.previous.value a), read (result.previous.value b),
    read result.parameter, positive, left.2.1, right.2.1, ?_, ?_, ?_⟩
  · rw [← closed.read_add a b left.1 right.1]
    exact sum.2.1
  · rw [← closed.read_mul a b left.1 right.1]
    exact product.2.1
  · rw [← targetClosed.read_sub _ _ left.1 parameter]
    exact difference.2.1

/-- The public collection theorem supplies usable transport premises for
every retained descriptor, including leading and zero reflection guards. -/
theorem collection_replay (collection : Collection base request) (following : base.Realization)
    (produced : request.gather? base = some collection) :
    ∃ read : collection.shared.input.context.Value → ℝ,
      ∃ domain : collection.shared.input.context.Value → Prop,
      ∀ index : Fin request.owners.length,
        ∀ descriptor : SignDet.Descriptor (request.owners[index]).Value Signature
          (request.owners[index]).sign (request.owners[index]).signature,
        List.Mem descriptor (request.frame ⟨index.val,
          by simpa only [Request.owners, List.length_map] using index.isLt⟩).descriptors →
        Transport.DescriptorData (fun a => read (collection.shared.value index a))
          (fun a => domain (collection.shared.value index a)) (request.owners[index]).sign
          (fun a : ℝ => (SignType.sign a : Int)) descriptor.raw descriptor.evidence := by
  obtain ⟨read, domain, data⟩ := collection.realize following produced
  have closed := data.ownerClosed
  have finite := data.finite
  refine ⟨read, domain, ?_⟩
  intro index descriptor member
  apply Transport.Inventory.descriptor_data (closed index)
  intro a stored
  apply finite index a
  unfold Request.inventory Frame.inventory
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨descriptor, member, stored⟩)

/-- A second actual enlargement uses the first returned factory model;
the collection need not be produced by a new gather. Its new parameter and
an expression involving the old parameter share one ordinary reader. -/
theorem enlarge_twice (first : Enlargement original) (next : Enlargement first.collection)
    (following : base.Realization) (gathered : request.gather? base = some original)
    (built : original.enlarge? = some first) (produced : first.collection.enlarge? = some next) :
    ∃ read : next.collection.shared.input.context.Value → ℝ,
      ∃ domain : next.collection.shared.input.context.Value → Prop,
        Transport.Closed read domain ∧
        domain (next.previous.value first.parameter) ∧ domain next.parameter ∧
        0 < read next.parameter ∧
        (SignType.sign (read (next.previous.value first.parameter)) : Int) =
          first.collection.shared.input.context.sign first.parameter ∧
        (SignType.sign (read (next.previous.value first.parameter) - read next.parameter) : Int) =
          next.collection.shared.input.context.sign
            (next.previous.value first.parameter - next.parameter) := by
  classical
  let reference := following.reference
  let initial := original.model following reference.model gathered
  let ambient := Ambient.ofField (Hex.RationalFn reference.Carrier)
  let previous := first.model initial ambient built
  obtain ⟨read, domain, data⟩ :=
    next.realize_model previous produced [first.parameter]
      [next.previous.value first.parameter - next.parameter]
  have closed := data.closed
  have finite := data.finite
  have fresh := data.additional
  have parameter := data.parameter
  have positive := data.positive
  have old := finite first.parameter (by simp)
  have difference := fresh (next.previous.value first.parameter - next.parameter) (by simp)
  refine ⟨read, domain, closed, old.1, parameter, positive, old.2.1, ?_⟩
  rw [← closed.read_sub _ _ old.1 parameter]
  exact difference.2.1

/-- The refreshed target-side replay inventory supplies the actual descriptor
transport premises, including exact-zero guards, under one ordinary reader. -/
theorem target_replay (collection : Collection base request) (following : base.Realization)
    (produced : request.gather? base = some collection) :
    ∃ read : collection.shared.input.context.Value → ℝ,
      ∃ domain : collection.shared.input.context.Value → Prop,
        ∀ frame : Frame collection.shared.input.context,
          List.Mem frame collection.frames →
          ∀ descriptor : SignDet.Descriptor collection.shared.input.context.Value Signature
            collection.shared.input.context.sign collection.shared.input.context.signature,
            List.Mem descriptor frame.descriptors →
            Transport.DescriptorData read domain collection.shared.input.context.sign
              (fun a : ℝ => (SignType.sign a : Int)) descriptor.raw descriptor.evidence := by
  obtain ⟨read, domain, data⟩ :=
    collection.realize following produced collection.inventory
  have closed := data.closed
  have additional := data.additional
  refine ⟨read, domain, ?_⟩
  intro frame member descriptor stored
  apply Transport.Inventory.descriptor_data closed
  intro a reached
  apply additional a
  unfold Collection.inventory
  apply List.mem_flatMap.mpr
  refine ⟨frame, member, ?_⟩
  unfold Frame.inventory
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨descriptor, stored, reached⟩)

/-- An independently validated single-constant owner enters a two-constant
prefix with a different preceding constant. Both bases retain one infinitesimal,
so the checked map uses the aligned stage branch and a non-prefix real map.
No provider-value agreement is supplied by the caller. -/
theorem separate_providers (source parent : BaseContext.RealPrefix.Model registry)
    (alpha beta : BaseContext.ConstantKey)
    (sourceKeys : source.context.keys = [beta]) (parentKeys : parent.context.keys = [alpha])
    (present : (registry beta).isSome = true) (tau : ℝ)
    (contained : ∀ delta, 0 < delta →
      OrderedFn.Oracle.Contains ((registry beta).get present delta) tau)
    (width : ∀ delta, 0 < delta → ((registry beta).get present delta).width ≤ delta)
    (transcendental : letI : Field parent.context.Carrier := HexPolyMathlib.fieldOfGrind
      OrderedFn.Real.RelativeTranscendence parent.interpretation.hom tau)
    (b : (Context.ofBase source.context.finish).Value) :
    let child := parent.register beta present tau contained width transcendental
    let original := source.context.finish.infinitesimal
    let target := child.context.finish.infinitesimal
    let a := Context.baseValue original (@RationalFn.C source.context.finish.Carrier
      inferInstance inferInstance (Context.baseStored source.context.finish b))
    ∃ shared : Shared target [Context.ofBase original],
      Shared.gather? target [Context.ofBase original] = some shared ∧
      ∃ read : shared.input.context.Value → ℝ,
        ∃ domain : shared.input.context.Value → Prop,
          Transport.Closed read domain ∧ domain (shared.value ⟨0, by simp⟩ a) ∧
          read (shared.value ⟨0, by simp⟩ a) =
            source.interpretation.hom (Context.baseStored source.context.finish b) := by
  classical
  intro child original target a
  have childKeys : child.context.keys = [alpha, beta] := by
    rw [BaseContext.RealPrefix.Model.register_keys, parentKeys]
    rfl
  have baseOrigin (base : BaseContext.PackedContext registry) :
      (Context.ofBase base).origin.base = base := by
    cases base with
    | pack base =>
      change (Context.base base).origin.base = BaseContext.PackedContext.pack base
      rw [Context.origin_base]
      rfl
  let following := child.realization.infinitesimal
  obtain ⟨shared, gathered, _⟩ := Shared.gather?_models following following.reference.model
    [Context.ofBase original] (by
      intro owner member
      cases List.mem_singleton.mp member
      simp only [baseOrigin, original, BaseContext.PackedContext.infinitesimal_signature,
        BaseContext.RealPrefix.finish_signature, sourceKeys, childKeys]
      exact ⟨List.sublist_append_right [alpha] [beta], Nat.le_refl _⟩)
  obtain ⟨read, domain, data⟩ :=
    shared.realize_values following gathered (fun _ => [])
  have closed := data.closed
  have ownerFixed := data.ownerFixed
  have real : BaseContext.PackedContext.Realization.RealValue source.realization.infinitesimal a
      (source.interpretation.hom (Context.baseStored source.context.finish b)) :=
    (BaseContext.PackedContext.Realization.realValue_infinitesimal source.realization b _).mpr
      ((source.realValue b _).mpr rfl)
  let suffix : Suffix (Context.ofBase original) := .nil
  obtain ⟨ownerHistory, inherited⟩ := suffix.realValue_owner original source.realization.infinitesimal
    a _ real
  have preserved := ownerFixed ⟨0, by simp⟩ ownerHistory a _ inherited
  exact ⟨shared, gathered, read, domain, closed, preserved⟩

end Hex.RealClosure.Tower.Live.RealizationTests

/-- info: 'Hex.RealClosure.Tower.Live.RealizationTests.enlarge_arithmetic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.RealizationTests.enlarge_arithmetic

/-- info: 'Hex.RealClosure.Tower.Live.RealizationTests.collection_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.RealizationTests.collection_replay

/-- info: 'Hex.RealClosure.Tower.Live.RealizationTests.enlarge_twice' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.RealizationTests.enlarge_twice

/-- info: 'Hex.RealClosure.Tower.Live.RealizationTests.separate_providers' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.RealizationTests.separate_providers

/-- info: 'Hex.RealClosure.Tower.Live.RealizationTests.target_replay' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Live.RealizationTests.target_replay
