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
  obtain ⟨read, domain, targetClosed, closed, finite, _, fresh, _, _, _, parameter, positive⟩ :=
    result.realize following gathered produced [a, b, a + b, a * b]
      [result.previous.value a - result.parameter]
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
  obtain ⟨read, domain, _, closed, finite, _, _⟩ := collection.realize following produced
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
    ∃ x epsilon : ℝ, 0 < epsilon ∧
      (SignType.sign x : Int) = first.collection.shared.input.context.sign first.parameter ∧
      (SignType.sign (x - epsilon) : Int) = next.collection.shared.input.context.sign
        (next.previous.value first.parameter - next.parameter) := by
  classical
  let reference := following.reference
  let initial := original.model following reference.model gathered
  let ambient := Ambient.ofField (Hex.RationalFn reference.Carrier)
  let previous := first.model initial ambient built
  obtain ⟨read, domain, closed, _, finite, _, fresh, _, _, _, parameter, positive⟩ :=
    next.realize_model previous produced [first.parameter]
      [next.previous.value first.parameter - next.parameter]
  have old := finite first.parameter (by simp)
  have difference := fresh (next.previous.value first.parameter - next.parameter) (by simp)
  refine ⟨read (next.previous.value first.parameter), read next.parameter,
    positive, old.2.1, ?_⟩
  rw [← closed.read_sub _ _ old.1 parameter]
  exact difference.2.1

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
