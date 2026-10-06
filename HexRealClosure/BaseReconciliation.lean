/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.BaseInclusion
public import HexRealClosure.BaseStagedReorder

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A cached native base map produced by staged reconciliation. Original
contexts retain their provider progress proofs and arithmetic dictionaries. -/
structure BaseReconciliation (source target : BaseContext.PackedContext registry) where
  private mk ::
  coefficients : BaseContext.FieldEmbedding source.Carrier target.Carrier
  produced : source.reconcile? target = some coefficients

/-- A checked native factory has one retained map for fixed actual contexts. -/
instance {source target : BaseContext.PackedContext registry} :
    Subsingleton (BaseReconciliation source target) where
  allEq a b := by
    have same := Option.some.inj (a.produced.symm.trans b.produced)
    cases a
    cases b
    cases same
    rfl

/-- Check provider-key reconciliation once and retain the resulting native map. -/
def BaseReconciliation.make? (source target : BaseContext.PackedContext registry) :
    Option (BaseReconciliation source target) :=
  match produced : source.reconcile? target with
  | none => none
  | some coefficients => some ⟨coefficients, produced⟩

/-- Every distinct-key inclusion with sufficient infinitesimal depth is accepted. -/
theorem BaseReconciliation.make?_success (source target : BaseContext.PackedContext registry)
    (sourceUnique : source.signature.constants.Nodup)
    (targetUnique : target.signature.constants.Nodup)
    (included : source.signature.constants ⊆ target.signature.constants)
    (depth : source.signature.infinitesimals ≤ target.signature.infinitesimals) :
    (BaseReconciliation.make? source target).isSome = true := by
  have accepted := source.reconcile?_success target sourceUnique targetUnique included depth
  unfold BaseReconciliation.make?
  split <;> simp_all only [Option.isSome_none, Option.isSome_some]

private theorem ordered_map (source target : BaseContext.PackedContext registry)
    (map : BaseContext.FieldEmbedding source.Carrier target.Carrier)
    (accepted : source.subsequence? target = some map) : source.reconcile? target = some map := by
  cases source with
  | pack original =>
    cases target with
    | pack following =>
      exact following.chain.reconcile?_ordered original.chain map accepted

/-- An existing ordered inclusion retains its exact cached coefficient map. -/
def BaseReconciliation.ofOrdered {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) : BaseReconciliation source target :=
  ⟨inclusion.coefficients, ordered_map source target inclusion.coefficients inclusion.produced⟩

/-- Every retained reconciliation equals an available ordered inclusion's
wrapper, including reconciliations already stored by gathering or caches. -/
theorem BaseReconciliation.eq_ofOrdered {source target : BaseContext.PackedContext registry}
    (reconciled : BaseReconciliation source target) (ordered : BaseInclusion source target) :
    reconciled = BaseReconciliation.ofOrdered ordered := Subsingleton.elim _ _

/-- Transport a nominal base value using the retained native coefficient map. -/
@[expose] def BaseReconciliation.value {source target : BaseContext.PackedContext registry}
    (inclusion : BaseReconciliation source target) (a : (Context.ofBase source).Value) :
    (Context.ofBase target).Value :=
  Context.baseValue target (inclusion.coefficients.value (Context.baseStored source a))

private theorem BaseReconciliation.make?_ordered_proof
    {source target : BaseContext.PackedContext registry} (inclusion : BaseInclusion source target) :
    BaseReconciliation.make? source target = some (BaseReconciliation.ofOrdered inclusion) := by
  have produced := ordered_map source target inclusion.coefficients inclusion.produced
  unfold BaseReconciliation.make?
  split <;> rename_i found
  · rw [produced] at found
    contradiction
  · have coefficients := Option.some.inj (found.symm.trans produced)
    cases coefficients
    rfl

/-- The actual factory retains an available ordered inclusion's coefficient map. -/
theorem BaseReconciliation.make?_ordered
    {source target : BaseContext.PackedContext registry} (inclusion : BaseInclusion source target) :
    BaseReconciliation.make? source target = some (BaseReconciliation.ofOrdered inclusion) :=
  BaseReconciliation.make?_ordered_proof inclusion

/-- Every accepted reconciliation agrees with an available original ordered
inclusion, including wrappers returned by the actual native factory. -/
theorem BaseReconciliation.value_eq_ordered
    {source target : BaseContext.PackedContext registry}
    (reconciled : BaseReconciliation source target) (ordered : BaseInclusion source target)
    (a : (Context.ofBase source).Value) : reconciled.value a = ordered.value a := by
  have accepted := ordered_map source target ordered.coefficients ordered.produced
  have coefficients : reconciled.coefficients = ordered.coefficients :=
    Option.some.inj (reconciled.produced.symm.trans accepted)
  simp only [BaseReconciliation.value, BaseInclusion.value, coefficients]

private theorem BaseReconciliation.ordered_value_proof {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) (a : (Context.ofBase source).Value) :
    (BaseReconciliation.ofOrdered inclusion).value a = inclusion.value a := rfl

/-- Ordered reconciliation uses the original ordered inclusion on every value. -/
theorem BaseReconciliation.ordered_value {source target : BaseContext.PackedContext registry}
    (inclusion : BaseInclusion source target) (a : (Context.ofBase source).Value) :
    (BaseReconciliation.ofOrdered inclusion).value a = inclusion.value a :=
  BaseReconciliation.ordered_value_proof inclusion a

/-- Reconciled base transport preserves and reflects native canonical zero. -/
theorem BaseReconciliation.zero {source target : BaseContext.PackedContext registry}
    (inclusion : BaseReconciliation source target) (a : (Context.ofBase source).Value) :
    inclusion.value a = 0 ↔ a = 0 := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      change (⟨inclusion.coefficients.value a.stored⟩ : BaseContext.Element target) = 0 ↔ a = 0
      exact (BaseContext.Element.stored_eq_zero _).symm.trans
        ((inclusion.coefficients.zero a.stored).trans (BaseContext.Element.stored_eq_zero a))

/-- Reconciled base transport preserves one. -/
theorem BaseReconciliation.one {source target : BaseContext.PackedContext registry}
    (inclusion : BaseReconciliation source target) : inclusion.value 1 = 1 := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      apply BaseContext.Element.ext
      exact inclusion.coefficients.one

/-- Reconciled base transport preserves subtraction in the stored dictionaries. -/
theorem BaseReconciliation.sub {source target : BaseContext.PackedContext registry}
    (inclusion : BaseReconciliation source target) (a b : (Context.ofBase source).Value) :
    inclusion.value (a - b) = inclusion.value a - inclusion.value b := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      apply BaseContext.Element.ext
      exact inclusion.coefficients.sub a.stored b.stored

/-- Reconciled base transport preserves multiplication in the stored dictionaries. -/
theorem BaseReconciliation.mul {source target : BaseContext.PackedContext registry}
    (inclusion : BaseReconciliation source target) (a b : (Context.ofBase source).Value) :
    inclusion.value (a * b) = inclusion.value a * inclusion.value b := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      apply BaseContext.Element.ext
      exact inclusion.coefficients.mul a.stored b.stored

/-- Reconciled base transport preserves totalized inversion, including zero. -/
theorem BaseReconciliation.inv {source target : BaseContext.PackedContext registry}
    (inclusion : BaseReconciliation source target) (a : (Context.ofBase source).Value) :
    inclusion.value a⁻¹ = (inclusion.value a)⁻¹ := by
  cases source with
  | pack source =>
    cases target with
    | pack target =>
      apply BaseContext.Element.ext
      exact inclusion.coefficients.inv a.stored

/-- Reconciliation into the same actual context retains every stored value. -/
theorem BaseReconciliation.self_value {base : BaseContext.PackedContext registry}
    (inclusion : BaseReconciliation base base) (a : (Context.ofBase base).Value) :
    inclusion.value a = a := by
  have same := inclusion.produced
  rw [BaseContext.PackedContext.reconcile?_self] at same
  have coefficients := (Option.some.inj same).symm
  cases base with
  | pack base =>
    apply BaseContext.Element.ext
    change inclusion.coefficients.value a.stored = a.stored
    rw [coefficients, BaseContext.FieldEmbedding.identity_value]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.make?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.make?_success

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.inv

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.self_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.self_value

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.make?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.make?_ordered

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.value_eq_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.value_eq_ordered

/-- info: 'Hex.RealClosure.Tower.BaseReconciliation.eq_ofOrdered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.BaseReconciliation.eq_ofOrdered
