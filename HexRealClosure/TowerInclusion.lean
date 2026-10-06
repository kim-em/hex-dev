/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosure.TowerCatalog
public import HexRealClosure.TowerTransport

public section

namespace Hex.RealClosure.Tower

variable {registry : BaseContext.Registry}

/-- A checked native inclusion with fixed source and target owners. The
conversion records the actual native steps, and the equality identifies its
returned target with the shared context. -/
structure Inclusion (source target : Context registry) : Type 1 where
  conversion : Conversion source
  context_eq : conversion.context = target

/-- Include one original value in the shared target. -/
@[expose] def Inclusion.value {source target : Context registry}
    (inclusion : Inclusion source target) (a : source.Value) : target.Value :=
  _root_.cast (congrArg Context.Value inclusion.context_eq) (inclusion.conversion.value a)

/-- Retain an inclusion's declared target and its checked native map. -/
@[expose] def Inclusion.native {source target : Context registry}
    (inclusion : Inclusion source target) : Conversion source :=
  Conversion.ofTransport inclusion.value (by
    rcases inclusion with ⟨conversion, same⟩
    cases same
    exact conversion.checked)

/-- Convert all coefficients with the same checked inclusion. -/
@[expose] def Inclusion.polynomial {source target : Context registry}
    (inclusion : Inclusion source target) (p : source.Poly) : target.Poly :=
  DensePoly.ofCoeffs (p.toArray.map inclusion.value)

/-- Retain the original immutable context without rebuilding it. -/
def Inclusion.identity (source : Context registry) : Inclusion source source :=
  ⟨Conversion.identity source, (Conversion.identity_spec source).1⟩

/-- Compose checked inclusions, keeping the original owner. -/
@[expose] def Inclusion.comp {source middle target : Context registry}
    (first : Inclusion source middle) (next : Inclusion middle target) :
    Inclusion source target :=
  let following := next.conversion.cast first.context_eq.symm
  ⟨first.conversion.comp following,
    (first.conversion.comp_spec following).1.trans
      ((next.conversion.cast_spec first.context_eq.symm).1.trans next.context_eq)⟩

private theorem cast_apply {source left right : Context registry} (same : left = right)
    (f : source.Value → left.Value) (g : source.Value → right.Value) (agree : HEq f g)
    (a : source.Value) :
    _root_.cast (congrArg Context.Value same) (f a) = g a := by
  cases same
  cases eq_of_heq agree
  rfl

/-- Read a checked conversion through its specified target and value map. -/
theorem Inclusion.value_eq {source target : Context registry}
    (conversion : Conversion source) (same : conversion.context = target)
    (value : source.Value → target.Value) (agree : HEq conversion.value value)
    (a : source.Value) :
    (⟨conversion, same⟩ : Inclusion source target).value a = value a :=
  cast_apply same conversion.value value agree a

/-- Composition applies the two cached inclusion maps in order. -/
theorem Inclusion.comp_value {source middle target : Context registry}
    (first : Inclusion source middle) (next : Inclusion middle target) (a : source.Value) :
    (first.comp next).value a = next.value (first.value a) := by
  rcases first with ⟨first, same⟩
  cases same
  rcases next with ⟨next, same⟩
  cases same
  have spec := first.comp_spec next
  simpa only [Inclusion.comp, Inclusion.value, Conversion.cast, cast_eq] using
    cast_apply spec.1 (first.comp next).value (fun a => next.value (first.value a)) spec.2 a

/-- Identity reads the original value in its original context. -/
theorem Inclusion.identity_value (source : Context registry) (a : source.Value) :
    (Inclusion.identity source).value a = a :=
  cast_apply (Conversion.identity_spec source).1 (Conversion.identity source).value id
    (Conversion.identity_spec source).2 a

/-- Identity before an inclusion preserves its value map. -/
theorem Inclusion.id_comp {source target : Context registry}
    (inclusion : Inclusion source target) (a : source.Value) :
    ((Inclusion.identity source).comp inclusion).value a = inclusion.value a := by
  rw [Inclusion.comp_value, Inclusion.identity_value]

/-- Identity after an inclusion preserves its value map. -/
theorem Inclusion.comp_id {source target : Context registry}
    (inclusion : Inclusion source target) (a : source.Value) :
    (inclusion.comp (Inclusion.identity target)).value a = inclusion.value a := by
  rw [Inclusion.comp_value, Inclusion.identity_value]

/-- Composition is associative on all original-owner values. -/
theorem Inclusion.comp_assoc {source middle later target : Context registry}
    (first : Inclusion source middle) (next : Inclusion middle later)
    (last : Inclusion later target) (a : source.Value) :
    ((first.comp next).comp last).value a = (first.comp (next.comp last)).value a := by
  simp only [Inclusion.comp_value]

/-- Extend a completed staged base by finitely many infinitesimals, using
constant-rational-function inclusions at every actual native level. -/
def Conversion.extendBase (base : BaseContext.PackedContext registry) :
    Nat → Conversion (Context.ofBase base)
  | 0 => Conversion.identity (Context.ofBase base)
  | n + 1 => by
    cases base with
    | pack base =>
      let first := Conversion.infinitesimal base
      let next := Conversion.extendBase (.pack base.infinitesimal) n
      exact first.comp (next.cast (Conversion.infinitesimal_spec base).1.symm)

/-- The iterated checked conversion returns precisely the native extended base. -/
theorem Conversion.extendBase_context (base : BaseContext.PackedContext registry) (n : Nat) :
    (Conversion.extendBase base n).context = Context.ofBase (base.extend n) := by
  induction n generalizing base with
  | zero => exact (Conversion.identity_spec _).1
  | succ n ih =>
    cases base with
    | pack base =>
      let first := Conversion.infinitesimal base
      let next := Conversion.extendBase (.pack base.infinitesimal) n
      have final : Context.ofBase ((BaseContext.PackedContext.pack base.infinitesimal).extend n) =
          Context.ofBase ((BaseContext.PackedContext.pack base).extend (n + 1)) :=
        congrArg Context.ofBase
          (BaseContext.PackedContext.extend_infinitesimal (.pack base) n)
      exact (first.comp_spec (next.cast (Conversion.infinitesimal_spec base).1.symm)).1.trans
        (((next.cast_spec (Conversion.infinitesimal_spec base).1.symm).1).trans
          ((ih (.pack base.infinitesimal)).trans final))

/-- A finite increase in infinitesimal depth gives a checked inclusion of the
whole staged predecessor into its actual extended base. -/
def Inclusion.extendBase (base : BaseContext.PackedContext registry) (n : Nat) :
    Inclusion (Context.ofBase base) (Context.ofBase (base.extend n)) :=
  ⟨Conversion.extendBase base n, Conversion.extendBase_context base n⟩

/-- Check the complete real-key subsequence and infinitesimal order before
including a staged base. The original keys are retained in the target;
unrelated paths and decreasing depth are rejected. -/
def Inclusion.base? (source target : BaseContext.PackedContext registry) :
    Option (Inclusion (Context.ofBase source) (Context.ofBase target)) :=
  (BaseInclusion.make? source target).map fun inclusion =>
    ⟨Conversion.base inclusion, (Conversion.base_spec inclusion).1⟩

private theorem Inclusion.base?_eq_proof (source target : BaseContext.PackedContext registry) :
    Inclusion.base? source target = (BaseInclusion.make? source target).map
      (fun inclusion => ⟨Conversion.base inclusion, (Conversion.base_spec inclusion).1⟩) := rfl

/-- Expose the actual checked coefficient map used by shared gathering. -/
theorem Inclusion.base?_eq (source target : BaseContext.PackedContext registry) :
    Inclusion.base? source target = (BaseInclusion.make? source target).map
      (fun inclusion => ⟨Conversion.base inclusion, (Conversion.base_spec inclusion).1⟩) :=
  Inclusion.base?_eq_proof source target

/-- Staged-base compatibility is checked on the full real-key subsequence and
on the required order of the retained infinitesimals. -/
theorem Inclusion.base?_isSome (source target : BaseContext.PackedContext registry) :
    (Inclusion.base? source target).isSome = true ↔
      List.Sublist source.signature.constants target.signature.constants ∧ source.depth ≤ target.depth := by
  simp only [Inclusion.base?, Option.isSome_map]
  exact BaseInclusion.make?_isSome source target

/-- Reconcile original provider order once, then retain the checked map as
a fixed-owner tower inclusion. Ordered subsequence maps remain the fast path. -/
def Inclusion.reconcileBase? (source target : BaseContext.PackedContext registry) :
    Option (Inclusion (Context.ofBase source) (Context.ofBase target)) :=
  (BaseReconciliation.make? source target).map fun inclusion =>
    ⟨Conversion.reconcileBase inclusion, (Conversion.reconcileBase_spec inclusion).1⟩

private theorem Inclusion.reconcileBase?_eq_proof (source target : BaseContext.PackedContext registry) :
    Inclusion.reconcileBase? source target = (BaseReconciliation.make? source target).map
      (fun inclusion => ⟨Conversion.reconcileBase inclusion, (Conversion.reconcileBase_spec inclusion).1⟩) := rfl

/-- Expose the exact cached coefficient factory retained by reconciliation. -/
theorem Inclusion.reconcileBase?_eq (source target : BaseContext.PackedContext registry) :
    Inclusion.reconcileBase? source target = (BaseReconciliation.make? source target).map
      (fun inclusion => ⟨Conversion.reconcileBase inclusion, (Conversion.reconcileBase_spec inclusion).1⟩) :=
  Inclusion.reconcileBase?_eq_proof source target

/-- Every distinct-key inclusion with sufficient depth produces a fixed-owner
tower inclusion from the actual native staged factory. -/
theorem Inclusion.reconcileBase?_success (source target : BaseContext.PackedContext registry)
    (sourceUnique : source.signature.constants.Nodup)
    (targetUnique : target.signature.constants.Nodup)
    (included : source.signature.constants ⊆ target.signature.constants)
    (depth : source.signature.infinitesimals ≤ target.signature.infinitesimals) :
    (Inclusion.reconcileBase? source target).isSome = true := by
  simp only [Inclusion.reconcileBase?, Option.isSome_map]
  exact BaseReconciliation.make?_success source target sourceUnique targetUnique included depth

/-- An available ordered tower inclusion is the exact result of the reconciled
factory, retaining its context, cached value map and all existing model facts. -/
theorem Inclusion.reconcileBase?_ordered
    {source target : BaseContext.PackedContext registry}
    (ordered : Inclusion (Context.ofBase source) (Context.ofBase target))
    (produced : Inclusion.base? source target = some ordered) :
    Inclusion.reconcileBase? source target = some ordered := by
  rw [Inclusion.base?_eq] at produced
  cases factory : BaseInclusion.make? source target with
  | none => simp only [factory, Option.map_none] at produced; contradiction
  | some coefficients =>
    simp only [factory, Option.map_some, Option.some.injEq] at produced
    subst ordered
    rw [Inclusion.reconcileBase?_eq, BaseReconciliation.make?_ordered coefficients, Option.map_some]
    simp only [Conversion.reconcileBase_ordered]

end Hex.RealClosure.Tower

/-- info: 'Hex.RealClosure.Tower.Inclusion.identity_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.identity_value

/-- info: 'Hex.RealClosure.Tower.Inclusion.comp_value' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.comp_value

/-- info: 'Hex.RealClosure.Tower.Inclusion.comp_assoc' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.comp_assoc

/-- info: 'Hex.RealClosure.Tower.Inclusion.reconcileBase?_success' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.reconcileBase?_success

/-- info: 'Hex.RealClosure.Tower.Inclusion.reconcileBase?_ordered' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.Inclusion.reconcileBase?_ordered
