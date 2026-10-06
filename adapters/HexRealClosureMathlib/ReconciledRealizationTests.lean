/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ReconciledRealization
public import HexRealClosureMathlib.ReconciledGatherTests

public section

namespace Hex.RealClosure.Tower.ReconciledTests

/-- Two reversed provider keys with any actual algebraic suffix admit one
ordinary reader for all requested values. The ordered factory rejects. -/
theorem reverse_realize {registry : BaseContext.Registry} {R : Type}
    [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R]
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign) (suffix : Suffix (Context.base original))
    (base : BaseContext.PackedContext registry) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R)
    (α β : BaseContext.ConstantKey) (different : α ≠ β)
    (sourceSignature : (BaseContext.PackedContext.pack original).signature = ⟨[α, β], 1⟩)
    (targetSignature : base.signature = ⟨[β, α], 2⟩)
    (values : (index : Fin ([suffix.context] : List (Context registry)).length) →
      List (([suffix.context] : List (Context registry))[index]).Value) :
    (BaseContext.PackedContext.pack original).subsequence? base = none ∧
    ∃ shared : Shared base [suffix.context],
      Shared.gatherReconciled? base [suffix.context] = some shared ∧
        ∃ read : shared.input.context.Value → ℝ, ∃ domain : shared.input.context.Value → Prop,
          shared.Realized following values [] read domain := by
  obtain ⟨rejected, shared, produced, model, _⟩ :=
    reverse_keys original suffix base following reference α β different sourceSignature targetSignature
  obtain ⟨read, domain, realized⟩ := shared.realizeReconciledValues following produced values
  exact ⟨rejected, shared, produced, read, domain, realized⟩

/-- Complete root requests, including their selected child and predecessor
replay inventory, are gathered and realized over reversed provider keys. -/
theorem reverse_request {registry : BaseContext.Registry} {R : Type}
    [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R]
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign) (suffix : Suffix (Context.base original))
    (root : Root suffix.context) (base : BaseContext.PackedContext registry)
    (following : base.Realization) (reference : Tower.Model (Context.ofBase base) R)
    (α β : BaseContext.ConstantKey) (different : α ≠ β)
    (sourceSignature : (BaseContext.PackedContext.pack original).signature = ⟨[α, β], 1⟩)
    (targetSignature : base.signature = ⟨[β, α], 2⟩) :
    (BaseContext.PackedContext.pack original).subsequence? base = none ∧
    ∃ collection : Live.Collection base (Live.rootRequest root),
      (Live.rootRequest root).gatherReconciled? base = some collection ∧
        ∃ read : collection.shared.input.context.Value → ℝ,
          ∃ domain : collection.shared.input.context.Value → Prop,
            collection.shared.Realized following (Live.rootRequest root).inventory [] read domain := by
  have rejected := (BaseContext.ReconstructionTests.reverse_keys (.pack original) base following
    reference α β different sourceSignature targetSignature).1
  have unique : (BaseContext.PackedContext.pack original).signature.constants.Nodup := by
    rw [sourceSignature]
    simp [different]
  have included : (BaseContext.PackedContext.pack original).signature.constants ⊆
      base.signature.constants := by
    rw [sourceSignature, targetSignature]
    intro key member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact member.elim Or.inr Or.inl
  have depth : (BaseContext.PackedContext.pack original).signature.infinitesimals ≤
      base.signature.infinitesimals := by
    rw [sourceSignature, targetSignature]
    change (1 : Nat) ≤ 2
    decide
  have originalBase := Suffix.origin_base original suffix
  have bases : ∀ context ∈ (Live.rootRequest root).owners,
      context.origin.base = suffix.context.origin.base := by
    cases root with
    | point value =>
      intro context member
      simp only [Live.rootRequest, Live.Request.owners, List.map_cons, List.map_nil,
        List.mem_singleton] at member
      subst context
      rfl
    | selected descriptor extension built =>
      intro context member
      simp only [Live.rootRequest, Live.Request.owners, List.map_cons, List.map_nil,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · subst context; rfl
      · subst context
        exact (Root.selected descriptor extension built).origin_base
  obtain ⟨collection, produced, _⟩ :=
    Live.Request.gatherReconciled?_models following reference (Live.rootRequest root) (by
      intro context member
      rw [bases context member, originalBase]
      exact ⟨unique, included, depth⟩)
  obtain ⟨read, domain, realized⟩ := collection.realizeReconciled following produced
  exact ⟨rejected, collection, produced, read, domain, realized⟩

end Hex.RealClosure.Tower.ReconciledTests

/-- info: 'Hex.RealClosure.Tower.ReconciledTests.reverse_realize' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledTests.reverse_realize

/-- info: 'Hex.RealClosure.Tower.ReconciledTests.reverse_request' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledTests.reverse_request
