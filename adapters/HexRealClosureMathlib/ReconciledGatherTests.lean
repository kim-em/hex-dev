/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ReconciledGatherModel
public import HexRealClosureMathlib.BaseReconstructionTests

public section

namespace Hex.RealClosure.Tower.ReconciledTests

/-- A full algebraic suffix over two reversed providers enters the shared
target using only its target realization. No source interpretation, root
agreement or cache-coherence premise is supplied. -/
theorem reverse_keys {registry : BaseContext.Registry} {R : Type u}
    [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R]
    {B : Type} [Lean.Grind.Field B] [DecidableEq B] {sign : B → Int}
    (original : BaseContext.Context registry B sign)
    (suffix : Suffix (Context.base original))
    (base : BaseContext.PackedContext registry) (following : base.Realization)
    (reference : Tower.Model (Context.ofBase base) R)
    (α β : BaseContext.ConstantKey) (different : α ≠ β)
    (sourceSignature : (BaseContext.PackedContext.pack original).signature = ⟨[α, β], 1⟩)
    (targetSignature : base.signature = ⟨[β, α], 2⟩) :
    (BaseContext.PackedContext.pack original).subsequence? base = none ∧
    ∃ shared : Shared base [suffix.context],
      Shared.gatherReconciled? base [suffix.context] = some shared ∧
        ∃ _model : Shared.Model (reader := OwnerReader.reconciled following reference)
            shared following reference,
          ∀ a : suffix.context.Value,
            shared.input.context.sign (shared.value 0 a) = suffix.context.sign a := by
  refine ⟨(BaseContext.ReconstructionTests.reverse_keys (.pack original) base following
    reference α β different sourceSignature targetSignature).1, ?_⟩
  have sourceUnique : (BaseContext.PackedContext.pack original).signature.constants.Nodup := by
    have reversed : (BaseContext.PackedContext.pack original).signature.constants =
        base.signature.constants.reverse := by
      rw [sourceSignature, targetSignature]
      rfl
    rw [reversed]
    exact List.nodup_reverse.mpr following.keys_nodup
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
  have originBase : suffix.context.origin.base = .pack original :=
    Suffix.origin_base original suffix
  obtain ⟨shared, produced, ⟨model⟩⟩ :=
    Shared.gatherReconciled?_models following reference [suffix.context] (by
      intro source member
      have same : source = suffix.context := List.mem_singleton.mp member
      subst source
      rw [originBase]
      exact ⟨sourceUnique, included, depth⟩)
  exact ⟨shared, produced, model, fun a => model.sign 0 a⟩

end Hex.RealClosure.Tower.ReconciledTests

/-- info: 'Hex.RealClosure.Tower.ReconciledTests.reverse_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledTests.reverse_keys
