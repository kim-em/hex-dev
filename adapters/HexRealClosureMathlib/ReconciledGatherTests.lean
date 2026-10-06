/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.ReconciledGatherModel
public import HexRealClosureMathlib.ReconciledLive
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

namespace Live

variable {registry : BaseContext.Registry} {R : Type u}
variable [Field R] [LinearOrder R] [DecidableEq R] [IsStrictOrderedRing R] [IsRealClosed R]

/-- The accepted-native reconciled model supplies root agreement directly. -/
theorem root_agreement {base : BaseContext.PackedContext registry}
    {parent : Context registry} (root : Root parent)
    (descriptor : SignDet.Descriptor parent.Value Signature parent.sign parent.signature)
    (selected : root.selection = .selected descriptor)
    {pre post : Hex.RealClosure.Tower.Live.Request registry}
    {request : Hex.RealClosure.Tower.Live.Request registry}
    (collection : Hex.RealClosure.Tower.Live.Collection base request)
    (split : request = pre ++ Hex.RealClosure.Tower.Live.rootRequest root ++ post)
    {following : base.Realization} {reference : Model (Context.ofBase base) R}
    (produced : request.gatherReconciled? base = some collection) :
    let model := collection.reconciledModel following reference produced
    ∃ (parentModel : Model parent R)
        (predecessor child : Hex.RealClosure.Tower.Live.Frame collection.shared.input.context)
        (fresh : SignDet.Descriptor collection.shared.input.context.Value Signature
          collection.shared.input.context.sign collection.shared.input.context.signature)
        (value : collection.shared.input.context.Value),
      collection.frames[pre.length]? = some predecessor ∧
        collection.frames[pre.length + 1]? = some child ∧
        predecessor.descriptors = [fresh] ∧ child.values = [value] ∧
        model.target.value value = fresh.root model.target.value model.target.zero_iff model.target.one
          model.target.add model.target.sub model.target.mul model.target.nat model.target.sign ∧
        (OwnerReader.reconciled following reference).read parent = some parentModel ∧
        fresh.root model.target.value model.target.zero_iff model.target.one model.target.add
          model.target.sub model.target.mul model.target.nat model.target.sign =
        descriptor.root parentModel.value parentModel.zero_iff parentModel.one parentModel.add parentModel.sub
          parentModel.mul parentModel.nat parentModel.sign :=
  collection.root_agreement root descriptor selected split
    (collection.reconciledModel following reference produced)

end Live

end Hex.RealClosure.Tower.ReconciledTests

/-- info: 'Hex.RealClosure.Tower.ReconciledTests.reverse_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledTests.reverse_keys

/-- info: 'Hex.RealClosure.Tower.ReconciledTests.Live.root_agreement' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.Tower.ReconciledTests.Live.root_agreement
