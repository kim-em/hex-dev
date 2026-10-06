/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseReconstruction

public section

namespace Hex.RealClosure.BaseContext.ReconstructionTests

/-- Reverse two providers and retain the source infinitesimal using only the
target's actual realization. The ordered reader rejects; reconstruction and
source-field interpretation are derived from the checked reconciliation. -/
theorem reverse_keys {registry : Registry} {R : Type u} [Field R] [LinearOrder R]
    (source target : PackedContext registry) (following : target.Realization)
    (targetModel : Tower.Model (Tower.Context.ofBase target) R)
    (α β : ConstantKey) (different : α ≠ β)
    (sourceSignature : source.signature = ⟨[α, β], 1⟩)
    (targetSignature : target.signature = ⟨[β, α], 2⟩) :
    source.subsequence? target = none ∧
      ∃ map : Tower.BaseReconciliation source target,
        Tower.BaseReconciliation.make? source target = some map ∧
        Nonempty source.Realization ∧
        (Tower.BaseReconciliation.Model.deriveCanonical following map targetModel).target = targetModel ∧
        ∀ a, (Tower.BaseReconciliation.Model.deriveCanonical following map targetModel).source.value a =
          targetModel.value (map.value a) := by
  have rejected : source.subsequence? target = none := by
    cases produced : source.subsequence? target with
    | none => rfl
    | some map =>
      have accepted := (source.subsequence?_isSome target).mp (by rw [produced]; rfl)
      rw [sourceSignature, targetSignature] at accepted
      have equal : [α, β] = [β, α] := accepted.1.eq_of_length rfl
      have heads := congrArg List.head? equal
      simp only [List.head?_cons, Option.some.injEq] at heads
      exact False.elim (different heads)
  refine ⟨rejected, ?_⟩
  have reversed : source.signature.constants = target.signature.constants.reverse := by
    rw [sourceSignature, targetSignature]
    rfl
  have sourceUnique : source.signature.constants.Nodup := by
    rw [reversed]
    exact List.nodup_reverse.mpr following.keys_nodup
  have included : source.signature.constants ⊆ target.signature.constants := by
    rw [sourceSignature, targetSignature]
    intro key member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
    exact member.elim Or.inr Or.inl
  have depth : source.signature.infinitesimals ≤ target.signature.infinitesimals := by
    rw [sourceSignature, targetSignature]
    change (1 : Nat) ≤ 2
    decide
  obtain ⟨map, produced⟩ := Option.isSome_iff_exists.mp
    (Tower.BaseReconciliation.make?_success source target sourceUnique following.keys_nodup included depth)
  have success := following.reconstruct?_accepted source (by rw [map.produced]; rfl)
  refine ⟨map, produced, ⟨(following.reconstruct? source).get success⟩,
    Tower.BaseReconciliation.Model.deriveCanonical_target following map targetModel, ?_⟩
  intro a
  have preserved := (Tower.BaseReconciliation.Model.deriveCanonical following map targetModel).value a
  rw [Tower.BaseReconciliation.Model.deriveCanonical_target] at preserved
  exact preserved.symm

end Hex.RealClosure.BaseContext.ReconstructionTests

/-- info: 'Hex.RealClosure.BaseContext.ReconstructionTests.reverse_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.ReconstructionTests.reverse_keys
