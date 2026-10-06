/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexRealClosureMathlib.BaseStagedReorder

public section

namespace Hex.RealClosure.BaseContext.ReorderTests

/-- Reverse two actual provider keys while retaining the source infinitesimal
and adding another outer infinitesimal. The ordered factory rejects, the
reconciliation fallback succeeds, and its actual map preserves native signs
and inherited real coefficients from both provider realizations. -/
theorem reverse_keys {registry : Registry} {K L : Type}
    [Lean.Grind.Field K] [DecidableEq K] [Lean.Grind.Field L] [DecidableEq L]
    {sourceSign : K → Int} {targetSign : L → Int}
    (source : Chain registry K sourceSign) (target : Chain registry L targetSign)
    (original : source.Realization registry) (following : target.Realization registry)
    (α β : ConstantKey) (different : α ≠ β)
    (sourceSignature : source.signature = ⟨[α, β], 1⟩)
    (targetSignature : target.signature = ⟨[β, α], 2⟩) :
    target.subsequence? source = none ∧
      ∃ map : FieldEmbedding K L, target.reconcile? source = some map ∧
        (∀ a, targetSign (map.value a) = sourceSign a) ∧
        (∀ a r, original.RealValue a r → following.RealValue (map.value a) r) := by
  have rejected : target.subsequence? source = none := by
    cases produced : target.subsequence? source with
    | none => rfl
    | some map =>
      have accepted := (target.subsequence?_isSome source).mp (by rw [produced]; rfl)
      rw [sourceSignature, targetSignature] at accepted
      have equal : [α, β] = [β, α] := accepted.1.eq_of_length rfl
      have heads := congrArg List.head? equal
      simp only [List.head?_cons, Option.some.injEq] at heads
      exact False.elim (different heads)
  refine ⟨rejected, ?_⟩
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
    (original.reconcile_success following included depth)
  refine ⟨map, produced, ?_, ?_⟩
  · exact following.reconcile_sign source original map produced
  · exact following.reconcile_realValue source original map produced

end Hex.RealClosure.BaseContext.ReorderTests

/-- info: 'Hex.RealClosure.BaseContext.ReorderTests.reverse_keys' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Hex.RealClosure.BaseContext.ReorderTests.reverse_keys
