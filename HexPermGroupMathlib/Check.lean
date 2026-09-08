/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Chain.Order
public import HexPermGroupMathlib.Word
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace Hex.PermGroup

/-- The Cartesian choices have the chain's orbit-product cardinality. -/
theorem choice_card (c : Chain n) : Nat.card c.Choice = c.orbitProduct := by
  induction c with
  | leaf S words => simp [Chain.Choice, Chain.orbitProduct]
  | cons level tail ih => simp [Chain.Choice, Chain.orbitProduct, Nat.card_prod, ih]

/-- The representative product identifies Cartesian choices with the original
mathematical subgroup. This equivalence is used for cardinality; executable
membership continues to use sifting. -/
noncomputable def choiceEquiv {S : Array (Perm n)} {c : Chain n}
    (h : checkChain S c = true) : c.Choice ≃ closure S := by
  have hc := of_decide_eq_true h
  let f : c.Choice → closure S := fun digits =>
    ⟨(c.value digits).toEquiv, generated_iff_mem.mp
      (checkWords_sound hc.2.1 (Chain.value_generated hc.2.2 digits))⟩
  apply Equiv.ofBijective f
  constructor
  · intro u v he
    apply Chain.value_injective hc.2.2
    have hv := congrArg (fun e : closure S => Perm.ofEquiv e.val) he
    simpa [f] using hv
  · intro e
    have hp : Generated S (Perm.ofEquiv e.val) := by
      apply generated_iff_mem.mpr
      simpa only [Perm.toEquiv_ofEquiv] using e.property
    have hg := (Chain.checkFrom_sound hc.2.2 _).mp ((sift_iff h _).mpr hp)
    obtain ⟨digits, hd⟩ := Chain.value_surjective hc.2.2 hg
    refine ⟨digits, ?_⟩
    apply Subtype.ext
    simp [f, hd]

/-- The orbit-size product is the exact cardinality of the original subgroup. -/
theorem checkChain_card {S : Array (Perm n)} {c : Chain n}
    (h : checkChain S c = true) : c.orbitProduct = Nat.card (closure S) := by
  rw [← choice_card]
  exact Nat.card_congr (choiceEquiv h)

/-- Headline complete-chain correspondence: exact membership and exact order,
with the action degree and original generator array retained. -/
theorem checkChain_spec {S : Array (Perm n)} {c : Chain n}
    (h : checkChain S c = true) :
    (∀ p : Perm n, c.accepts 0 p = true ↔ p.toEquiv ∈ closure S) ∧
      c.orbitProduct = Nat.card (closure S) :=
  ⟨fun p => (sift_iff h p).trans generated_iff_mem, checkChain_card h⟩

end Hex.PermGroup
