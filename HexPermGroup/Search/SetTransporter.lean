/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.First
public import HexPermGroup.Search.Sets

public section

namespace Hex.PermGroup.Search.Sets

@[expose] def cardinality (A : Vector Bool n) : Nat := (List.finRange n).countP A.get

theorem cardinality_eq (A B : Vector Bool n) (p : Perm n) (h : test A B p = true) :
    cardinality A = cardinality B := by
  have hn : ((List.finRange n).map p.get).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    apply (List.nodup_finRange n).imp
    intro x y hxy he
    exact hxy (p.get_inj he)
  have he : ((List.finRange n).map p.get).Perm (List.finRange n) := by
    apply (List.perm_ext_iff_of_nodup hn (List.nodup_finRange n)).mpr
    intro x
    simp only [List.mem_map, List.mem_finRange, true_and, iff_true]
    exact p.get_surj x
  have hc := he.countP_eq B.get
  simp only [List.countP_map, Function.comp_def] at hc
  have hf : (fun x => B.get (p.get x)) = A.get := funext (fun x => ((of_decide_eq_true h) x).symm)
  rw [hf] at hc
  exact hc

/-- A cardinality mismatch excludes all permutations, before any chain
traversal; other reasons identify a violated partial-image constraint. -/
inductive TransportReason (n : Nat) where
  | cardinality
  | refinement (reason : Reason n)

@[expose] def transporter (G : Group n) (A B : Vector Bool n) : Pruner G (test A B) :=
  let unequal := decide (cardinality A ≠ cardinality B)
  { Reason := TransportReason n
    reject t r := match r with
      | .cardinality => unequal
      | .refinement r => reject A B t r
    sound t r hr p hp := by
      cases r with
      | cardinality =>
        apply Bool.eq_false_iff.mpr
        intro ht
        exact (of_decide_eq_true hr) (cardinality_eq A B p ht)
      | refinement r => exact reject_sound A B t r hr p hp
    trials _ := if unequal then .singleton .cardinality else (trials n).map .refinement }

end Hex.PermGroup.Search.Sets

namespace Hex.PermGroup.Group

/-- A checked transporter word or a complete failure certificate. The source
and target subsets need not be in the same orbit. -/
@[expose] def setTransporterSearch (G : Group n) (A B : Vector Bool n) :
    Search.Answer (Search.Sets.transporter G A B) :=
  Search.first (Search.Sets.transporter G A B)

@[expose] def setTransporter? (G : Group n) (A B : Vector Bool n) : Option (Element G) :=
  (G.setTransporterSearch A B).element? (Search.Sets.transporter G A B)

theorem setTransporter_image (G : Group n) (A B : Vector Bool n) (p : Element G)
    (h : G.setTransporter? A B = some p) : (Action.subsets G).act p A = B :=
  (Search.Sets.test_action G A B p).mp
    (Search.Answer.some_spec (Search.Sets.transporter G A B) (G.setTransporterSearch A B) p h)

theorem setTransporter_none (G : Group n) (A B : Vector Bool n) :
    G.setTransporter? A B = none ↔ ¬ ∃ p : Element G, (Action.subsets G).act p A = B := by
  rw [setTransporter?, Search.Answer.none_spec]
  simp only [Search.Sets.test_action]

theorem setTransporter_cardinality (G : Group n) (A B : Vector Bool n)
    (h : Search.Sets.cardinality A ≠ Search.Sets.cardinality B) : G.setTransporter? A B = none := by
  apply (G.setTransporter_none A B).mpr
  rintro ⟨p, hp⟩
  exact h (Search.Sets.cardinality_eq A B p.val ((Search.Sets.test_action G A B p).mpr hp))

/-- The relative permutation to any one transporter lies in the source set
stabilizer exactly when the original permutation is another transporter. -/
theorem mem_transporter_coset (G : Group n) (A B : Vector Bool n) (t : Element G)
    (ht : (Action.subsets G).act t A = B) (p : Perm n) :
    Generated (G.setStabilizer A).generators (t.val.inv.comp p) ↔
      Generated G.generators p ∧ Search.Sets.test A B p = true := by
  rw [mem_setStabilizer]
  have ht := of_decide_eq_true ((Search.Sets.test_action G A B t).mpr ht)
  constructor
  · rintro ⟨hp, hs⟩
    refine ⟨?_, ?_⟩
    · simpa only [← Perm.comp_assoc, Perm.comp_inv_self, Perm.id_comp] using t.property.comp hp
    · apply decide_eq_true
      intro x
      have he := (hs x).trans (ht ((t.val.inv.comp p).get x))
      simpa only [Perm.get_comp, Perm.get_inv_get] using he
  · rintro ⟨hp, hs⟩
    refine ⟨t.property.inv.comp hp, ?_⟩
    intro x
    have he := ht ((t.val.inv.comp p).get x)
    simp only [Perm.get_comp, Perm.get_inv_get] at he
    simpa only [Perm.get_comp] using ((of_decide_eq_true hs) x).trans he.symm

/-- All transporters are the left coset `t * setStabilizer G A`, with the
same multiplication order as the executable action. -/
theorem setTransporter_coset (G : Group n) (A B : Vector Bool n) (t p : Element G)
    (ht : (Action.subsets G).act t A = B) :
    (Action.subsets G).act p A = B ↔
      ∃ k : Element (G.setStabilizer A), p.val = t.val.comp k.val := by
  rw [← Search.Sets.test_action]
  constructor
  · intro hp
    refine ⟨⟨t.val.inv.comp p.val, (G.mem_transporter_coset A B t ht p.val).mpr ⟨p.property, hp⟩⟩, ?_⟩
    simp only [← Perm.comp_assoc, Perm.comp_inv_self, Perm.id_comp]
  · rintro ⟨k, hk⟩
    apply ((G.mem_transporter_coset A B t ht p.val).mp ?_).2
    simpa only [hk, ← Perm.comp_assoc, Perm.inv_comp_self, Perm.id_comp] using k.property

end Hex.PermGroup.Group
