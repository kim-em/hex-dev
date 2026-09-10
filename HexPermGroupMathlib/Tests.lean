/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import all Init.Data.Array.Basic

import HexPermGroupMathlib

namespace Hex.PermGroup.Tests

example (p q : Perm n) : Perm.equiv (p * q) = Perm.equiv p * Perm.equiv q :=
  Perm.equiv.map_mul p q

example (e : Equiv.Perm (Fin n)) : (Perm.ofEquiv e).toEquiv = e := by simp

example (p : Perm n) : p.order = orderOf p.toEquiv := p.order_eq_orderOf

example (p q : Perm n) : (p.comp q).sign = p.sign * q.sign := p.sign_comp q

example (p q : Perm n) : ((q.comp p).comp q.inv).cycleType = p.cycleType := p.cycleType_conj q

example (p : Perm n) : (p.cycleType.toList : Multiset Nat) =
    Equiv.Perm.cycleType p.toEquiv +
      Multiset.replicate (n - (Equiv.Perm.support p.toEquiv).card) 1 := p.cycleType_eq_mathlib

private def mixedCycles : Perm 6 := ⟨#v[1, 2, 0, 4, 3, 5], by decide, by decide⟩

example : mixedCycles.cycleType = #[1, 2, 3] ∧ mixedCycles.order = 6 ∧ mixedCycles.sign = -1 :=
  by decide +kernel

example : mixedCycles.toEquiv ^ 6 = 1 := by
  rw [← Perm.toEquiv_pow]
  have h : mixedCycles.pow 6 = Perm.id 6 := mixedCycles.pow_order
  rw [h, Perm.toEquiv_id]

example : (Perm.id 0).order = 1 ∧ (Perm.id 0).cycleType = #[] ∧ (Perm.id 0).sign = 1 :=
  by decide +kernel

example (S : Array (Perm n)) (p : Perm n) :
    Generated S p ↔ p.toEquiv ∈ closure S := generated_iff_mem

example (S : Array (Perm n)) : (Group.ofGenerators S).order = Nat.card (closure S) :=
  (Group.ofGenerators_spec S).2

example (S : Array (Perm n)) (p : Perm n) :
    (Group.ofGenerators S).contains p = true ↔ p.toEquiv ∈ closure S :=
  (Group.ofGenerators_spec S).1 p

example (G H : Group n) : G.sameGroup H = true ↔ closure G.generators = closure H.generators :=
  Group.sameGroup_spec G H

example (G H : Group n) : closure (G.join H).generators = closure G.generators ⊔ closure H.generators :=
  Group.join_spec G H

example (G : Group n) (a : Fin n) : closure (G.stabilizer a).generators =
    closure G.generators ⊓ MulAction.stabilizer (Equiv.Perm (Fin n)) a :=
  Group.stabilizer_spec G a

example (H G : Group n) (h : H.IsSubgroup G) : H.isNormal G h = true ↔
    ((closure H.generators).subgroupOf (closure G.generators)).Normal :=
  Group.isNormal_spec H G h

example (G : Group n) (p : Element G) : G.rankEquiv.symm (G.rankEquiv p) = p :=
  G.rankEquiv.symm_apply_apply p

example (G : Group n) (source : PMF (Fin G.order)) (p : Element G) :
    (source.map G.unrank) p = source (G.rank p) :=
  Group.unrank_probability G source p

private def swap : Perm 3 := ⟨#v[1, 0, 2], by decide, by decide⟩
private def inverse : Program := ⟨#[.generator 0, .inv 0], 1⟩

example : swap.inv.toEquiv ∈ closure #[swap] :=
  checkWord_spec (by decide : checkWord #[swap] swap.inv inverse = true)

example : (Perm.id 0).toEquiv ∈ closure (#[] : Array (Perm 0)) :=
  checkWord_spec (program := ⟨#[.id], 0⟩) (by decide)

private def swap2 : Perm 2 := ⟨#v[1, 0], by decide, by decide⟩
private def chain2 : Chain 2 :=
  .cons
    { generators := #[swap2]
      words := #v[⟨#[.generator 0], 0⟩]
      orbit :=
        { points := #[0, 1]
          lookup := #v[some 0, some 1]
          reps := #v[Perm.id 2, swap2]
          words := #v[⟨#[.id], 0⟩, ⟨#[.generator 0], 0⟩] } }
    (.cons
      { generators := #[]
        words := #v[]
        orbit :=
          { points := #[1]
            lookup := #v[none, some 0]
            reps := #v[Perm.id 2]
            words := #v[⟨#[.id], 0⟩] } }
      (.leaf #[] #v[]))

private theorem chain2_valid : checkChain #[swap2] chain2 = true := by decide +kernel

example : Nat.card (closure #[swap2]) = 2 :=
  (checkChain_card chain2_valid).symm

private def group2 : Group 2 := ⟨#[swap2], chain2, chain2_valid⟩
example : group2.order = 2 := by decide
example (p q : Element group2) :
    Element.equiv group2 (p * q) = Element.equiv group2 p * Element.equiv group2 q :=
  (Element.equiv group2).map_mul p q

example : MulAction.IsPreprimitive (closure group2.generators) (Fin 2) :=
  (group2.primitive_spec.mp (Primitivity.check_sound (by decide) (by decide +kernel)
    (by decide +kernel : Primitivity.check group2 0 #v[[], [(0, 1)]] = true))).2

example (G : Group n) (pairs : List (Fin n × Fin n)) :
    IsLeast {r : Setoid (Fin n) |
      (∀ g ∈ closure G.generators, ∀ x y, r x y → r (g x) (g y)) ∧
        ∀ q ∈ pairs, r q.1 q.2} (G.blocks pairs).toSetoid := G.blocks_spec pairs

example (G : Group n) (p : Partition n) (hp : p.IsInvariant G) (a : BlockAction G p hp) :
    G.order = a.kernel.group.order * a.image.group.order := a.order_mul_image

example (G H : Group n) (h : H.IsSubgroup G) :
    (closure (G.normalClosure H h).generators).subgroupOf (closure G.generators) =
      Subgroup.normalClosure
        ((closure H.generators).subgroupOf (closure G.generators) : Set (closure G.generators)) :=
  G.normalClosure_spec H h

example (G H : Group n) (h : H.IsSubgroup G) :
    (closure (G.core H h).generators).subgroupOf (closure G.generators) =
      ((closure H.generators).subgroupOf (closure G.generators)).normalCore := G.core_spec H h

example (G : Group n) : closure G.derived.generators = ⁅closure G.generators, closure G.generators⁆ :=
  G.derived_spec

example (G : Group n) : G.isSolvable = true ↔ _root_.Group.IsSolvable (closure G.generators) :=
  G.isSolvable_spec

example (G : Group n) (c : Series.Certificate n) (h : Series.check G c = true) :
    c.accepted = true ↔ _root_.Group.IsSolvable (closure G.generators) :=
  (Series.check_spec h).trans G.solvable_spec

example (G : Group n) (H : Group m) :
    Nonempty (closure (G.directProduct H).generators ≃* closure G.generators × closure H.generators) :=
  ⟨DirectProduct.groupEquiv G H⟩

example (G : Group n) (H : Group m) (p : Element G) (q : Element H) :
    DirectProduct.groupEquiv G H (Element.equiv (G.directProduct H) (DirectProduct.pair p q)) =
      (Element.equiv G p, Element.equiv H q) := DirectProduct.groupEquiv_pair G H p q

example (G : Group n) (H : Group m) (hn : 0 < n) :
    Nonempty (closure (G.wreathProduct H hn).generators ≃*
      SemidirectProduct (Fin m → closure G.generators) (closure H.generators) (WreathProduct.subgroupShift G H)) :=
  ⟨WreathProduct.groupEquiv G H hn⟩

example (G : Group n) (H : Group m) (hn : 0 < n) :
    (WreathProduct.inlHom G H hn).range = (WreathProduct.topHom G H hn).ker := WreathProduct.range_inl G H hn

end Hex.PermGroup.Tests
