/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Predicates
public import HexPermGroup.Search.NormalizerPredicate

public section

namespace Hex.PermGroup.Normal

/-- Normality checked on symmetric generators already certified in the ambient
chain. The checker does not run the generator normalization producer. -/
@[expose] def check (G H : Group n) : Bool :=
  decide (∀ i : Fin G.chain.generators.size, ∀ j : Fin H.generators.size,
    H.contains (G.chain.generators[i.val].conj H.generators[j.val]) = true)

/-- A full pass stops at the first failed conjugate. The nested scans do not
allocate the Cartesian product of the generator arrays. -/
@[expose] def failure? (G H : Group n) : Option (Fin G.chain.generators.size × Fin H.generators.size) :=
  (List.finRange G.chain.generators.size).findSome? fun i =>
    ((List.finRange H.generators.size).find? fun j =>
      !H.contains (G.chain.generators[i.val].conj H.generators[j.val])).map fun j => (i, j)

theorem failure_none (G H : Group n) : failure? G H = none ↔ check G H = true := by
  simp [failure?, check]

theorem failure_sound (G H : Group n) (i : Fin G.chain.generators.size) (j : Fin H.generators.size)
    (h : failure? G H = some (i, j)) :
    ¬Generated H.generators (G.chain.generators[i.val].conj H.generators[j.val]) := by
  obtain ⟨i', _, hi⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨j', hj, he⟩ := Option.map_eq_some_iff.mp hi
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
  have hf := List.find?_some hj
  intro hp
  simp [(H.contains_iff _).mpr hp] at hf

theorem check_iff (G H : Group n) : check G H = true ↔
    ∀ g p : Perm n, Generated G.generators g → Generated H.generators p →
      Generated H.generators (g.conj p) := by
  constructor
  · intro hc g p hg hp
    have step (i : Fin G.chain.generators.size) :
        (Search.Predicate.normalizer H).test G.chain.generators[i.val] = true := by
      have hf := of_decide_eq_true hc i
      obtain ⟨j, hj, he⟩ := Array.mem_iff_getElem.mp
        (G.chain_symmetric _ (Array.getElem_mem i.isLt))
      have hb := of_decide_eq_true hc ⟨j, hj⟩
      change Search.Normalizer.test H G.chain.generators[i.val] = true
      simp only [Search.Normalizer.test, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hf, he ▸ hb⟩
    have ht := (Search.Predicate.normalizer H).generated step ((G.chain_generated g).mpr hg)
    exact ((Search.Normalizer.test_iff H g).mp ht p).mp hp
  · intro h
    apply decide_eq_true
    intro i j
    apply (H.contains_iff _).mpr
    exact h _ _ ((G.chain_generated _).mp (.generator (Array.getElem_mem i.isLt)))
      (.generator (Array.getElem_mem j.isLt))

theorem check_normal (G H : Group n) (h : H.IsSubgroup G) :
    check G H = true ↔ H.isNormal G h = true :=
  (check_iff G H).trans (H.isNormal_iff G h).symm

end Hex.PermGroup.Normal
