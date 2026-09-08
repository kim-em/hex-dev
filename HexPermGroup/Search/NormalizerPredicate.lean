/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Search.Predicate
public import HexPermGroup.Conjugate

public section

namespace Hex.PermGroup.Search

namespace Normalizer

/-- Check conjugates of original generators in both directions. This proves
subgroup equality, including when the second group lies outside the ambient one. -/
@[expose] def test (H : Group n) (p : Perm n) : Bool :=
  decide (∀ i : Fin H.generators.size, H.contains (p.conj H.generators[i.val]) = true) &&
    decide (∀ i : Fin H.generators.size, H.contains (p.inv.conj H.generators[i.val]) = true)

theorem preserves (H : Group n) (p : Perm n)
    (h : ∀ i : Fin H.generators.size, H.contains (p.conj H.generators[i.val]) = true)
    {q : Perm n} (hq : Generated H.generators q) : Generated H.generators (p.conj q) := by
  apply hq.lift (P := fun q => Generated H.generators (p.conj q))
  · simpa using (Generated.id : Generated H.generators (Perm.id n))
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hr
    exact (H.contains_iff _).mp (h ⟨i, hi⟩)
  · intro r s hr hs
    simpa only [Perm.conj_comp] using hr.comp hs
  · intro r hr
    simpa only [Perm.conj_inv] using hr.inv

theorem test_iff (H : Group n) (p : Perm n) : test H p = true ↔
    ∀ q : Perm n, Generated H.generators q ↔ Generated H.generators (p.conj q) := by
  rw [test, Bool.and_eq_true]
  constructor
  · rintro ⟨hf, hb⟩ q
    refine ⟨preserves H p (of_decide_eq_true hf), ?_⟩
    intro hq
    simpa only [Perm.inv_conj_conj] using preserves H p.inv (of_decide_eq_true hb) hq
  · intro h
    constructor <;> apply decide_eq_true <;> intro i <;> apply (H.contains_iff _).mpr
    · exact (h _).mp (.generator (Array.getElem_mem i.isLt))
    · apply (h _).mpr
      simpa only [Perm.conj_inv_conj] using
        (Generated.generator (Array.getElem_mem i.isLt) : Generated H.generators H.generators[i.val])

end Normalizer

@[expose] def Predicate.normalizer (H : Group n) : Predicate n where
  test := Normalizer.test H
  id := (Normalizer.test_iff H _).mpr (by simp)
  comp p q hp hq := by
    apply (Normalizer.test_iff H _).mpr
    intro r
    rw [Perm.comp_conj]
    exact ((Normalizer.test_iff H q).mp hq r).trans ((Normalizer.test_iff H p).mp hp (q.conj r))
  inv p hp := by
    apply (Normalizer.test_iff H _).mpr
    intro r
    simpa only [Perm.conj_inv_conj] using ((Normalizer.test_iff H p).mp hp (p.inv.conj r)).symm

theorem Predicate.normalizer_iff (H : Group n) (p : Perm n) :
    (normalizer H).test p = true ↔
      ∀ q : Perm n, Generated H.generators q ↔ Generated H.generators (p.conj q) :=
  Normalizer.test_iff H p

end Hex.PermGroup.Search
