/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles.Type
public import HexPermGroupMathlib.Cycles.Factors

public section

namespace Hex.Perm.Cycle

theorem split_ones (xs : List Nat) (hp : ∀ x ∈ xs, 0 < x) :
    (xs : Multiset Nat) = (xs.filter (fun x => decide (1 < x)) : Multiset Nat) +
      Multiset.replicate (xs.count 1) 1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have ht := ih (fun y hy => hp y (by simp [hy]))
    have hx := hp x (by simp)
    by_cases he : x = 1
    · subst x
      simp [← Multiset.cons_coe, ht, Multiset.replicate_succ]
    · have hs : 1 < x := by omega
      simp [hs, he, ← Multiset.cons_coe, ht]

end Hex.Perm.Cycle

namespace Hex.Perm

/-- The complete executable cycle type is Mathlib's nontrivial cycle type
with one entry for each fixed point. -/
theorem cycleType_eq_mathlib (p : Perm n) :
    (p.cycleType.toList : Multiset Nat) = Equiv.Perm.cycleType p.toEquiv +
      Multiset.replicate (n - (Equiv.Perm.support p.toEquiv).card) 1 := by
  have hsplit := Cycle.split_ones (p.allCycles.toList.map Array.size) (by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hk
    exact (p.allCycles_valid c (by simpa using hc)).nonempty)
  have ht : ((p.allCycles.toList.map Array.size).filter (fun k => decide (1 < k)) : Multiset Nat) =
      Equiv.Perm.cycleType p.toEquiv := by
    rw [p.cycleType_factors]
    simp only [cycles, Array.toList_filter, List.filter_map]
    rfl
  rw [ht] at hsplit
  have hs : n = (Equiv.Perm.support p.toEquiv).card +
      (p.allCycles.toList.map Array.size).count 1 := by
    simpa [Equiv.Perm.sum_cycleType, p.allCycles_length] using congrArg Multiset.sum hsplit
  have he : (p.allCycles.toList.map Array.size).count 1 = n - (Equiv.Perm.support p.toEquiv).card :=
    by omega
  calc
    (p.cycleType.toList : Multiset Nat) = (p.allCycles.toList.map Array.size : Multiset Nat) :=
      Quot.sound p.cycleType_perm
    _ = _ := by simpa [he] using hsplit

/-- Conjugation preserves the sorted cycle type, including fixed points. -/
theorem cycleType_conj (p q : Perm n) : ((q.comp p).comp q.inv).cycleType = p.cycleType := by
  have he : (((q.comp p).comp q.inv).cycleType.toList : Multiset Nat) =
      (p.cycleType.toList : Multiset Nat) := by
    rw [cycleType_eq_mathlib, cycleType_eq_mathlib]
    simp only [toEquiv_comp, toEquiv_inv, Equiv.Perm.cycleType_conj, Equiv.Perm.card_support_conj]
  apply Array.toList_inj.mp
  exact (Multiset.coe_eq_coe.mp he).eq_of_pairwise (fun _ _ _ _ => Nat.le_antisymm)
    ((q.comp p).comp q.inv).cycleType_sorted p.cycleType_sorted

end Hex.Perm
