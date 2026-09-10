/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles.Canonical
public import HexPermGroupMathlib.Perm
public import Mathlib.GroupTheory.Perm.Cycle.Concrete

public section

namespace Hex.Perm.Cycle

theorem Valid.formPerm_get {p : Perm n} {c : Array (Fin n)} (h : Valid p c)
    (x : Fin n) (hx : x ∈ c) : c.toList.formPerm x = p.get x := by
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  have he := List.formPerm_apply_getElem c.toList h.1 i (by simpa using hi)
  rw [h.get i hi]
  simpa using he

/-- A product of disjoint recorded cycles acts as the permutation on their
union and fixes every point outside that union. -/
theorem prod_apply (p : Perm n) (cs : List (Array (Fin n)))
    (hv : ∀ c ∈ cs, Valid p c) (hd : (cs.flatMap Array.toList).Nodup) (x : Fin n) :
    (cs.map (fun c => c.toList.formPerm)).prod x =
      if x ∈ cs.flatMap Array.toList then p.get x else x := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have hn := List.nodup_append.mp (show (c.toList ++ cs.flatMap Array.toList).Nodup from hd)
    have hc := hv c (by simp)
    have ht := ih (fun d hd => hv d (by simp [hd])) hn.2.1
    simp only [List.map_cons, List.prod_cons, Equiv.Perm.mul_apply]
    rw [ht]
    by_cases hx : x ∈ cs.flatMap Array.toList
    · have hall : x ∈ (c :: cs).flatMap Array.toList := by simp [hx]
      rw [ite_eq_left hx, ite_eq_left hall]
      apply List.formPerm_apply_of_notMem
      intro hp
      have hx' : x ∈ c.toList := by
        have := (hc.mem_iff x).mp (by simpa using hp)
        simpa using this
      exact hn.2.2 x hx' x hx rfl
    · rw [ite_eq_right hx]
      by_cases hx' : x ∈ c
      · have hall : x ∈ (c :: cs).flatMap Array.toList := by simp [hx']
        rw [ite_eq_left hall]
        exact hc.formPerm_get x hx'
      · have hall : x ∉ (c :: cs).flatMap Array.toList := by simpa using And.intro hx' hx
        rw [ite_eq_right hall]
        exact List.formPerm_apply_of_notMem (by simpa using hx')

end Hex.Perm.Cycle

namespace Hex.Perm

/-- Multiplying the recorded cycles reconstructs the Mathlib permutation. -/
theorem allCycles_prod (p : Perm n) :
    (p.allCycles.toList.map (fun c => c.toList.formPerm)).prod = p.toEquiv := by
  apply Equiv.ext
  intro x
  rw [Cycle.prod_apply p _ (fun c hc => p.allCycles_valid c (by simpa using hc)) p.allCycles_distinct]
  obtain ⟨c, hc, hx⟩ := p.mem_allCycles x
  have hm : x ∈ p.allCycles.toList.flatMap Array.toList :=
    List.mem_flatMap.mpr ⟨c, by simpa using hc, by simpa using hx⟩
  simp [hm]

theorem cycles_prod (p : Perm n) :
    (p.cycles.toList.map (fun c => c.toList.formPerm)).prod = p.toEquiv := by
  have hv : ∀ c ∈ p.allCycles.toList, Cycle.Valid p c :=
    fun c hc => p.allCycles_valid c (by simpa using hc)
  rw [← p.allCycles_prod]
  simp only [cycles, Array.toList_filter]
  generalize p.allCycles.toList = cs at *
  induction cs with
  | nil => simp
  | cons c cs ih =>
    have ht := ih (fun d hd => hv d (by simp [hd]))
    by_cases hs : 1 < c.size
    · simp [hs, ht]
    · have hpos := (hv c (by simp)).nonempty
      have hsize : c.toList.length = 1 := by simp only [Array.length_toList]; omega
      obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hsize
      have he : c.toList.formPerm = 1 := by simp [hx]
      simp [hs, ht, he]

theorem cycles_disjoint (p : Perm n) :
    (p.cycles.toList.map (fun c => c.toList.formPerm)).Pairwise Equiv.Perm.Disjoint := by
  apply List.pairwise_map.mpr
  have hp := (List.pairwise_flatMap.mp p.allCycles_distinct).2
  have hf := hp.filter (fun c => decide (1 < c.size))
  rw [cycles, Array.toList_filter]
  apply hf.imp
  intro c d hcd
  rw [Equiv.Perm.disjoint_iff_eq_or_eq]
  intro x
  by_cases hx : x ∈ c.toList
  · right
    apply List.formPerm_apply_of_notMem
    intro hd
    exact hcd x hx x hd rfl
  · exact Or.inl (List.formPerm_apply_of_notMem hx)

theorem cycle_support (p : Perm n) (c : Array (Fin n)) (hc : c ∈ p.cycles) :
    c.toList.formPerm.support.card = c.size := by
  have hmem : c ∈ p.allCycles ∧ 1 < c.size := by simpa [cycles] using hc
  have hv := p.allCycles_valid c hmem.1
  rw [List.support_formPerm_of_nodup c.toList hv.1, List.toFinset_card_of_nodup hv.1]
  · simp
  · intro x hx
    have := congrArg List.length hx
    simp only [Array.length_toList, List.length_singleton] at this
    omega

/-- Mathlib omits fixed points from its cycle type. Its entries are precisely
the lengths of the nontrivial cycles returned by the executable traversal. -/
theorem cycleType_factors (p : Perm n) :
    Equiv.Perm.cycleType p.toEquiv = (p.cycles.toList.map Array.size : Multiset Nat) := by
  rw [Equiv.Perm.cycleType_eq _ p.cycles_prod ?_ p.cycles_disjoint]
  · apply congrArg (fun l : List Nat => (l : Multiset Nat))
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    exact p.cycle_support c (by simpa using hc)
  · intro q hq
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hq
    have hmem : c ∈ p.allCycles ∧ 1 < c.size := by simpa [cycles] using hc
    apply List.isCycle_formPerm (p.allCycles_valid c hmem.1).1
    simp only [Array.length_toList]
    omega

end Hex.Perm
