/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles.Scan

public section

namespace Hex.Perm.Cycle

/-- The first entry is the least point in the cycle. -/
@[expose] def Least (c : Array (Fin n)) : Prop :=
  ∀ hc : 0 < c.size, ∀ x ∈ c, c[0] ≤ x

/-- Cycles are ordered by their first entries. -/
@[expose] def Precedes (c d : Array (Fin n)) : Prop :=
  ∀ hc : 0 < c.size, ∀ hd : 0 < d.size, c[0] < d[0]

theorem scan_canonical (p : Perm n) (xs : List (Fin n)) (seen : Vector Bool n)
    (cs : Array (Array (Fin n))) (h : Decomposition p seen cs)
    (outside : ∀ x, x ∉ xs → seen[x.val] = true)
    (sorted : xs.Pairwise (· < ·))
    (least : ∀ c ∈ cs, Least c) (ordered : cs.toList.Pairwise Precedes)
    (before : ∀ c ∈ cs, ∀ x ∈ xs, ∀ hc : 0 < c.size, c[0] < x) :
    let result := (p.scanCycles xs seen cs).2
    (∀ c ∈ result, Least c) ∧ result.toList.Pairwise Precedes := by
  induction xs generalizing seen cs with
  | nil => exact ⟨least, ordered⟩
  | cons x xs ih =>
    obtain ⟨hxs, hs⟩ := List.pairwise_cons.mp sorted
    simp only [Perm.scanCycles]
    split
    · rename_i hx
      refine ih seen cs h ?_ hs least ordered ?_
      · intro y hy
        by_cases he : y = x
        · simpa [he] using hx
        · exact outside y (by simp [he, hy])
      · intro c hc y hy
        exact before c hc y (by simp [hy])
    · rename_i hx
      have hx' : seen[x.val] = false := by cases hb : seen[x.val] <;> simp_all
      obtain ⟨hc, hm, hd⟩ := visit_complete p seen x h.invariant hx'
      obtain ⟨hf, heq⟩ := visit_first p x seen hx'
      have hl : Least (p.visit n x seen #[]).2 := by
        intro hzero y hy
        rw [heq]
        have hn : ¬ y < x := by
          intro hlt
          have hnmem : y ∉ x :: xs := by
            intro hymem
            rcases List.mem_cons.mp hymem with he | hyxs
            · subst y
              exact (Nat.lt_irrefl _) hlt
            · have hxy := hxs y hyxs
              exact (Nat.lt_irrefl _) (Nat.lt_trans hlt hxy)
          have hyseen := outside y hnmem
          simp [hd y hy] at hyseen
        exact Nat.le_of_not_gt hn
      apply ih _ _ (h.push hc hm hd) ?_ hs ?_ ?_ ?_
      · intro y hy
        apply (hm y).mpr
        by_cases he : y = x
        · subst y
          exact Or.inr (Array.mem_iff_getElem.mpr ⟨0, hf, heq⟩)
        · exact Or.inl (outside y (by simp [he, hy]))
      · intro c hcmem
        rcases Array.mem_push.mp hcmem with hcmem | rfl
        · exact least c hcmem
        · exact hl
      · simp only [Array.toList_push]
        apply List.pairwise_append.mpr
        refine ⟨ordered, by simp, ?_⟩
        intro c hcmem d hdmem
        have he : d = (p.visit n x seen #[]).2 := by simpa using hdmem
        subst d
        intro hc0 hd0
        rw [heq]
        exact before c (by simpa using hcmem) x (by simp) hc0
      · intro c hcmem y hy hc0
        rcases Array.mem_push.mp hcmem with hcmem | rfl
        · exact before c hcmem y (by simp [hy]) hc0
        · rw [heq]
          exact hxs y hy

end Hex.Perm.Cycle

namespace Hex.Perm

theorem allCycles_least (p : Perm n) (c : Array (Fin n)) (hc : c ∈ p.allCycles) :
    Cycle.Least c :=
  (Cycle.scan_canonical p (List.finRange n) _ _ (Cycle.Decomposition.empty p)
    (by simp) (List.pairwise_lt_finRange n) (by simp) (by simp) (by simp)).1 c hc

theorem allCycles_ordered (p : Perm n) : p.allCycles.toList.Pairwise Cycle.Precedes :=
  (Cycle.scan_canonical p (List.finRange n) _ _ (Cycle.Decomposition.empty p)
    (by simp) (List.pairwise_lt_finRange n) (by simp) (by simp) (by simp)).2

theorem cycles_least (p : Perm n) (c : Array (Fin n)) (hc : c ∈ p.cycles) : Cycle.Least c :=
  p.allCycles_least c (Array.mem_of_mem_filter hc)

theorem cycles_ordered (p : Perm n) : p.cycles.toList.Pairwise Cycle.Precedes := by
  simpa only [cycles, Array.toList_filter] using p.allCycles_ordered.filter _

end Hex.Perm
