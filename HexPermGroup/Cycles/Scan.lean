/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles.Visit

public section

namespace Hex.Perm.Cycle

/-- The accumulated cycles are valid and disjoint, and account for exactly
the marked points. -/
structure Decomposition (p : Perm n) (seen : Vector Bool n) (cs : Array (Array (Fin n))) : Prop where
  valid : ∀ c ∈ cs, Valid p c
  distinct : (cs.toList.flatMap Array.toList).Nodup
  marked : ∀ x : Fin n, seen[x.val] = true ↔ ∃ c ∈ cs, x ∈ c

theorem Decomposition.empty (p : Perm n) :
    Decomposition p (Vector.replicate n false) #[] := by
  constructor <;> simp

theorem Decomposition.invariant {p : Perm n} {seen : Vector Bool n} {cs : Array (Array (Fin n))}
    (h : Decomposition p seen cs) : Invariant p seen := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [h.marked, h.marked]
  constructor
  · rintro ⟨c, hc, hx⟩
    exact ⟨c, hc, ((h.valid c hc).mem_iff x).mp hx⟩
  · rintro ⟨c, hc, hx⟩
    exact ⟨c, hc, ((h.valid c hc).mem_iff x).mpr hx⟩

theorem Decomposition.push {p : Perm n} {seen next : Vector Bool n}
    {cs : Array (Array (Fin n))} {c : Array (Fin n)} (h : Decomposition p seen cs)
    (hc : Valid p c)
    (hm : ∀ x : Fin n, next[x.val] = true ↔ seen[x.val] = true ∨ x ∈ c)
    (hd : ∀ x ∈ c, seen[x.val] = false) : Decomposition p next (cs.push c) := by
  constructor
  · intro d hd
    rcases Array.mem_push.mp hd with hd | rfl
    · exact h.valid d hd
    · exact hc
  · simp only [Array.toList_push, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply List.nodup_append.mpr
    refine ⟨h.distinct, hc.1, ?_⟩
    intro x hx y hy he
    have hy' : x ∈ c := by simpa [← he] using hy
    obtain ⟨d, hd', hx'⟩ := List.mem_flatMap.mp hx
    have hs := (h.marked x).mpr ⟨d, by simpa using hd', by simpa using hx'⟩
    simp [hd x hy'] at hs
  · intro x
    rw [hm, h.marked]
    simp only [Array.mem_push]
    constructor
    · rintro (⟨d, hd, hx⟩ | hx)
      · exact ⟨d, Or.inl hd, hx⟩
      · exact ⟨c, Or.inr rfl, hx⟩
    · rintro ⟨d, hd | rfl, hx⟩
      · exact Or.inl ⟨d, hd, hx⟩
      · exact Or.inr hx

/-- The scan preserves the partial decomposition. Every point outside the
remaining list is marked, so exhausting that list gives a full partition. -/
theorem scan_complete (p : Perm n) (xs : List (Fin n)) (seen : Vector Bool n)
    (cs : Array (Array (Fin n))) (h : Decomposition p seen cs)
    (outside : ∀ x, x ∉ xs → seen[x.val] = true) :
    let result := p.scanCycles xs seen cs
    Decomposition p result.1 result.2 ∧ ∀ x : Fin n, result.1[x.val] = true := by
  induction xs generalizing seen cs with
  | nil => exact ⟨h, fun x => outside x (by simp)⟩
  | cons x xs ih =>
    simp only [Perm.scanCycles]
    split
    · rename_i hx
      apply ih seen cs h
      intro y hy
      by_cases he : y = x
      · simpa [he] using hx
      · exact outside y (by simp [he, hy])
    · rename_i hx
      have hx' : seen[x.val] = false := by cases hb : seen[x.val] <;> simp_all
      obtain ⟨hc, hm, hd⟩ := visit_complete p seen x h.invariant hx'
      apply ih _ _ (h.push hc hm hd)
      intro y hy
      apply (hm y).mpr
      by_cases he : y = x
      · subst y
        obtain ⟨hf, heq⟩ := visit_first p x seen hx'
        exact Or.inr (Array.mem_iff_getElem.mpr ⟨0, hf, heq⟩)
      · exact Or.inl (outside y (by simp [he, hy]))

end Hex.Perm.Cycle

namespace Hex.Perm

/-- Every emitted cycle follows the permutation, including wrap-around. -/
theorem allCycles_valid (p : Perm n) (c : Array (Fin n)) (hc : c ∈ p.allCycles) :
    Cycle.Valid p c :=
  (Cycle.scan_complete p (List.finRange n) _ _ (Cycle.Decomposition.empty p)
    (by simp)).1.valid c hc

/-- No point occurs twice in the cycle decomposition. -/
theorem allCycles_distinct (p : Perm n) :
    (p.allCycles.toList.flatMap Array.toList).Nodup :=
  (Cycle.scan_complete p (List.finRange n) _ _ (Cycle.Decomposition.empty p)
    (by simp)).1.distinct

/-- Every point occurs in an emitted cycle, including fixed points. -/
theorem mem_allCycles (p : Perm n) (x : Fin n) : ∃ c ∈ p.allCycles, x ∈ c := by
  have h := Cycle.scan_complete p (List.finRange n) _ _ (Cycle.Decomposition.empty p) (by simp)
  exact (h.1.marked x).mp (h.2 x)

/-- Reading the successor in the emitted cycle reconstructs the original action. -/
theorem allCycles_get (p : Perm n) (c : Array (Fin n)) (hc : c ∈ p.allCycles)
    (i : Nat) (hi : i < c.size) :
    p.get c[i] = c[(i + 1) % c.size]'(Nat.mod_lt _ (p.allCycles_valid c hc).nonempty) :=
  (p.allCycles_valid c hc).get i hi

theorem allCycles_length (p : Perm n) : (p.allCycles.toList.map Array.size).sum = n := by
  have hlo := List.nodup_subset_length_le (List.nodup_finRange n)
    (l₂ := p.allCycles.toList.flatMap Array.toList) (fun x _ => by
      obtain ⟨c, hc, hx⟩ := p.mem_allCycles x
      exact List.mem_flatMap.mpr ⟨c, by simpa using hc, by simpa using hx⟩)
  have hhi := List.nodup_subset_length_le p.allCycles_distinct
    (l₂ := List.finRange n) (fun x _ => List.mem_finRange x)
  have he := Nat.le_antisymm hhi hlo
  simpa [List.length_flatMap] using he

end Hex.Perm
