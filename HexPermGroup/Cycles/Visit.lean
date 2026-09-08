/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexPermGroup.Cycles.Path

public section

namespace Hex.Perm.Cycle

/-- The old marks are a union of complete cycles. -/
@[expose] def Invariant (p : Perm n) (seen : Vector Bool n) : Prop :=
  ∀ x : Fin n, seen[(p.get x).val] = seen[x.val]

/-- A visit appends fresh points and marks exactly those appended points. -/
structure State (p : Perm n) (old seen : Vector Bool n) (c : Array (Fin n)) (next : Fin n) : Prop where
  follows : Follows p c next
  distinct : c.toList.Nodup
  marked : ∀ x : Fin n, seen[x.val] = true ↔ old[x.val] = true ∨ x ∈ c
  disjoint : ∀ x ∈ c, old[x.val] = false
  fresh : old[next.val] = false

theorem State.initial (p : Perm n) (seen : Vector Bool n) (x : Fin n) (hx : seen[x.val] = false) :
    State p seen seen #[] x :=
  ⟨follows_empty p x, by simp, by intro y; simp, by simp, hx⟩

theorem State.mem_of_seen {p : Perm n} {old seen : Vector Bool n} {c : Array (Fin n)} {x : Fin n}
    (s : State p old seen c x) (hx : seen[x.val] = true) : x ∈ c := by
  rcases (s.marked x).mp hx with h | h
  · simp [s.fresh] at h
  · exact h

theorem State.not_mem {p : Perm n} {old seen : Vector Bool n} {c : Array (Fin n)} {x : Fin n}
    (s : State p old seen c x) (hx : seen[x.val] ≠ true) : x ∉ c :=
  fun hm => hx ((s.marked x).mpr (Or.inr hm))

theorem State.push {p : Perm n} {old seen : Vector Bool n} {c : Array (Fin n)} {x : Fin n}
    (s : State p old seen c x) (ho : Invariant p old) (hx : seen[x.val] ≠ true) :
    State p old (seen.set x.val true) (c.push x) (p.get x) := by
  have hm := s.not_mem hx
  refine ⟨s.follows.push, ?_, ?_, ?_, ?_⟩
  · simp only [Array.toList_push]
    apply List.nodup_append.mpr
    refine ⟨s.distinct, by simp, ?_⟩
    intro a ha b hb he
    have hb' : b = x := by simpa using hb
    have ha' : a ∈ c := by simpa using ha
    exact hm ((he.trans hb') ▸ ha')
  · intro y
    by_cases he : y = x
    · subst y
      simp [Array.mem_push]
    · have hv : y.val ≠ x.val := fun h => he (Fin.ext h)
      simpa [Vector.getElem_set, hv, Ne.symm hv, Array.mem_push, he] using s.marked y
  · intro y hy
    rcases Array.mem_push.mp hy with hy | rfl
    · exact s.disjoint y hy
    · exact s.fresh
  · rw [ho x]
    exact s.fresh

/-- At zero fuel there are already at least `n` distinct entries. A further
fresh point would give `n+1` distinct elements of `Fin n`. -/
theorem State.seen_of_full {p : Perm n} {old seen : Vector Bool n} {c : Array (Fin n)} {x : Fin n}
    (s : State p old seen c x) (ho : Invariant p old) (hc : n ≤ c.size) : seen[x.val] = true := by
  by_cases hx : seen[x.val] = true
  · exact hx
  · have hd := nodup_size (s.push ho hx).distinct
    simp only [Array.size_push] at hd
    omega

/-- The actual visit loop returns a complete cycle, with exact new marks and
no overlap with the cycles that were already marked. -/
theorem visit_valid (p : Perm n) (old seen : Vector Bool n) (c : Array (Fin n)) (x : Fin n)
    (fuel : Nat) (s : State p old seen c x) (ho : Invariant p old) (bound : n ≤ fuel + c.size) :
    let result := p.visit fuel x seen c
    Valid p result.2 ∧
      (∀ y : Fin n, result.1[y.val] = true ↔ old[y.val] = true ∨ y ∈ result.2) ∧
      (∀ y ∈ result.2, old[y.val] = false) := by
  induction fuel generalizing seen c x with
  | zero =>
    have hx := s.mem_of_seen (s.seen_of_full ho (by simpa using bound))
    exact ⟨s.follows.valid s.distinct hx, s.marked, s.disjoint⟩
  | succ fuel ih =>
    simp only [Perm.visit]
    split
    · rename_i hx
      exact ⟨s.follows.valid s.distinct (s.mem_of_seen hx), s.marked, s.disjoint⟩
    · rename_i hx
      apply ih _ _ _ (s.push ho hx)
      simp only [Array.size_push]
      omega

theorem marked_invariant {p : Perm n} {old seen : Vector Bool n} {c : Array (Fin n)}
    (ho : Invariant p old) (hc : Valid p c)
    (hm : ∀ x : Fin n, seen[x.val] = true ↔ old[x.val] = true ∨ x ∈ c) : Invariant p seen := by
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [hm, hm, ho x, hc.mem_iff x]

/-- Visiting preserves the entries already appended, in their original order. -/
theorem visit_append (p : Perm n) (fuel : Nat) (x : Fin n) (seen : Vector Bool n)
    (c : Array (Fin n)) : ∃ tail, (p.visit fuel x seen c).2 = c ++ tail := by
  induction fuel generalizing x seen c with
  | zero => exact ⟨#[], by simp [Perm.visit]⟩
  | succ fuel ih =>
    simp only [Perm.visit]
    split
    · exact ⟨#[], by simp⟩
    · obtain ⟨tail, ht⟩ := ih (p.get x) (seen.set x.val true) (c.push x)
      exact ⟨#[x] ++ tail, by simpa only [Array.push_eq_append, Array.append_assoc] using ht⟩

theorem visit_first (p : Perm n) (x : Fin n) (seen : Vector Bool n)
    (hx : seen[x.val] = false) :
    ∃ hc : 0 < (p.visit n x seen #[]).2.size, (p.visit n x seen #[]).2[0] = x := by
  cases n with
  | zero => exact Fin.elim0 x
  | succ n =>
    obtain ⟨tail, ht⟩ := visit_append p n (p.get x) (seen.set x.val true) #[x]
    have hout : (p.visit (n + 1) x seen #[]).2 = #[x] ++ tail := by
      simpa only [Perm.visit, hx, Bool.false_eq_true, ↓reduceIte, Array.push_eq_append,
        Array.empty_append] using ht
    rw [hout]
    exact ⟨by simp; omega, by simp⟩

/-- Starting at an unmarked point produces its whole cycle and marks exactly
that cycle in addition to the old marks. -/
theorem visit_complete (p : Perm n) (seen : Vector Bool n) (x : Fin n)
    (ho : Invariant p seen) (hx : seen[x.val] = false) :
    let result := p.visit n x seen #[]
    Valid p result.2 ∧
      (∀ y : Fin n, result.1[y.val] = true ↔ seen[y.val] = true ∨ y ∈ result.2) ∧
      (∀ y ∈ result.2, seen[y.val] = false) :=
  visit_valid p seen seen #[] x n (State.initial p seen x hx) ho (by simp)

end Hex.Perm.Cycle
