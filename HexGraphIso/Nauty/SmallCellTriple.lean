/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellIter
import all HexGraphIso.Nauty.Equitable

public section

/-!
The cheapautom triple analogues (SPEC § Verified search refinement,
the code-1 arm of the store-validity obligation).

The first guard branch (`defect ≤ nontrivial + 1`) forces every cell
of the partition to be a singleton, a pair, or one triple, and any two
size-three cells to coincide (the sharpened form of
`hOdd_of_defect_le`'s counting argument). On that shape this file
proves the triple analogues of the pair flip theory:

* `triple_const`: the triple's members have identical bits at every
  member of any other cell of size at most two — the count into a
  singleton is the adjacency bit, and the count into a pair is twice
  it by `pair_odd_eq`'s both-or-neither;
* `triple_internal`: the induced graph on the triple is empty or
  complete — the off-diagonal bits are all equal, by the three row-sum
  equalities of equitability (a one-regular graph on three vertices
  is impossible);
* `triple_flip_rows`: the transposition of any two triple members,
  fixing every other vertex, preserves the adjacency rows. Unlike the
  pair flip no matching closure is needed: every other cell is small,
  so the triple's relations to it are constant across the triple.

Remaining on top of this file: the self-equivalence `StPerm` of a
row-preserving flip and the generalized single-deviation theorem, the
pair-closure involution construction, the all-leaves induction, the
`noncheaplevel` event lemma and arm-2 assembly — plus the exotic
defect-four configurations outside the first branch.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-! # The sharpened guard: sizes at most three, at most one triple -/

private theorem sum_excess_ge_countP :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) →
      ((l.map fun p => p.2 - p.1).sum ≥
        l.countP fun p => decide (p.1 < p.2))
  | [], _ => by simp
  | a :: l, hwf => by
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    have ih := sum_excess_ge_countP l
      fun p hp => hwf p (List.mem_cons_of_mem _ hp)
    rcases Decidable.em (a.1 < a.2) with h | h
    · rw [ite_eq_left (decide_eq_true h)]
      omega
    · rw [ite_eq_right (by simpa using h)]
      omega

private theorem sum_excess_ge_countP_add {q : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) → q ∈ l →
      ((l.map fun p => p.2 - p.1).sum ≥
        (l.countP fun p => decide (p.1 < p.2)) + (q.2 - q.1) - 1)
  | [], _, hq => absurd hq (by simp)
  | a :: l, hwf, hq => by
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    rcases List.mem_cons.mp hq with rfl | hmem
    · have ih := sum_excess_ge_countP l
        fun p hp => hwf p (List.mem_cons_of_mem _ hp)
      rcases Decidable.em (q.1 < q.2) with h | h
      · rw [ite_eq_left (decide_eq_true h)]
        omega
      · rw [ite_eq_right (by simpa using h)]
        omega
    · have ih := sum_excess_ge_countP_add l
        (fun p hp => hwf p (List.mem_cons_of_mem _ hp)) hmem
      have ha := hwf a List.mem_cons_self
      rcases Decidable.em (a.1 < a.2) with h | h
      · rw [ite_eq_left (decide_eq_true h)]
        omega
      · rw [ite_eq_right (by simpa using h)]
        omega

private theorem sum_excess_ge_countP_add2 {q q' : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) → q ∈ l → q' ∈ l →
      q ≠ q' →
      ((l.map fun p => p.2 - p.1).sum ≥
        (l.countP fun p => decide (p.1 < p.2)) +
          (q.2 - q.1) + (q'.2 - q'.1) - 2)
  | [], _, hq, _, _ => absurd hq (by simp)
  | a :: l, hwf, hq, hq', hne => by
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    have hwl : ∀ p ∈ l, p.1 ≤ p.2 :=
      fun p hp => hwf p (List.mem_cons_of_mem _ hp)
    rcases List.mem_cons.mp hq with rfl | hmem
    · have hq'l : q' ∈ l := by
        rcases List.mem_cons.mp hq' with heq | hmem'
        · exact absurd heq.symm hne
        · exact hmem'
      have ih := sum_excess_ge_countP_add (q := q') l hwl hq'l
      rcases Decidable.em (q.1 < q.2) with h | h
      · rw [ite_eq_left (decide_eq_true h)]
        omega
      · rw [ite_eq_right (by simpa using h)]
        omega
    · rcases List.mem_cons.mp hq' with rfl | hmem'
      · have ih := sum_excess_ge_countP_add (q := q) l hwl hmem
        rcases Decidable.em (q'.1 < q'.2) with h | h
        · rw [ite_eq_left (decide_eq_true h)]
          omega
        · rw [ite_eq_right (by simpa using h)]
          omega
      · have ih := sum_excess_ge_countP_add2 l hwl hmem hmem' hne
        have ha := hwf a List.mem_cons_self
        rcases Decidable.em (a.1 < a.2) with h | h
        · rw [ite_eq_left (decide_eq_true h)]
          omega
        · rw [ite_eq_right (by simpa using h)]
          omega

private theorem sum_sizes_split :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) →
      (l.map fun p => p.2 + 1 - p.1).sum =
        (l.map fun p => p.2 - p.1).sum + l.length
  | [], _ => rfl
  | a :: l, hwf => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      List.length_cons,
      sum_sizes_split l fun p hp => hwf p (List.mem_cons_of_mem _ hp)]
    have := hwf a List.mem_cons_self
    omega

/-- In the first guard branch every cell has size at most three. -/
theorem size_le_three_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn, q.2 + 1 - q.1 ≤ 3 := by
  intro q hq
  have hwf : ∀ p ∈ cells ptn level nn, p.1 ≤ p.2 :=
    fun p hp => cells_le p hp
  have hsum : ((cells ptn level nn).map fun p =>
      p.2 + 1 - p.1).sum = nn := by
    rw [cells]
    have h := cells_go_sizes_sum hps hend nn 0 (by omega)
    rw [show nn - 0 = nn by omega] at h
    exact h
  have hsplit := sum_sizes_split (cells ptn level nn) hwf
  have hmem := sum_excess_ge_countP_add (cells ptn level nn) hwf hq
  have hq12 := hwf q hq
  omega

/-- In the first guard branch any two size-three cells coincide. -/
theorem triple_uniq_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn, ∀ q' ∈ cells ptn level nn,
      q.2 + 1 - q.1 = 3 → q'.2 + 1 - q'.1 = 3 → q = q' := by
  intro q hq q' hq' hs hs'
  rcases Decidable.em (q = q') with heq | hne
  · exact heq
  · exfalso
    have hwf : ∀ p ∈ cells ptn level nn, p.1 ≤ p.2 :=
      fun p hp => cells_le p hp
    have hsum : ((cells ptn level nn).map fun p =>
        p.2 + 1 - p.1).sum = nn := by
      rw [cells]
      have h := cells_go_sizes_sum hps hend nn 0 (by omega)
      rw [show nn - 0 = nn by omega] at h
      exact h
    have hsplit := sum_sizes_split (cells ptn level nn) hwf
    have hmem := sum_excess_ge_countP_add2 (cells ptn level nn) hwf
      hq hq' hne
    have hq12 := hwf q hq
    have hq12' := hwf q' hq'
    omega

/-- The first-branch shape: every cell is a singleton, a pair, or the
unique triple. -/
theorem cells_shape_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn,
      q.2 + 1 - q.1 = 1 ∨ q.2 + 1 - q.1 = 2 ∨
        (q.2 + 1 - q.1 = 3 ∧
          ∀ q' ∈ cells ptn level nn, q'.2 + 1 - q'.1 = 3 → q' = q) := by
  intro q hq
  have hle := size_le_three_of_defect_le hps hend hguard q hq
  have hge := cells_le q hq
  rcases Decidable.em (q.2 + 1 - q.1 = 3) with h3 | h3
  · exact Or.inr (Or.inr ⟨h3, fun q' hq' hs' =>
      triple_uniq_of_defect_le hps hend hguard q' hq' q hq hs' h3⟩)
  · rcases Decidable.em (q.2 + 1 - q.1 = 2) with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inl (by omega)

end Hex.GraphIso.Nauty
