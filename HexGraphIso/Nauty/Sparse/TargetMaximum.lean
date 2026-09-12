/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetBest

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- The first occurrence of a maximal score: preceding scores are strictly
smaller, and following scores are no larger. -/
@[expose] def FirstMax (score : Nat → Nat) (xs : List Nat) (winner : Nat) : Prop :=
  ∃ before after, xs = before ++ winner :: after ∧
    (∀ v ∈ before, score v < score winner) ∧ ∀ v ∈ after, score v ≤ score winner

namespace FirstMax

theorem mem {score : Nat → Nat} {xs : List Nat} {winner : Nat} (h : FirstMax score xs winner) :
    winner ∈ xs := by
  obtain ⟨before, after, rfl, _, _⟩ := h
  simp

theorem bound {score : Nat → Nat} {xs : List Nat} {winner v : Nat}
    (h : FirstMax score xs winner) (hv : v ∈ xs) : score v ≤ score winner := by
  obtain ⟨before, after, rfl, hb, ha⟩ := h
  rcases List.mem_append.mp hv with hv | hv
  · exact Nat.le_of_lt (hb v hv)
  · rcases List.mem_cons.mp hv with rfl | hv
    · exact Nat.le_refl _
    · exact ha v hv

theorem cons_lt {score : Nat → Nat} {xs : List Nat} {winner v : Nat}
    (h : FirstMax score xs winner) (hv : score v < score winner) :
    FirstMax score (v :: xs) winner := by
  obtain ⟨before, after, rfl, hb, ha⟩ := h
  refine ⟨v :: before, after, rfl, ?_, ha⟩
  intro k hk
  rcases List.mem_cons.mp hk with rfl | hk
  · exact hv
  · exact hb k hk

/-- A candidate no better than the current representative can be skipped
without changing the earliest maximal candidate. -/
theorem insert {score : Nat → Nat} {xs : List Nat} {winner b v : Nat}
    (h : FirstMax score (b :: xs) winner) (hv : score v ≤ score b) :
    FirstMax score (b :: v :: xs) winner := by
  obtain ⟨before, after, he, hb, ha⟩ := h
  cases before with
  | nil =>
    simp only [List.nil_append, List.cons.injEq] at he
    obtain ⟨hw, ht⟩ := he
    subst winner
    subst after
    refine ⟨[], v :: xs, rfl, by simp, ?_⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hv
    · exact ha k hk
  | cons c before =>
    simp only [List.cons_append, List.cons.injEq] at he
    obtain ⟨hc, ht⟩ := he
    subst c
    subst xs
    refine ⟨b :: v :: before, after, rfl, ?_, ha⟩
    intro k hk
    rcases List.mem_cons.mp hk with rfl | hk
    · exact hb k (by simp)
    · rcases List.mem_cons.mp hk with rfl | hk
      · exact Nat.lt_of_le_of_lt hv (hb b (by simp))
      · exact hb k (by simp [hk])

end FirstMax

private theorem fold_max (score : Nat → Nat) (xs : List Nat) (b : Nat) :
    FirstMax score (b :: xs) (xs.foldl (select score) (b, score b)).1 := by
  induction xs generalizing b with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons v xs ih =>
    rw [List.foldl_cons]
    unfold select
    split
    · next hv =>
      have h := ih v
      exact h.cons_lt (Nat.lt_of_lt_of_le hv (h.bound (by simp)))
    · next hv => exact (ih b).insert (by omega)

/-- The strict comparison in the executed selection fold chooses precisely
the first cell with maximum score. -/
theorem best_max (keys : List Nat) (score : Nat → Nat) (empty : Nat) (hne : keys ≠ []) :
    FirstMax score keys (best keys score empty) := by
  cases keys with
  | nil => exact False.elim (hne rfl)
  | cons b xs =>
    have hstep : select score (b, 0) b = (b, score b) := by
      unfold select
      split
      · rfl
      · next h =>
        have hz : score b = 0 := by omega
        simp [hz]
    simpa only [best, List.isEmpty_cons, Bool.false_eq_true, ite_false, List.headD_cons,
      List.foldl_cons, hstep] using fold_max score xs b

end Hex.GraphIso.Nauty.Sparse.Target
