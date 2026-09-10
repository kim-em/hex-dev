/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import Std

public section

/-!
Sums over `List.range`, `countP` uniqueness, and the excess and size
sums of a list of cell windows: the arithmetic the guard, flip and
pigeonhole arguments of the small-cell theory share.
-/

namespace Hex.GraphIso.Nauty

/-- Peel the last summand off a sum over `List.range`. -/
theorem sum_range_succ (f : Nat → Nat) (m : Nat) :
    ((List.range (m + 1)).map f).sum =
      ((List.range m).map f).sum + f m := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

/-- A sum over `List.range 2` in closed form. -/
theorem sum_range_two (f : Nat → Nat) :
    ((List.range 2).map f).sum = f 0 + f 1 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, sum_range_succ,
    show (1 : Nat) = 0 + 1 from rfl, sum_range_succ]
  simp

/-- A sum over `List.range 3` in closed form. -/
theorem sum_range_three (f : Nat → Nat) :
    ((List.range 3).map f).sum = f 0 + f 1 + f 2 := by
  rw [show (3 : Nat) = 2 + 1 from rfl, sum_range_succ, sum_range_two]

/-- A constant sum over `List.range`. -/
theorem sum_range_const (c : Nat) :
    ∀ m, ((List.range m).map fun _ => c).sum = m * c
  | 0 => by simp
  | m + 1 => by
    rw [sum_range_succ, sum_range_const c m, Nat.succ_mul]

/-- A sum of values at most one over `List.range m` is at
most `m`. -/
theorem sum_range_le (f : Nat → Nat) :
    ∀ m, (∀ o, o < m → f o ≤ 1) → ((List.range m).map f).sum ≤ m
  | 0, _ => by simp
  | m + 1, hf => by
    rw [sum_range_succ]
    have h1 := sum_range_le f m fun o ho => hf o (by omega)
    have h2 := hf m (by omega)
    omega

/-- A vanishing sum over `List.range` has every summand
zero. -/
theorem sum_range_eq_zero {f : Nat → Nat} :
    ∀ m, ((List.range m).map f).sum = 0 → ∀ o, o < m → f o = 0
  | m + 1, hs, o, ho => by
    rw [sum_range_succ] at hs
    rcases Decidable.em (o = m) with rfl | hne
    · omega
    · exact sum_range_eq_zero m (by omega) o (by omega)

/-- A sum of values at most one over `List.range m` that
reaches `m` has every summand one. -/
theorem sum_range_eq_len {f : Nat → Nat} :
    ∀ m, (∀ o, o < m → f o ≤ 1) → ((List.range m).map f).sum = m →
      ∀ o, o < m → f o = 1
  | m + 1, hf, hs, o, ho => by
    rw [sum_range_succ] at hs
    have h1 := sum_range_le f m fun o ho => hf o (by omega)
    have h2 := hf m (by omega)
    rcases Decidable.em (o = m) with rfl | hne
    · omega
    · exact sum_range_eq_len m (fun o ho => hf o (by omega)) (by omega)
        o (by omega)

/-- A predicate satisfied nowhere in a list counts
zero. -/
theorem countP_zero_of_none {p : Nat → Bool} :
    ∀ (l : List Nat), (∀ i ∈ l, ¬ p i = true) → l.countP p = 0
  | [], _ => rfl
  | i :: l, h => by
    rw [List.countP_cons,
      ite_eq_right (h i List.mem_cons_self),
      countP_zero_of_none l fun i' hi' =>
        h i' (List.mem_cons_of_mem _ hi')]

/-- A predicate satisfied at no two distinct positions
counts at most one over `List.range`. -/
theorem countP_range_le_one {p : Nat → Bool} {n : Nat}
    (h : ∀ i j, i < n → j < n → p i = true → p j = true → i = j) :
    (List.range n).countP p ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons,
      List.countP_nil]
    rcases hp : p m with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      have := ih fun i j hi hj hpi hpj =>
        h i j (by omega) (by omega) hpi hpj
      omega
    · have hz : (List.range m).countP p = 0 := by
        rw [List.countP_eq_zero]
        intro a ha hpa
        have ham := List.mem_range.mp ha
        exact absurd (h a m (by omega) (by omega) hpa hp) (by omega)
      simp [hz]

/-- A predicate satisfied at exactly one position of
`List.range n` counts one. -/
theorem countP_range_one {p : Nat → Bool} {n i₀ : Nat}
    (hi₀ : i₀ < n) (hp : p i₀ = true)
    (huniq : ∀ j, j < n → p j = true → j = i₀) :
    (List.range n).countP p = 1 := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.countP_append]
    rcases Decidable.em (i₀ = m) with heq | hne
    · have h0 : (List.range m).countP p = 0 :=
        List.countP_eq_zero.mpr fun a ha hpa => by
          have han := List.mem_range.mp ha
          have := huniq a (by omega) hpa
          omega
      have hpm : p m = true := heq ▸ hp
      rw [h0, List.countP_cons, List.countP_nil, hpm]
      simp
    · have him : i₀ < m := by omega
      have h1 : (List.range m).countP p = 1 :=
        ih him (fun j hj hpj => huniq j (by omega) hpj)
      have h0 : ([m].countP p) = 0 :=
        List.countP_eq_zero.mpr fun a ha hpa => by
          have ham : a = m := by simpa using ha
          have := huniq a (by omega) hpa
          omega
      omega

/-- A predicate counting at most one is satisfied by at
most one member. -/
theorem countP_le_one_unique {p : Nat → Bool} :
    ∀ (l : List Nat), l.countP p ≤ 1 →
      ∀ w ∈ l, p w = true → ∀ w' ∈ l, p w' = true → w = w'
  | a :: t, h, w, hw, hpw, w', hw', hpw' => by
    rw [List.countP_cons] at h
    rcases Decidable.em (p a = true) with hpa | hpa
    · rw [ite_eq_left hpa] at h
      have ht0 : t.countP p = 0 := by omega
      have hnt : ∀ x ∈ t, ¬ p x = true := by
        intro x hx hpx
        have : 0 < t.countP p := by
          have := countP_zero_none t ht0 x hx
          exact absurd hpx this
        omega
      have hwa : w = a := by
        rcases List.mem_cons.mp hw with rfl | hmem
        · rfl
        · exact absurd hpw (hnt w hmem)
      have hwa' : w' = a := by
        rcases List.mem_cons.mp hw' with rfl | hmem
        · rfl
        · exact absurd hpw' (hnt w' hmem)
      rw [hwa, hwa']
    · rw [ite_eq_right hpa] at h
      have hwt : w ∈ t := by
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact absurd hpw hpa
        · exact hmem
      have hwt' : w' ∈ t := by
        rcases List.mem_cons.mp hw' with rfl | hmem
        · exact absurd hpw' hpa
        · exact hmem
      exact countP_le_one_unique t h w hwt hpw w' hwt' hpw'
where
  countP_zero_none : ∀ (l : List Nat), l.countP p = 0 →
      ∀ x ∈ l, ¬ p x = true
    | a :: t, h0, x, hx => by
      rw [List.countP_cons] at h0
      rcases Decidable.em (p a = true) with hpa | hpa
      · rw [ite_eq_left hpa] at h0
        omega
      · rcases List.mem_cons.mp hx with rfl | hmem
        · exact fun hpx => hpa hpx
        · rw [ite_eq_right hpa] at h0
          exact countP_zero_none t h0 x hmem

/-- The window sizes of a list of intervals split into the
excesses plus the number of intervals. -/
theorem sum_sizes_split :
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

/-- The excesses of a list of intervals sum to at least
the number of nontrivial ones. -/
theorem sum_excess_ge_countP :
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

/-- The excess sum also carries one distinguished
interval's excess in full. -/
theorem sum_excess_ge_countP_add {q : Nat × Nat} :
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

/-- The excess sum also carries two distinct
distinguished intervals' excesses in full. -/
theorem sum_excess_ge_countP_add2 {q q' : Nat × Nat} :
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

/-- The excesses of a list of intervals sum to at least one
member's excess. -/
theorem exc_ge_one {q : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), q ∈ l →
      (l.map fun p => p.2 - p.1).sum ≥ q.2 - q.1
  | [], hq => absurd hq (by simp)
  | a :: l, hq => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hmem
    · omega
    · have := exc_ge_one l hmem
      omega

/-- The excesses of a list of intervals sum to at least two
distinct members' excesses. -/
theorem exc_ge_two {q q' : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), q ∈ l → q' ∈ l → q ≠ q' →
      (l.map fun p => p.2 - p.1).sum ≥ (q.2 - q.1) + (q'.2 - q'.1)
  | [], hq, _, _ => absurd hq (by simp)
  | a :: l, hq, hq', hne => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hmem
    · have hq'l : q' ∈ l := by
        rcases List.mem_cons.mp hq' with rfl | h
        · exact absurd rfl hne
        · exact h
      have := exc_ge_one l hq'l
      omega
    · rcases List.mem_cons.mp hq' with rfl | hmem'
      · have := exc_ge_one l hmem
        omega
      · have := exc_ge_two l hmem hmem' hne
        omega

/-- The excesses of a list of intervals sum to at least three
distinct members' excesses. -/
theorem exc_ge_three {q q' q'' : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), q ∈ l → q' ∈ l → q'' ∈ l →
      q ≠ q' → q ≠ q'' → q' ≠ q'' →
      (l.map fun p => p.2 - p.1).sum ≥
        (q.2 - q.1) + (q'.2 - q'.1) + (q''.2 - q''.1)
  | [], hq, _, _, _, _, _ => absurd hq (by simp)
  | a :: l, hq, hq', hq'', hne, hne', hne'' => by
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp hq with rfl | hmem
    · have h1 : q' ∈ l := by
        rcases List.mem_cons.mp hq' with rfl | h
        · exact absurd rfl hne
        · exact h
      have h2 : q'' ∈ l := by
        rcases List.mem_cons.mp hq'' with rfl | h
        · exact absurd rfl hne'
        · exact h
      have := exc_ge_two l h1 h2 hne''
      omega
    · rcases List.mem_cons.mp hq' with rfl | hmem'
      · have h2 : q'' ∈ l := by
          rcases List.mem_cons.mp hq'' with rfl | h
          · exact absurd rfl hne''
          · exact h
        have := exc_ge_two l hmem h2 hne'
        omega
      · rcases List.mem_cons.mp hq'' with rfl | hmem''
        · have := exc_ge_two l hmem hmem' hne
          omega
        · have := exc_ge_three l hmem hmem' hmem'' hne hne' hne''
          omega

end Hex.GraphIso.Nauty
