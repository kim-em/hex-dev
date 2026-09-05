/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison

This file contains code translated from the nauty 2.9.3 sources
(https://users.cecs.anu.edu.au/~bdm/nauty/), copyright Brendan McKay and Adolfo
Piperno, released under the Apache 2.0 license.
-/

module
public import HexGraphIso.Nauty.VSet.Basic

public section

/-!
Cardinality of packed vertex sets: the empty set, disjoint unions,
singletons, comparisons, and the effect of `insert` and `erase`.
-/

namespace Hex.GraphIso.Nauty

namespace VSet

variable {n : Nat}

/-! # Identities of the empty set -/

@[simp] theorem card_empty : (empty : VSet n).card = 0 := by
  rw [card_eq_countBelow, countBelow, List.countP_eq_zero]
  intro v _
  rw [mem_empty]
  exact Bool.false_ne_true

@[simp] theorem inter_empty (s : VSet n) : s.inter empty = empty :=
  ext fun w => by rw [mem_inter, mem_empty, Bool.and_false]

@[simp] theorem empty_inter (s : VSet n) : (empty : VSet n).inter s = empty :=
  ext fun w => by rw [mem_inter, mem_empty, Bool.false_and]

@[simp] theorem union_empty (s : VSet n) : s.union empty = s :=
  ext fun w => by rw [mem_union, mem_empty, Bool.or_false]

@[simp] theorem empty_union (s : VSet n) : (empty : VSet n).union s = s :=
  ext fun w => by rw [mem_union, mem_empty, Bool.false_or]

theorem inter_self (s : VSet n) : s.inter s = s :=
  ext fun w => by rw [mem_inter, Bool.and_self]

/-! # Counts over disjoint unions -/

private theorem countP_or_disjoint {p q : Nat → Bool} :
    ∀ l : List Nat, (∀ i ∈ l, ¬(p i = true ∧ q i = true)) →
      l.countP (fun i => p i || q i) = l.countP p + l.countP q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      countP_or_disjoint l fun i hi => h i (List.mem_cons_of_mem x hi)]
    rcases hp : p x with _ | _ <;> rcases hq : q x with _ | _
    · simp
    · simp; omega
    · simp; omega
    · exact absurd ⟨hp, hq⟩ (h x (List.mem_cons_self ..))

/-- Member counts add over a disjoint union. -/
theorem card_union_disjoint {a b : VSet n} (hd : a.inter b = empty) :
    (a.union b).card = a.card + b.card := by
  rw [card_eq_countBelow, card_eq_countBelow, card_eq_countBelow, countBelow, countBelow,
    countBelow]
  have hf : (a.union b).mem = fun i => a.mem i || b.mem i := funext fun i => mem_union a b i
  rw [hf]
  refine countP_or_disjoint _ fun i _ hpq => ?_
  have := congrArg (fun s => s.mem i) hd
  simp only [mem_inter, mem_empty, hpq.1, hpq.2] at this
  cases this

theorem inter_union_distrib (a b x : VSet n) :
    (a.union b).inter x = (a.inter x).union (b.inter x) :=
  ext fun w => by
    rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
    cases a.mem w <;> cases b.mem w <;> cases x.mem w <;> rfl

/-- Counts into a set add over a disjoint union. -/
theorem cardInter_union_disjoint {a b : VSet n} (hd : a.inter b = empty) (x : VSet n) :
    (a.union b).cardInter x = a.cardInter x + b.cardInter x := by
  rw [cardInter_eq, cardInter_eq, cardInter_eq, inter_union_distrib]
  refine card_union_disjoint (ext fun w => ?_)
  have := congrArg (fun s => s.mem w) hd
  simp only [mem_inter, mem_empty] at this ⊢
  cases ha : a.mem w <;> cases hb : b.mem w <;> simp_all

/-! # Singletons -/

theorem mem_singleton (u v : Nat) :
    ((empty : VSet n).insert u).mem v = (u == v && decide (u < n)) := by
  rw [mem_insert, mem_empty, Bool.false_or]

theorem inter_comm (s t : VSet n) : s.inter t = t.inter s :=
  ext fun w => by rw [mem_inter, mem_inter, Bool.and_comm]

theorem union_comm (s t : VSet n) : s.union t = t.union s :=
  ext fun w => by rw [mem_union, mem_union, Bool.or_comm]

theorem union_assoc (s t u : VSet n) : (s.union t).union u = s.union (t.union u) :=
  ext fun w => by rw [mem_union, mem_union, mem_union, mem_union, Bool.or_assoc]

theorem cardInter_comm (s t : VSet n) : s.cardInter t = t.cardInter s := by
  rw [cardInter_eq, cardInter_eq, inter_comm]

/-- The count into a singleton is the membership bit. -/
theorem cardInter_singleton (u : Nat) (x : VSet n) :
    ((empty : VSet n).insert u).cardInter x = if x.mem u then 1 else 0 := by
  rw [cardInter_eq, card_eq_countBelow, countBelow]
  rcases hb : x.mem u with _ | _
  · have hz : (List.range n).countP
        (fun v => (((empty : VSet n).insert u).inter x).mem v) = 0 := by
      rw [List.countP_eq_zero]
      intro v _
      rw [mem_inter, mem_singleton]
      rcases Decidable.em (u = v) with rfl | hne
      · simp [hb]
      · simp [hne]
    rw [hz]
    simp
  · have hu : u < n := mem_lt hb
    rw [List.countP_eq_length_filter]
    have hsplit : List.range n = List.range u ++ u :: List.range' (u + 1) (n - (u + 1)) := by
      have h1 := @List.range'_append 0 u (n - u) 1
      rw [Nat.zero_add, Nat.one_mul, show u + (n - u) = n by omega] at h1
      rw [List.range_eq_range', ← h1, ← List.range_eq_range',
        show n - u = (n - (u + 1)) + 1 by omega, List.range'_succ]
    have hfilter : (List.range n).filter
        (fun v => (((empty : VSet n).insert u).inter x).mem v) = [u] := by
      rw [hsplit, List.filter_append, List.filter_cons_of_pos (by
        rw [mem_inter, mem_singleton, beq_self_eq_true, decide_eq_true hu, hb]
        rfl)]
      have hl : (List.range u).filter
          (fun v => (((empty : VSet n).insert u).inter x).mem v) = [] := by
        rw [List.filter_eq_nil_iff]
        intro v hv
        rw [List.mem_range] at hv
        rw [mem_inter, mem_singleton, show (u == v) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega]
        simp
      have hr : (List.range' (u + 1) (n - (u + 1))).filter
          (fun v => (((empty : VSet n).insert u).inter x).mem v) = [] := by
        rw [List.filter_eq_nil_iff]
        intro v hv
        rw [List.mem_range'] at hv
        rw [mem_inter, mem_singleton, show (u == v) = false by
          simp only [beq_eq_false_iff_ne, ne_eq]; omega]
        simp
      rw [hl, hr]
      rfl
    rw [hfilter]
    rfl

/-! # Cardinality comparisons -/

/-- `countP` is monotone under pointwise implication of the predicate
on the list's elements. -/
theorem countP_le_of_imp {α : Type _} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, p x = true → q x = true) →
      l.countP p ≤ l.countP q
  | [], _ => by simp
  | x :: l, h => by
    have hrec : l.countP p ≤ l.countP q :=
      countP_le_of_imp fun y hy => h y (List.mem_cons_of_mem x hy)
    rcases hp : p x with _ | _
    · rw [List.countP_cons_of_neg (by simp [hp])]
      exact Nat.le_trans hrec ((List.sublist_cons_self x l).countP_le)
    · have hq : q x = true := h x (List.mem_cons_self ..) hp
      rw [List.countP_cons_of_pos (by simp [hp]),
        List.countP_cons_of_pos (by simp [hq])]
      omega

/-- Two `filter`s ordered by pointwise implication are equal when they
have the same length. -/
theorem filter_eq_of_imp_of_length_eq {α : Type _} {p q : α → Bool}
    {l : List α} (himp : ∀ x ∈ l, p x = true → q x = true)
    (hlen : (l.filter p).length = (l.filter q).length) :
    l.filter p = l.filter q := by
  have hsub : List.Sublist (l.filter p) (l.filter q) := by
    clear hlen
    induction l with
    | nil => simp
    | cons x l ih =>
      rw [List.filter_cons, List.filter_cons]
      have ih' := ih fun y hy => himp y (List.mem_cons_of_mem x hy)
      rcases hp : p x with _ | _
      · rcases hq : q x with _ | _
        · simpa using ih'
        · exact ih'.trans (List.sublist_cons_self _ _)
      · have hq : q x = true := himp x (List.mem_cons_self ..) hp
        simpa [hq] using ih'.cons_cons x
  exact hsub.eq_of_length hlen

/-- A subset has no more members. -/
theorem card_le_of_subset {s t : VSet n} (h : s.subset t = true) : s.card ≤ t.card := by
  rw [card_eq_countBelow, card_eq_countBelow, countBelow, countBelow]
  exact countP_le_of_imp fun v _ hv => subset_iff.mp h v hv

/-- A set with no members is empty. -/
theorem eq_empty_of_card_eq_zero {s : VSet n} (h : s.card = 0) : s = empty := by
  rw [eq_empty_iff]
  intro v
  rcases Nat.lt_or_ge v n with hv | hv
  · rw [card_eq_countBelow, countBelow, List.countP_eq_zero] at h
    simpa using h v (List.mem_range.mpr hv)
  · exact mem_of_ge hv

/-- A subset with the same member count is the whole set. -/
theorem eq_of_subset_of_card_eq {s t : VSet n} (h : s.subset t = true)
    (hcard : s.card = t.card) : s = t := by
  have hlen : ((List.range n).filter s.mem).length = ((List.range n).filter t.mem).length := by
    have := hcard
    rw [card_eq_countBelow, card_eq_countBelow, countBelow, countBelow,
      List.countP_eq_length_filter, List.countP_eq_length_filter] at this
    exact this
  have hfilter : (List.range n).filter s.mem = (List.range n).filter t.mem :=
    filter_eq_of_imp_of_length_eq (fun v _ hv => subset_iff.mp h v hv) hlen
  refine ext fun v => ?_
  rcases Nat.lt_or_ge v n with hv | hv
  · have hiff := congrArg (fun l => v ∈ l) hfilter
    simp only [List.mem_filter, List.mem_range, hv, true_and, eq_iff_iff] at hiff
    rcases hs : s.mem v with _ | _
    · rcases ht : t.mem v with _ | _
      · rfl
      · exact absurd (hiff.mpr ht) (by simp [hs])
    · exact (subset_iff.mp h v hs).symm
  · rw [mem_of_ge hv, mem_of_ge hv]

/-! # Cardinality under insert and erase -/

theorem countBelow_succ (s : VSet n) (k : Nat) :
    s.countBelow (k + 1) = s.countBelow k + (if s.mem k then 1 else 0) := by
  rw [countBelow, countBelow, List.range_succ, List.countP_append, List.countP_cons,
    List.countP_nil]
  rcases h : s.mem k with _ | _ <;> simp

theorem countBelow_congr {s t : VSet n} {k : Nat}
    (h : ∀ i, i < k → s.mem i = t.mem i) : s.countBelow k = t.countBelow k := by
  induction k with
  | zero => rfl
  | succ m ih =>
    rw [countBelow_succ, countBelow_succ, ih fun i hi => h i (by omega), h m (by omega)]

theorem countBelow_le (s : VSet n) (k : Nat) : s.countBelow k ≤ k := by
  rw [countBelow]
  exact Nat.le_trans List.countP_le_length (Nat.le_of_eq List.length_range)

/-- A set has at most `n` members. -/
theorem card_le (s : VSet n) : s.card ≤ n := by
  rw [card_eq_countBelow]
  exact countBelow_le s n

theorem countBelow_insert_le (s : VSet n) (v k : Nat) :
    (s.insert v).countBelow k ≤ s.countBelow k + 1 := by
  induction k with
  | zero => simp [countBelow]
  | succ m ih =>
    rw [countBelow_succ, countBelow_succ, mem_insert]
    rcases hv : (v == m) with _ | _
    · rcases h : s.mem m with _ | _ <;> simp <;> omega
    · have hvm : v = m := by simpa using hv
      rw [countBelow_congr (t := s) fun i hi => by
        rw [mem_insert, show (v == i) = false from by simp [show v ≠ i from by omega],
          Bool.false_and, Bool.or_false]]
      rcases h : s.mem m with _ | _ <;> rcases hd : decide (v < n) with _ | _ <;> simp <;>
        omega

/-- Inserting adds at most one member. -/
theorem card_insert_le (s : VSet n) (v : Nat) : (s.insert v).card ≤ s.card + 1 := by
  rw [card_eq_countBelow, card_eq_countBelow]
  exact countBelow_insert_le s v n

theorem countBelow_erase_of_mem {s : VSet n} {v : Nat} (h : s.mem v = true) :
    ∀ k, v < k → (s.erase v).countBelow k + 1 = s.countBelow k
  | 0, hv => absurd hv (by omega)
  | m + 1, hv => by
    rcases Decidable.em (v = m) with heq | hne
    · rw [countBelow_succ, countBelow_succ, mem_erase,
        show (v == m) = true from by simp [heq], Bool.not_true, Bool.and_false,
        countBelow_congr (t := s) fun i hi => by
          rw [mem_erase, show (v == i) = false from by simp [show v ≠ i from by omega],
            Bool.not_false, Bool.and_true],
        show s.mem m = true from heq ▸ h]
      simp
    · rw [countBelow_succ, countBelow_succ, mem_erase,
        show (v == m) = false from by simp [hne], Bool.not_false, Bool.and_true]
      have := countBelow_erase_of_mem h m (by omega)
      omega

/-- Erasing a member removes exactly one. -/
theorem card_erase_of_mem {s : VSet n} {v : Nat} (h : s.mem v = true) :
    (s.erase v).card + 1 = s.card := by
  rw [card_eq_countBelow, card_eq_countBelow]
  exact countBelow_erase_of_mem h n (mem_lt h)

/-- Erasing never adds members. -/
theorem card_erase_le (s : VSet n) (v : Nat) : (s.erase v).card ≤ s.card :=
  card_le_of_subset (subset_iff.mpr fun w hw => by
    rw [mem_erase] at hw
    exact ((Bool.and_eq_true _ _).mp hw).1)

/-- Inserting a member changes nothing. -/
theorem insert_of_mem {s : VSet n} {v : Nat} (h : s.mem v = true) : s.insert v = s :=
  ext fun w => by
    rw [mem_insert]
    rcases Decidable.em (v = w) with rfl | hne
    · rw [h, Bool.true_or]
    · rw [show (v == w) = false from by simp [hne], Bool.false_and, Bool.or_false]


end VSet

end Hex.GraphIso.Nauty
