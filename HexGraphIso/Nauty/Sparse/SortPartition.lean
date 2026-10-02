/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortOrder
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

theorem get_swap (x : Array Nat) (i j q : Nat)
    (hi : i < x.size) (hj : j < x.size) (hq : q < x.size) :
    (x.swapIfInBounds i j)[q]! = if q = i then x[j]! else if q = j then x[i]! else x[q]! := by
  rw [getElem!_pos (x.swapIfInBounds i j) q (by simpa), Array.getElem_swapIfInBounds]
  simp only [hi, hj, and_true, getElem!_pos x i hi, getElem!_pos x j hj, getElem!_pos x q hq]
  split <;> (try split) <;> simp_all

/-- The four processed regions around the unscanned interval `[b,c)`.
The equal-pivot regions remain at the two ends until the final block swaps. -/
structure Cuts (x y : Array Nat) (lo hi v a b c d : Nat) : Prop where
  bounds : lo ≤ a ∧ a ≤ b ∧ b ≤ c ∧ c ≤ d ∧ d ≤ hi
  left_eq : ∀ q, lo ≤ q → q < a → y[x[q]!]! = v
  left_lt : ∀ q, a ≤ q → q < b → y[x[q]!]! < v
  right_gt : ∀ q, c ≤ q → q < d → v < y[x[q]!]!
  right_eq : ∀ q, d ≤ q → q < hi → y[x[q]!]! = v

namespace Cuts

theorem initial (x y : Array Nat) (lo hi v : Nat) (h : lo ≤ hi) :
    Cuts x y lo hi v lo lo hi hi := by
  constructor <;> intros <;> omega

theorem left_lt_step {x y : Array Nat} {lo hi v a b c d : Nat}
    (h : Cuts x y lo hi v a b c d) (hbc : b < c) (hk : y[x[b]!]! < v) :
    Cuts x y lo hi v a (b + 1) c d := by
  rcases h with ⟨hb, he, hl, hg, hr⟩
  refine ⟨by omega, he, ?_, hg, hr⟩
  intro q hq hq'
  by_cases hqb : q = b
  · simpa only [hqb] using hk
  · exact hl q hq (by omega)

theorem right_gt_step {x y : Array Nat} {lo hi v a b c d : Nat}
    (h : Cuts x y lo hi v a b c d) (hbc : b < c) (hk : v < y[x[c - 1]!]!) :
    Cuts x y lo hi v a b (c - 1) d := by
  rcases h with ⟨hb, he, hl, hg, hr⟩
  refine ⟨by omega, he, hl, ?_, hr⟩
  intro q hq hq'
  by_cases hqc : q = c - 1
  · simpa only [hqc] using hk
  · exact hg q (by omega) hq'

theorem left_eq_step {x y : Array Nat} {lo hi v a b c d : Nat}
    (h : Cuts x y lo hi v a b c d) (hs : hi ≤ x.size)
    (hbc : b < c) (hk : y[x[b]!]! = v) :
    Cuts (x.swapIfInBounds a b) y lo hi v (a + 1) (b + 1) c d := by
  rcases h with ⟨hb, he, hl, hg, hr⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  all_goals
    intro q hq hq'
    rw [get_swap _ _ _ _ (by omega) (by omega) (by omega)]
    split <;> (try split) <;> grind

theorem right_eq_step {x y : Array Nat} {lo hi v a b c d : Nat}
    (h : Cuts x y lo hi v a b c d) (hs : hi ≤ x.size)
    (hbc : b < c) (hk : y[x[c - 1]!]! = v) :
    Cuts (x.swapIfInBounds (c - 1) (d - 1)) y lo hi v a b (c - 1) (d - 1) := by
  rcases h with ⟨hb, he, hl, hg, hr⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  all_goals
    intro q hq hq'
    rw [get_swap _ _ _ _ (by omega) (by omega) (by omega)]
    split <;> (try split) <;> grind

theorem cross {x y : Array Nat} {lo hi v a b c d : Nat}
    (h : Cuts x y lo hi v a b c d) (hs : hi ≤ x.size)
    (hbc : b < c) (hl : v < y[x[b]!]!) (hr : y[x[c - 1]!]! < v) :
    Cuts (x.swapIfInBounds b (c - 1)) y lo hi v a (b + 1) (c - 1) d := by
  have hgap : b + 1 < c := by
    by_cases hn : b + 1 < c
    · exact hn
    have he : b = c - 1 := by omega
    rw [he] at hl
    omega
  rcases h with ⟨hb, he, hlt, hgt, he'⟩
  refine ⟨by omega, ?_, ?_, ?_, ?_⟩
  all_goals
    intro q hq hq'
    rw [get_swap _ _ _ _ (by omega) (by omega) (by omega)]
    split <;> (try split) <;> grind

end Cuts

/-- Allocation, exterior entries, and an occurrence of the sampled pivot
are preserved by every partition swap. -/
structure Store (x base y : Array Nat) (lo hi v : Nat) : Prop where
  size_eq : x.size = base.size
  outside : ∀ q, q < lo ∨ hi ≤ q → x[q]! = base[q]!
  seen : ∃ q, lo ≤ q ∧ q < hi ∧ y[x[q]!]! = v

theorem Store.swap {x base y : Array Nat} {lo hi v i j : Nat}
    (h : Store x base y lo hi v) (hs : hi ≤ x.size)
    (hib : lo ≤ i ∧ i < hi) (hj : lo ≤ j ∧ j < hi) :
    Store (x.swapIfInBounds i j) base y lo hi v := by
  refine ⟨by simpa using h.size_eq, ?_, ?_⟩
  · intro q hq
    by_cases hqb : q < x.size
    · rw [get_swap _ _ _ _ (by omega) (by omega) hqb,
        ite_eq_right (by omega), ite_eq_right (by omega)]
      exact h.outside q hq
    · have hbase : ¬q < base.size := by rw [← h.size_eq]; exact hqb
      rw [getElem!_neg (x.swapIfInBounds i j) q (by simp only [Array.size_swapIfInBounds]; omega),
        getElem!_neg base q hbase]
  · obtain ⟨q, hql, hqu, he⟩ := h.seen
    by_cases hqi : q = i
    · refine ⟨j, hj.1, hj.2, ?_⟩
      rw [get_swap _ _ _ _ (by omega) (by omega) (by omega)]
      split <;> (try split) <;> simp_all
    · by_cases hqj : q = j
      · refine ⟨i, hib.1, hib.2, ?_⟩
        rw [get_swap _ _ _ _ (by omega) (by omega) (by omega), ite_eq_left rfl]
        simpa only [hqj] using he
      · refine ⟨q, hql, hqu, ?_⟩
        rw [get_swap _ _ _ _ (by omega) (by omega) (by omega),
          ite_eq_right hqi, ite_eq_right hqj]
        exact he

/-- The two recursive fragments omit at least one pivot occurrence. -/
theorem Cuts.proper {x base y : Array Nat} {lo hi v a b c d : Nat}
    (h : Cuts x y lo hi v a b c d) (hs : Store x base y lo hi v) :
    (b - a) + (d - c) < hi - lo := by
  obtain ⟨q, hql, hqu, he⟩ := hs.seen
  have hb := h.bounds
  by_cases hp : (b - a) + (d - c) < hi - lo
  · exact hp
  have ha : a = lo := by omega
  have hc : c = b := by omega
  have hd : d = hi := by omega
  by_cases hqb : q < b
  · have hk := h.left_lt q (by omega) hqb
    omega
  · have hk := h.right_gt q (by omega) (by omega)
    omega

/-- The right scan preserves the left scan's stopping condition. -/
theorem right_stop (x y : Array Nat) (b c d v : Nat)
    (hbc : b < c) (hcd : c ≤ d) (hs : d ≤ x.size)
    (h : b = c ∨ v < y[x[b]!]!) :
    b = c - 1 ∨ v < y[(x.swapIfInBounds (c - 1) (d - 1))[b]!]! := by
  by_cases he : b = c - 1
  · exact Or.inl he
  · apply Or.inr
    rw [get_swap _ _ _ _ (by omega) (by omega) (by omega),
      ite_eq_right he, ite_eq_right (by omega)]
    rcases h with h | h
    · omega
    · exact h

/-- The recursive fragments exclude a pivot entry, and all swaps stay
inside the requested segment. -/
theorem partition_proper (x y : Array Nat) (start len : Nat)
    (hb : start + len ≤ x.size) (hl : 0 < len) :
    (partition x y start len).2.1 + (partition x y start len).2.2 < len ∧
      ∀ q, q < start ∨ start + len ≤ q → (partition x y start len).1[q]! = x[q]! := by
  unfold partition
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × Nat × Nat =>
    r.2.1 + r.2.2 < len ∧ ∀ q, q < start ∨ start + len ≤ q → r.1[q]! = x[q]!)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ => ⌜
      Cuts s.1 y start (start + len) (pivot x y start len)
        s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2 ∧
      Store s.1 x y start (start + len) (pivot x y start len)⌝
  | inv2 pref it suff hr outer xs pair a pair2 b pair3 c d hout => ⇓⟨cursor, s⟩ => ⌜
      Cuts s.1 y start (start + len) (pivot x y start len) s.2.1 s.2.2 c d ∧
      Store s.1 x y start (start + len) (pivot x y start len) ∧
      (start + cursor.prefix.length ≤ s.2.2 ∨ (cursor.suffix = [] ∧
        (s.2.2 = c ∨ pivot x y start len < y[s.1[s.2.2]!]!)))⌝
  | inv3 pref it suff hr outer xs pair a0 pair2 b0 pair3 c d hout r xr rest a b hleft =>
      ⇓⟨cursor, s⟩ => ⌜
      Cuts s.1 y start (start + len) (pivot x y start len) a b s.2.1 s.2.2 ∧
      Store s.1 x y start (start + len) (pivot x y start len) ∧
      (b = s.2.1 ∨ pivot x y start len < y[s.1[b]!]!) ∧
      (s.2.1 + cursor.prefix.length ≤ start + len ∨ (cursor.suffix = [] ∧
        (b = s.2.1 ∨ y[s.1[s.2.1 - 1]!]! < pivot x y start len)))⌝
  | inv4 => ⇓⟨_, a⟩ => ⌜Store a x y start (start + len) (pivot x y start len)⌝
  | inv5 => ⇓⟨_, a⟩ => ⌜Store a x y start (start + len) (pivot x y start len)⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.add_sub_cancel, Nat.sub_zero,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.length_range', Nat.add_zero] at *
  all_goals
    try simp_all only [Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
      List.cons_ne_nil, false_and, or_false, true_and, Nat.zero_add]
  case vc11.pre =>
    refine ⟨Cuts.initial _ _ _ _ _ (by omega), ⟨rfl, fun _ _ => rfl, ?_⟩⟩
    obtain ⟨i, hi, he⟩ := pivot_mem x y start len hl
    exact ⟨start + i, by omega, by omega, he.symm⟩
  case vc16.post.success.post.success.post.success =>
    rename_i hout middle right hmid result hresult
    exact ⟨by simpa only [Nat.add_sub_cancel_left] using hout.1.proper hout.2, hresult.outside⟩
  all_goals
    try grind only [Cuts.bounds, Store.size_eq, Cuts.left_lt_step, Cuts.right_gt_step,
      Cuts.left_eq_step, Store.swap, Cuts.cross,
      List.mem_of_range'_eq_append_cons, List.mem_range'_1]
  case vc1.step.isTrue =>
    rename_i hguard hin hr hs
    have hbounds := hin.1.bounds
    omega
  case vc2.step.isFalse.isTrue =>
    rename_i hguard heq hin hr hs
    have hbounds := hin.1.bounds
    have hsize := hin.2.1.size_eq
    refine ⟨hin.1.left_eq_step (by omega) (by omega) heq, ?_, Or.inl (by omega)⟩
    apply hin.2.1.swap <;> omega
  case vc4.step.pre =>
    rename_i hin hr
    have hbounds := hin.1.bounds
    exact Or.inl (by omega)
  case vc5.step.isTrue =>
    rename_i hguard hin hr hs hleft
    have hbounds := hin.1.bounds
    omega
  case vc6.step.isFalse.isTrue =>
    rename_i hguard heq hin hr hs hleft
    have hbounds := hin.1.bounds
    have hsize := hin.2.1.size_eq
    refine ⟨hin.1.right_eq_step (by omega) (by omega) heq, ?_, ?_, Or.inl (by omega)⟩
    · apply hin.2.1.swap <;> omega
    · exact right_stop _ _ _ _ _ _ (by omega) (by omega) (by omega) hin.2.2.1
  case vc8.step.post.success.pre =>
    rename_i hr hin
    have hbounds := hin.1.bounds
    exact ⟨by omega, Or.inl (by omega)⟩
  case vc10.step.post.success.post.success.isFalse =>
    rename_i hguard next b c hr hleft hin
    have hbounds := hin.1.bounds
    have hsize := hin.2.1.size_eq
    refine ⟨hin.1.cross (by omega) (by omega) (by omega) (by omega), ?_⟩
    apply hin.2.1.swap <;> omega
  case vc12.step =>
    rename_i hout pref i suff a next hin hr
    have hbounds := hout.1.bounds
    have hi := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Nat.zero_add] at hi
    have hsize := hin.size_eq
    apply hin.swap <;> omega
  case vc14.step =>
    rename_i hout middle right hmid pref i suff a next hin hr
    have hbounds := hout.1.bounds
    have hi := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Nat.zero_add] at hi
    have hsize := hin.size_eq
    apply hin.swap <;> omega

end Hex.GraphIso.Nauty.Sparse.Sort
