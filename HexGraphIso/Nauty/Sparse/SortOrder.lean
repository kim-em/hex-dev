/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortProps
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- Key order on a segment, using the same indirect reads as the executable. -/
@[expose] def Sorted (x y : Array Nat) (start len : Nat) : Prop :=
  ∀ i j, i < j → j < len → y[x[start + i]!]! ≤ y[x[start + j]!]!

theorem Sorted.mono {x y : Array Nat} {start len small : Nat}
    (h : Sorted x y start len) (hs : small ≤ len) : Sorted x y start small :=
  fun i j hij hj => h i j hij (by omega)

private theorem get_set (a : Array Nat) (i v j : Nat) (hj : j < a.size) :
    (a.set! i v)[j]! = if i = j then v else a[j]! := by
  by_cases he : i = j
  · subst i
    rw [Array.getElem!_set!_self _ _ _ hj, ite_eq_left rfl]
  · rw [Array.getElem!_set!_ne _ _ _ _ he, ite_eq_right he]

/-- Removing the hole leaves a sorted sequence; the saved entry precedes
every element already shifted to its right. -/
private def Hole (a y : Array Nat) (start last hole key : Nat) : Prop :=
  (∀ u v, u < v → v ≤ last → u ≠ hole → v ≠ hole →
    y[a[start + u]!]! ≤ y[a[start + v]!]!) ∧
  ∀ v, hole < v → v ≤ last → key ≤ y[a[start + v]!]!

private def Ready (a y : Array Nat) (start hole key : Nat) : Prop :=
  hole = 0 ∨ y[a[start + hole - 1]!]! ≤ key

private theorem hole_start (a y : Array Nat) (start last : Nat)
    (hs : Sorted a y start last) : Hole a y start last last y[a[start + last]!]! := by
  constructor
  · intro u v huv hv _ hvh
    exact hs u v huv (by omega)
  · intro v hv hvl
    omega

private theorem hole_shift (a y : Array Nat) (start last hole key : Nat)
    (hb : start + last < a.size) (hh : 0 < hole) (hl : hole ≤ last)
    (h : Hole a y start last hole key) (hkey : key < y[a[start + hole - 1]!]!) :
    Hole (a.set! (start + hole) a[start + hole - 1]!) y start last (hole - 1) key := by
  have he : start + hole - 1 = start + (hole - 1) := by omega
  constructor
  · intro u v huv hv huh hvh
    rw [get_set _ _ _ _ (by omega), get_set _ _ _ _ (by omega)]
    split <;> split
    · omega
    · next hu hv' =>
      have hue : u = hole := by omega
      rw [he]
      exact h.1 (hole - 1) v (by omega) hv (by omega) (by omega)
    · next hu hv' =>
      have hve : v = hole := by omega
      rw [he]
      exact h.1 u (hole - 1) (by omega) (by omega) (by omega) (by omega)
    · next hu hv' => exact h.1 u v huv hv (by omega) (by omega)
  · intro v hv hvl
    rw [get_set _ _ _ _ (by omega)]
    split
    · exact Nat.le_of_lt hkey
    · next hne => exact h.2 v (by omega) hvl

private theorem hole_close (a y : Array Nat) (start last hole value : Nat)
    (hb : start + last < a.size) (hh : hole ≤ last)
    (h : Hole a y start last hole y[value]!) (hr : Ready a y start hole y[value]!) :
    Sorted (a.set! (start + hole) value) y start (last + 1) := by
  intro u v huv hv
  rw [get_set _ _ _ _ (by omega), get_set _ _ _ _ (by omega)]
  split <;> split
  · omega
  · next hu hv' => exact h.2 v (by omega) (by omega)
  · next hu hv' =>
    have hve : v = hole := by omega
    have hhpos : 0 < hole := by omega
    have hr' : y[a[start + (hole - 1)]!]! ≤ y[value]! := by
      rcases hr with hz | hr
      · omega
      · simpa only [show start + hole - 1 = start + (hole - 1) by omega] using hr
    by_cases he : u = hole - 1
    · simpa only [he] using hr'
    · exact Nat.le_trans (h.1 u (hole - 1) (by omega) (by omega) (by omega) (by omega)) hr'
  · next hu hv' => exact h.1 u v huv (by omega) (by omega) (by omega)

/-- The executed short-segment insertion sort orders the indirect keys. -/
theorem insertion_sorted (x y : Array Nat) (start len : Nat)
    (hb : start + len ≤ x.size) : Sorted (insertion x y start len) y start len := by
  unfold insertion
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => Sorted a y start len)
  mvcgen invariants
  | inv1 => ⇓⟨cursor, a⟩ => ⌜a.size = x.size ∧ Sorted a y start (1 + cursor.prefix.length)⌝
  | inv2 pref i suff he a tmp key ha => ⇓⟨cursor, s⟩ => ⌜
      s.1.size = x.size ∧ Hole s.1 y start i s.2 key ∧ s.2 ≤ i ∧
      ((0 < s.2 ∧ s.2 + cursor.prefix.length = i) ∨
        (cursor.suffix = [] ∧ Ready s.1 y start s.2 key))⌝
  all_goals
    simp +zetaDelta only [Std.Legacy.Range.toList, Nat.add_sub_cancel, Nat.sub_zero,
      Nat.div_one, List.length_append, List.length_cons, List.length_nil,
      List.length_range', Nat.add_zero] at *
  case vc1.step.isTrue => grind [Ready]
  case vc2.step.isFalse.isTrue | vc3.step.isFalse.isFalse =>
    rename_i pref i suff a tmp key hout pref' z suff' s ax j hkey next nextj hz hin hr he
    have hi := List.mem_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1] at hi
    rcases hin with ⟨hsize, hhole, hle, hlive⟩
    simp only [List.cons_ne_nil, false_and, or_false] at hlive
    have hbound : start + i < s.1.size := by omega
    refine ⟨by simpa using hsize,
      hole_shift _ _ _ _ _ _ hbound hlive.1 hle hhole (by omega), by omega, ?_⟩
    all_goals simp only [beq_iff_eq] at hz
    all_goals simp only [Ready]
    all_goals first
      | exact Or.inr ⟨trivial, Or.inl hz⟩
      | exact Or.inl ⟨by omega, by omega⟩
  case vc4.step.pre =>
    rename_i pref i suff a tmp key hout hr
    have hi := List.mem_of_range'_eq_append_cons hr
    have hic := List.eq_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Nat.one_mul] at hi hic
    refine ⟨hout.1, hole_start _ _ _ _ ?_, Nat.le_refl _, Or.inl ⟨by omega, trivial⟩⟩
    simpa only [← hic] using hout.2
  case vc5.step.post.success =>
    rename_i pref i suff a tmp key hout r ax j next hr hin
    have hi := List.mem_of_range'_eq_append_cons hr
    have hic := List.eq_of_range'_eq_append_cons hr
    simp only [List.mem_range'_1, Nat.one_mul] at hi hic
    have hready : Ready r.1 y start r.2 y[a[start + i]!]! := by
      rcases hin.2.2.2 with h | h
      · omega
      · exact h.2
    refine ⟨by simpa using hin.1, ?_⟩
    have hsize := hin.1
    have h := hole_close r.1 y start i r.2 a[start + i]! (by omega) hin.2.2.1 hin.2.1 hready
    simpa only [hic, Nat.zero_add, Nat.add_assoc] using h
  case vc6.pre => exact ⟨trivial, fun i j hij hj => by omega⟩
  case vc7.post.success =>
    rename_i a h
    exact h.2.mono (by omega)

/-- Insertion sort leaves every entry outside its segment unchanged. -/
theorem insertion_outside (x y : Array Nat) (start len q : Nat)
    (hq : q < start ∨ start + len ≤ q) : (insertion x y start len)[q]! = x[q]! := by
  unfold insertion
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => a[q]! = x[q]!)
  mvcgen invariants
  | inv1 => ⇓⟨_, a⟩ => ⌜a[q]! = x[q]!⌝
  | inv2 pref i suff he a tmp key ha => ⇓⟨_, s⟩ => ⌜s.1[q]! = x[q]! ∧ s.2 ≤ i⌝
  with grind [Array.getElem!_set!_ne]

/-- A median is one of its samples, including when sample keys coincide. -/
theorem median_mem (a b c : Nat) : median a b c = a ∨ median a b c = b ∨ median a b c = c := by
  unfold median
  grind

/-- Both pinned pivot schemes choose a key belonging to the nonempty segment. -/
theorem pivot_mem (x y : Array Nat) (start len : Nat) (hl : 0 < len) :
    ∃ i, i < len ∧ pivot x y start len = y[x[start + i]!]! := by
  have hm (a b c : Nat)
      (ha : ∃ i, i < len ∧ a = y[x[start + i]!]!)
      (hb : ∃ i, i < len ∧ b = y[x[start + i]!]!)
      (hc : ∃ i, i < len ∧ c = y[x[start + i]!]!) :
      ∃ i, i < len ∧ median a b c = y[x[start + i]!]! := by
    rcases median_mem a b c with h | h | h
    · simpa only [h] using ha
    · simpa only [h] using hb
    · simpa only [h] using hc
  unfold pivot
  split
  · apply hm
    · exact ⟨0, hl, rfl⟩
    · exact ⟨len / 2, by omega, rfl⟩
    · exact ⟨len - 1, by omega, rfl⟩
  · apply hm <;> apply hm
    all_goals refine ⟨_, ?_, rfl⟩
    all_goals omega

end Hex.GraphIso.Nauty.Sparse.Sort
