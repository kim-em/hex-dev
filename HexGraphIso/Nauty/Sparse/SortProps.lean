/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Sort
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

open Std.Do

set_option mvcgen.warning false

private theorem swap_perm {a b : Array Nat} (h : a.toList.Perm b.toList) (i j : Nat) :
    (a.swapIfInBounds i j).toList.Perm b.toList := by
  unfold Array.swapIfInBounds
  split
  · split
    · exact (Array.swap_perm _ _).toList.trans h
    · exact h
  · exact h

/-- Moving the hole of insertion sort preserves the list once its saved
entry is restored. The hole and its predecessor are distinct valid indices. -/
private theorem shift_perm (a : Array Nat) (u v value : Nat)
    (hu : u < a.size) (hv : v < a.size) (hne : u ≠ v) :
    ((a.set! u a[v]!).set! v value).toList.Perm (a.set! u value).toList := by
  have hs : (a.set! u value).swapIfInBounds u v = (a.set! u a[v]!).set! v value := by
    apply Array.ext
    · simp
    · intro i hi hj
      simp only [Array.getElem_swapIfInBounds, Array.set!_eq_setIfInBounds]
      split <;> simp_all [Array.getElem_setIfInBounds] <;>
        grind
  rw [← hs]
  exact swap_perm (.refl _) u v

private theorem shift_preserves (a b : Array Nat) (u v value : Nat)
    (hu : u < a.size) (hv : v < a.size) (hne : u ≠ v)
    (h : (a.set! u value).toList.Perm b.toList) :
    ((a.set! u a[v]!).set! v value).toList.Perm b.toList :=
  (shift_perm a u v value hu hv hne).trans h

private theorem shift_step (a b : Array Nat) (start value i j done : Nat)
    (hsize : start + i < b.size) (hdone : done < i)
    (h : (a.set! (start + j) value).toList.Perm b.toList ∧
      j ≤ i ∧ i ≤ j + done) :
    ((a.set! (start + j) a[start + j - 1]!).set! (start + (j - 1)) value).toList.Perm
        b.toList ∧ j - 1 ≤ i ∧ i ≤ (j - 1) + (done + 1) := by
  have hs : a.size = b.size := by simpa using h.1.length_eq
  have hj : 0 < j := by omega
  have he : start + (j - 1) = start + j - 1 := by omega
  refine ⟨?_, by omega, by omega⟩
  rw [he]
  exact shift_preserves a b _ _ value (by omega) (by omega) (by omega) h.1

private theorem restore_self (a : Array Nat) (i : Nat) : a.set! i a[i]! = a := by
  by_cases hi : i < a.size
  · simp [Array.set!, Array.setIfInBounds, hi]
  · simp [Array.set!, Array.setIfInBounds, hi]

/-- Every partition operation is a swap, including the equal-pivot blocks. -/
theorem partition_perm (x y : Array Nat) (start len : Nat) :
    (partition x y start len).1.toList.Perm x.toList := by
  unfold partition
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × Nat × Nat => r.1.toList.Perm x.toList)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ => ⌜s.1.toList.Perm x.toList⌝
  | inv2 => ⇓⟨_, s⟩ => ⌜s.1.toList.Perm x.toList⌝
  | inv3 => ⇓⟨_, s⟩ => ⌜s.1.toList.Perm x.toList⌝
  | inv4 => ⇓⟨_, a⟩ => ⌜a.toList.Perm x.toList⌝
  | inv5 => ⇓⟨_, a⟩ => ⌜a.toList.Perm x.toList⌝
  with grind [swap_perm, List.Perm.refl]

theorem partition_size (x y : Array Nat) (start len : Nat) :
    (partition x y start len).1.size = x.size :=
  (partition_perm x y start len).length_eq

theorem insertion_size (x y : Array Nat) (start len : Nat) :
    (insertion x y start len).size = x.size := by
  unfold insertion
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => a.size = x.size)
  mvcgen invariants
  | inv1 => ⇓⟨_, a⟩ => ⌜a.size = x.size⌝
  | inv2 => ⇓⟨_, s⟩ => ⌜s.1.size = x.size⌝
  with grind

theorem insertion_perm (x y : Array Nat) (start len : Nat) (h : start + len ≤ x.size) :
    (insertion x y start len).toList.Perm x.toList := by
  unfold insertion
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => a.toList.Perm x.toList)
  mvcgen invariants
  | inv1 => ⇓⟨_, a⟩ => ⌜a.toList.Perm x.toList⌝
  | inv2 pref i suff he a tmp key ha => ⇓⟨cursor, s⟩ =>
      ⌜(s.1.set! (start + s.2) tmp).toList.Perm x.toList ∧
        s.2 ≤ i ∧ i ≤ s.2 + cursor.prefix.length⌝
  all_goals
    simp +zetaDelta only [Array.set!_eq_setIfInBounds, Std.Legacy.Range.toList,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at *
    try grind only [List.Perm.refl, List.length_range', List.length_append,
      List.length_cons, List.length_nil, List.mem_of_range'_eq_append_cons,
      List.mem_range'_1, shift_step, restore_self]
  case vc4.step.pre =>
    rename_i pref i suff a tmp key ha hi
    change (a.set! (start + i) a[start + i]!).toList.Perm x.toList ∧ _
    rw [restore_self]
    exact ⟨ha, Nat.le_refl _, by simp⟩
  case vc2.step.isFalse.isTrue | vc3.step.isFalse.isFalse =>
    rename_i pref i suff a tmp key ha pref' t suff' s ax j hc next nextj hz hs hi ht
    have hi' : i < len := by
      have hm : i ∈ List.range' 1 (len - 1) := by rw [hi]; simp
      simp only [List.mem_range'_1] at hm
      omega
    have hd : pref'.length < i := by
      have he := congrArg List.length ht
      simp only [List.length_range', List.length_append, List.length_cons] at he
      omega
    have hm := shift_step s.1 x start (a[start + i]!) i s.2 pref'.length
      (by omega) hd hs
    refine ⟨hm.1, hm.2.1, ?_⟩
    simp only [List.length_range', List.length_append, List.length_cons, List.length_nil]
    omega

/-- Both returned subsegments lie in the segment passed to partition. -/
theorem partition_bounds (x y : Array Nat) (start len : Nat) :
    (partition x y start len).2.1 ≤ len ∧ (partition x y start len).2.2 ≤ len := by
  unfold partition
  apply Id.of_wp_run_eq rfl (fun r : Array Nat × Nat × Nat => r.2.1 ≤ len ∧ r.2.2 ≤ len)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ =>
      ⌜start ≤ s.2.1 ∧ s.2.1 ≤ s.2.2.1 ∧ s.2.2.1 ≤ start + len ∧
        start ≤ s.2.2.2.1 ∧ s.2.2.2.1 ≤ s.2.2.2.2 ∧ s.2.2.2.2 ≤ start + len⌝
  | inv2 => ⇓⟨_, s⟩ => ⌜start ≤ s.2.1 ∧ s.2.1 ≤ s.2.2 ∧ s.2.2 ≤ start + len⌝
  | inv3 => ⇓⟨_, s⟩ => ⌜start ≤ s.2.1 ∧ s.2.1 ≤ s.2.2 ∧ s.2.2 ≤ start + len⌝
  | inv4 => ⇓⟨_, _⟩ => ⌜True⌝
  | inv5 => ⇓⟨_, _⟩ => ⌜True⌝
  with grind

theorem indirect_size (x y : Array Nat) (start len : Nat) :
    (indirect x y start len).size = x.size := by
  unfold indirect
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => a.size = x.size)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ => ⌜s.1.size = x.size⌝
  with grind [partition_size, insertion_size]

/-- The exact indirect sort preserves every entry, including its repeated
keys. The work stack contains only subsegments of the original array. -/
theorem indirect_perm (x y : Array Nat) (start len : Nat) (h : start + len ≤ x.size) :
    (indirect x y start len).toList.Perm x.toList := by
  unfold indirect
  apply Id.of_wp_run_eq rfl (fun a : Array Nat => a.toList.Perm x.toList)
  mvcgen invariants
  | inv1 => ⇓⟨_, s⟩ => ⌜s.1.toList.Perm x.toList ∧ s.1.size = x.size ∧
      ∀ p ∈ s.2, p.1 + p.2 ≤ x.size⌝
  all_goals
    simp_all +zetaDelta only [List.mem_cons, List.not_mem_nil, forall_eq_or_imp] <;>
    grind [partition_size, insertion_size, partition_perm, insertion_perm,
      partition_bounds, List.Perm.refl, List.Perm.trans]

end Hex.GraphIso.Nauty.Sparse.Sort
