/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortPartition

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem range_cursor {first last cur : Nat} {pref suff : List Nat}
    (h : first ≤ last)
    (hr : [first:last].toList = pref ++ cur :: suff) : cur + suff.length + 1 = last := by
  simp only [Std.Legacy.Range.toList, Nat.div_one, Nat.add_sub_cancel] at hr
  have hs := congrArg List.length hr
  have hp := List.eq_of_range'_eq_append_cons hr
  simp only [List.length_range', List.length_append, List.length_cons, Nat.one_mul] at hs hp
  omega

/-- Reading after a bounded-array write, in the form used by refinement's
insertion and scatter operations. -/
theorem get_set (a : Array Nat) (i v q : Nat) (hq : q < a.size) :
    (a.set! i v)[q]! = if q = i then v else a[q]! := by
  by_cases he : q = i
  · subst q; rw [Array.getElem!_set!_self _ _ _ hq, ite_eq_left rfl]
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm he), ite_eq_right he]

/-- The two-write exchange also covers equal indices. -/
theorem exchange_eq (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    (a.set! i a[j]!).set! j a[i]! = a.swapIfInBounds i j := by
  apply Array.ext
  · simp
  · intro q hq hq'
    have hb : q < a.size := by simpa using hq
    have h := Sort.get_swap a i j q hi hj hb
    rw [← getElem!_pos _ q hq, ← getElem!_pos _ q hq',
      get_set _ _ _ _ (by simpa), get_set _ _ _ _ hb, h]
    split <;> (try split) <;> simp_all

/-- Nauty's three writes are two exchanges even when neighbouring cut
positions coincide. The order excludes a nonadjacent index collision. -/
theorem rotate_eq (a : Array Nat) (i j k : Nat)
    (hkj : k ≤ j) (hji : j ≤ i) (hi : i < a.size) :
    ((a.set! i a[j]!).set! j a[k]!).set! k a[i]! =
      (a.swapIfInBounds i j).swapIfInBounds j k := by
  have hj : j < a.size := by omega
  have hk : k < a.size := by omega
  apply Array.ext
  · simp
  · intro q hq hq'
    have hb : q < a.size := by simpa using hq
    rw [← getElem!_pos _ q hq, ← getElem!_pos _ q hq',
      get_set _ _ _ _ (by simpa), get_set _ _ _ _ (by simpa), get_set _ _ _ _ hb,
      Sort.get_swap _ _ _ _ (by simpa) (by simpa) (by simpa),
      Sort.get_swap _ _ _ _ hi hj hk, Sort.get_swap _ _ _ _ hi hj hj,
      Sort.get_swap _ _ _ _ hi hj hb]
    split <;> (try split) <;> (try split) <;> grind

theorem swap_perm (a : Array Nat) (i j : Nat) :
    (a.swapIfInBounds i j).toList.Perm a.toList := by
  unfold Array.swapIfInBounds
  split
  · split
    · exact (Array.swap_perm _ _).toList
    · exact .refl _
  · exact .refl _

theorem exchange_perm (a : Array Nat) (i j : Nat) (hi : i < a.size) (hj : j < a.size) :
    ((a.set! i a[j]!).set! j a[i]!).toList.Perm a.toList := by
  rw [exchange_eq a i j hi hj]
  exact swap_perm a i j

theorem rotate_perm (a : Array Nat) (i j k : Nat)
    (hkj : k ≤ j) (hji : j ≤ i) (hi : i < a.size) :
    (((a.set! i a[j]!).set! j a[k]!).set! k a[i]!).toList.Perm a.toList := by
  rw [rotate_eq a i j k hkj hji hi]
  exact (swap_perm _ j k).trans (swap_perm a i j)

/-- The second source read in the executed rotation follows its first write.
If that write aliases the read, all three positions coincide. -/
theorem rotate_read (a : Array Nat) (i j k : Nat)
    (hkj : k ≤ j) (hji : j ≤ i) (hi : i < a.size) :
    (a.set! i a[j]!)[k]! = a[k]! := by
  rw [get_set _ _ _ _ (by omega)]
  split
  · next he =>
    have hj : j = k := by omega
    rw [hj]
  · rfl

theorem perm_size {a b : Array Nat} (h : a.toList.Perm b.toList) : a.size = b.size :=
  h.length_eq

theorem indirect_perm {a b y : Array Nat} {start len : Nat}
    (h : a.toList.Perm b.toList) (hb : start + len ≤ b.size) :
    (Sort.indirect a y start len).toList.Perm b.toList :=
  (Sort.indirect_perm a y start len (by rw [perm_size h]; exact hb)).trans h

end Hex.GraphIso.Nauty.Sparse
