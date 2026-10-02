/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SortPartition

public section

namespace Hex.GraphIso.Nauty.Sparse.Sort

set_option maxHeartbeats 800000

/-- Pointwise state of the two disjoint blocks after exchanging their
first `done` entries. -/
@[expose] def Blocks (a base : Array Nat) (left right done : Nat) : Prop :=
  a.size = base.size ∧ ∀ q, a[q]! =
    if left ≤ q ∧ q < left + done then base[right + (q - left)]!
    else if right ≤ q ∧ q < right + done then base[left + (q - right)]!
    else base[q]!

theorem Blocks.initial (a : Array Nat) (left right : Nat) :
    Blocks a a left right 0 := by
  refine ⟨rfl, ?_⟩
  intro q
  simp (disch := omega) only [ite_eq_right]

theorem Blocks.step {a base : Array Nat} {left right count done : Nat}
    (h : Blocks a base left right done) (hleft : left + count ≤ right)
    (hright : right + count ≤ base.size) (hd : done < count) :
    Blocks (a.swapIfInBounds (left + done) (right + done)) base left right (done + 1) := by
  have hsize := h.1
  refine ⟨by simpa using h.1, ?_⟩
  intro q
  by_cases hq : q < a.size
  · rw [get_swap _ _ _ _ (by omega) (by omega) hq]
    simp only [h.2]
    split <;> (try split)
    all_goals try simp (disch := omega) only [ite_eq_left, ite_eq_right]
    all_goals grind
  · rw [getElem!_neg (a.swapIfInBounds _ _) q (by simpa using hq)]
    simp (disch := omega) only [ite_eq_right, getElem!_neg base q (by omega)]

/-- After moving the equal keys from the left end, the left recursive
fragment precedes that pivot block. The right half is unchanged. -/
theorem Cuts.left_block {x y out : Array Nat} {lo hi v a b d : Nat}
    (h : Cuts x y lo hi v a b b d)
    (hs : Blocks out x lo (b - min (a - lo) (b - a)) (min (a - lo) (b - a))) :
    Cuts out y lo hi v lo (lo + (b - a)) b d ∧
      (∀ q, lo + (b - a) ≤ q → q < b → y[out[q]!]! = v) := by
  have hb := h.bounds
  constructor
  · refine ⟨by omega, by intros; omega, ?_, ?_, ?_⟩
    · intro q hql hqu
      rw [hs.2]
      split
      · exact h.left_lt _ (by omega) (by omega)
      · split
        · next hq => omega
        · exact h.left_lt _ (by omega) (by omega)
    · intro q hql hqu
      rw [hs.2]
      simp (disch := omega) only [ite_eq_right]
      exact h.right_gt q hql hqu
    · intro q hql hqu
      rw [hs.2]
      simp (disch := omega) only [ite_eq_right]
      exact h.right_eq q hql hqu
  · intro q hql hqu
    rw [hs.2]
    split
    · next hq => omega
    · split
      · exact h.left_eq _ (by omega) (by omega)
      · exact h.left_eq _ (by omega) (by omega)

/-- The final partition has strictly smaller keys, equal pivot keys,
and strictly larger keys in three consecutive intervals. -/
structure Separated (x y : Array Nat) (lo hi v left right : Nat) : Prop where
  bounds : lo ≤ left ∧ left ≤ right ∧ right ≤ hi
  lt : ∀ q, lo ≤ q → q < left → y[x[q]!]! < v
  eq : ∀ q, left ≤ q → q < right → y[x[q]!]! = v
  gt : ∀ q, right ≤ q → q < hi → v < y[x[q]!]!

theorem Cuts.right_block {x y out : Array Nat} {lo hi v left b d : Nat}
    (h : Cuts x y lo hi v lo left b d)
    (he : ∀ q, left ≤ q → q < b → y[x[q]!]! = v)
    (hs : Blocks out x b (hi - min (d - b) (hi - d)) (min (d - b) (hi - d))) :
    Separated out y lo hi v left (hi - (d - b)) := by
  have hb := h.bounds
  refine ⟨by omega, ?_, ?_, ?_⟩
  · intro q hql hqu
    rw [hs.2]
    simp (disch := omega) only [ite_eq_right]
    exact h.left_lt q hql hqu
  · intro q hql hqu
    rw [hs.2]
    split
    · exact h.right_eq _ (by omega) (by omega)
    · split
      · next hq => omega
      · by_cases hqb : q < b
        · exact he q hql hqb
        · exact h.right_eq _ (by omega) (by omega)
  · intro q hql hqu
    rw [hs.2]
    split
    · next hq => omega
    · split
      · exact h.right_gt _ (by omega) (by omega)
      · exact h.right_gt _ (by omega) (by omega)

end Hex.GraphIso.Nauty.Sparse.Sort
