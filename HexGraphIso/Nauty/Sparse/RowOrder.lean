/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Key

public section

namespace Hex.GraphIso.Nauty.Sparse.RowOrder

open Std
attribute [local instance] lexOrd

theorem degree_lt {a b : List (Fin n)} (h : b.length < a.length) : rowCmp a b = .lt := by
  change (compare b.length a.length).then (compare b a) = .lt
  have hc : compare b.length a.length = .lt := compareOfLessAndEq_eq_lt.mpr h
  simp [hc]

theorem degree_gt {a b : List (Fin n)} (h : a.length < b.length) : rowCmp a b = .gt := by
  exact (Std.OrientedCmp.gt_iff_lt (cmp := rowCmp)).mpr (degree_lt h)

/-- In equally long sorted rows, an exclusive member smaller than every
exclusive member of the other row determines the lexicographic comparison. -/
theorem lex_lt {a b : List (Fin n)} {v : Fin n}
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·))
    (hlen : a.length = b.length) (hv : v ∈ a) (hn : v ∉ b)
    (hmin : ∀ w ∈ b, w ∉ a → v < w) : compare a b = .lt := by
  induction a generalizing b with
  | nil => simp at hv
  | cons x xs ih =>
    cases b with
    | nil => simp at hlen
    | cons y ys =>
      obtain ⟨hax, has⟩ := List.pairwise_cons.mp ha
      obtain ⟨hby, hbs⟩ := List.pairwise_cons.mp hb
      by_cases hxy : x = y
      · subst y
        have hvx : v ≠ x := by intro h; exact hn (by simp [h])
        have hv' : v ∈ xs := (List.mem_cons.mp hv).resolve_left hvx
        have hn' : v ∉ ys := fun h => hn (List.mem_cons_of_mem x h)
        have hm : ∀ w ∈ ys, w ∉ xs → v < w := by
          intro w hw hnot
          apply hmin w (List.mem_cons_of_mem x hw)
          intro h
          rcases List.mem_cons.mp h with rfl | h
          · have := hby w hw
            exact (Fin.lt_irrefl w) this
          · exact hnot h
        simpa only [List.compare_cons_cons, compare_self, Ordering.eq_then] using
          ih has hbs (by simpa using hlen) hv' hn' hm
      · by_cases hlt : x < y
        · have hc : compare x y = .lt :=
            (compareOfLessAndEq_eq_lt (x := x.val) (y := y.val)).mpr hlt
          simp [List.compare_cons_cons, hc]
        · have hyx : y < x := by omega
          have hy : y ∉ x :: xs := by
            intro h
            rcases List.mem_cons.mp h with h | h
            · exact hxy h.symm
            · have := hax y h
              omega
          have hvy := hmin y (by simp) hy
          rcases List.mem_cons.mp hv with rfl | hv
          · omega
          · have := hax v hv
            omega

/-- Sparse nauty prefers the row containing the first differing vertex
when both degrees agree. -/
theorem row_gt {a b : List (Fin n)} {v : Fin n}
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·))
    (hlen : a.length = b.length) (hv : v ∈ a) (hn : v ∉ b)
    (hmin : ∀ w ∈ b, w ∉ a → v < w) : rowCmp a b = .gt := by
  have h := lex_lt ha hb hlen hv hn hmin
  have hr : compare b a = .gt := (OrientedCmp.gt_iff_lt).mpr h
  change (compare b.length a.length).then (compare b a) = .gt
  simp [hlen, hr]

theorem row_lt {a b : List (Fin n)} {v : Fin n}
    (ha : a.Pairwise (· < ·)) (hb : b.Pairwise (· < ·))
    (hlen : a.length = b.length) (hv : v ∈ b) (hn : v ∉ a)
    (hmin : ∀ w ∈ a, w ∉ b → v < w) : rowCmp a b = .lt := by
  exact (OrientedCmp.gt_iff_lt (cmp := rowCmp)).mp
    (row_gt hb ha hlen.symm hv hn hmin)

end Hex.GraphIso.Nauty.Sparse.RowOrder
