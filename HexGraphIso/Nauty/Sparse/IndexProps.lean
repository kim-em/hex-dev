/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.IndexRun

public section

namespace Hex.GraphIso.Nauty.Sparse.Index

/-- Every position of a closed partition belongs to a bounded maximal cell. -/
theorem cover {ptn : Array Nat} {n level i : Nat}
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level) (hi : i < n) :
    ∃ a len, IsCell ptn level a len ∧ a + len ≤ n ∧ a ≤ i ∧ i < a + len := by
  obtain ⟨p, hp, hlo, hhi⟩ := cells_cover (ptn := ptn) (level := level) i hi
  have hb := cells_bound (nn := n) (by omega) (by simpa [hs] using hend) p hp
  have hc := cells_isCell (nn := n) (by omega) (by simpa [hs] using hend) p hp
  have hg := cells_le p hp
  exact ⟨p.1, p.2 + 1 - p.1, hc, by omega, hlo, by omega⟩

namespace Valid

/-- A valid cache's endpoint agrees with the independent partition walk. -/
theorem end_eq {lab ptn starts ends : Array Nat} {n level a : Nat}
    (h : Valid n lab ptn level starts ends) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (ha : a < n)
    (hstart : a = 0 ∨ ptn[a - 1]! ≤ level) :
    ends[a]! = cellEnd ptn level a := by
  have hb : cellEnd ptn level a < n := by
    simpa [hs] using cellEnd_lt (ptn := ptn) (level := level) (i := a)
      (by omega) (by simpa [hs] using hend)
  have hc := isCell_cellEnd (ptn := ptn) (level := level) (a := a)
    (by omega) hstart (by simpa [hs] using hend)
  have hg : a ≤ cellEnd ptn level a := cellEnd_ge
  have he := h.ends_eq a _ hc (by omega) ha
  omega

/-- Vertex indices are either bounded cell starts or the singleton sentinel. -/
theorem start_le {lab ptn starts ends : Array Nat} {n level i : Nat}
    (h : Valid n lab ptn level starts ends) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hi : i < n) : starts[lab[i]!]! ≤ n := by
  obtain ⟨a, len, hc, hb, hlo, hhi⟩ := cover hs hend hi
  rw [h.starts_eq a len hc hb (by omega) i hlo hhi]
  split <;> omega

/-- A nonsentinel index identifies the complete nontrivial cell containing
that labelled vertex, including all bounds for subsequent array accesses. -/
theorem nontrivial {lab ptn starts ends : Array Nat} {n level i : Nat}
    (h : Valid n lab ptn level starts ends) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hi : i < n) (hne : starts[lab[i]!]! ≠ n) :
    let a := starts[lab[i]!]!
    let b := ends[a]!
    IsCell ptn level a (b + 1 - a) ∧ a < b ∧ b < n ∧ a ≤ i ∧ i ≤ b := by
  obtain ⟨a, len, hc, hb, hlo, hhi⟩ := cover hs hend hi
  have hv := h.starts_eq a len hc hb (by omega) i hlo hhi
  have hpos := hc.1
  have hn : len ≠ 1 := by intro he; simp [he] at hv; exact hne hv
  rw [ite_eq_right hn] at hv
  dsimp only
  rw [hv, h.ends_eq a len hc hb (by omega)]
  refine ⟨?_, by omega, by omega, hlo, by omega⟩
  simpa only [show a + len - 1 + 1 - a = len by omega] using hc

end Valid

end Hex.GraphIso.Nauty.Sparse.Index
