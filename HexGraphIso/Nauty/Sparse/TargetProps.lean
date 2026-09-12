/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CellList

public section

namespace Hex.GraphIso.Nauty.Sparse.Target

/-- The nontrivial-cell list is strictly increasing, so its order also fixes ties. -/
theorem ordered (ptn : Array Nat) (level n : Nat) :
    (nontrivial (cells ptn level n)).Pairwise (· < ·) := by
  apply List.pairwise_map.mpr
  apply ((cells_pairwise (ptn := ptn) (level := level) (nn := n)).filter
    (fun p => p.1 < p.2)).imp_of_mem
  intro p q hp hq hpq
  have hle := cells_le p (List.mem_filter.mp hp).1
  omega

theorem nodup (ptn : Array Nat) (level n : Nat) :
    (nontrivial (cells ptn level n)).Nodup :=
  (ordered ptn level n).imp (fun h => Nat.ne_of_lt h)

theorem mem_iff {cs : List (Nat × Nat)} {a : Nat} :
    a ∈ nontrivial cs ↔ ∃ b, (a, b) ∈ cs ∧ a < b := by
  simp only [nontrivial, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hc, hlt⟩, rfl⟩
    exact ⟨y, hc, hlt⟩
  · rintro ⟨b, hc, hlt⟩
    exact ⟨(a, b), ⟨hc, hlt⟩, rfl⟩

theorem bound {ptn : Array Nat} {n level a : Nat}
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (ha : a ∈ nontrivial (cells ptn level n)) : a < n := by
  obtain ⟨b, hc, hab⟩ := mem_iff.mp ha
  have hb := cells_bound (nn := n) (by omega) (by simpa [hs] using hend) (a, b) hc
  omega

/-- Every bounded maximal cell is one of the cells enumerated by the walk. -/
theorem cell_mem {ptn : Array Nat} {n level a len : Nat}
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hc : IsCell ptn level a len) (hb : a + len ≤ n) :
    (a, a + len - 1) ∈ cells ptn level n := by
  have hp := hc.1
  obtain ⟨p, hm, hlo, hhi⟩ := cells_cover (ptn := ptn) (level := level) a (by omega : a < n)
  have hpc := cells_isCell (nn := n) (by omega) (by simpa [hs] using hend) p hm
  have hg := cells_le p hm
  have hd := isCell_disjoint_or_eq hc hpc
  rcases hd with hd | hd | ⟨he, hl⟩
  · omega
  · omega
  · have hpair : p = (a, a + len - 1) := Prod.ext (by omega) (by omega)
    rwa [hpair] at hm

/-- Every nonsentinel vertex index is an enumerated nontrivial cell start. -/
theorem index_mem {lab ptn starts ends : Array Nat} {n level i : Nat}
    (h : Index.Valid n lab ptn level starts ends) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hi : i < n) (hne : starts[lab[i]!]! ≠ n) :
    starts[lab[i]!]! ∈ nontrivial (cells ptn level n) := by
  obtain ⟨hc, hlt, hb, hlo, hhi⟩ := h.nontrivial hs hend hi hne
  apply mem_iff.mpr
  refine ⟨ends[starts[lab[i]!]!]!, ?_, hlt⟩
  have hm := cell_mem hs hend hc (by omega)
  simpa only [show starts[lab[i]!]! + (ends[starts[lab[i]!]!]! + 1 - starts[lab[i]!]!) - 1 =
    ends[starts[lab[i]!]!]! by omega] using hm

/-- A checked labelling makes every native vertex lookup a cell start or the
singleton sentinel; the count loops need no stronger scratch hypothesis. -/
theorem vertex_index {lab ptn starts ends : Array Nat} {n level : Nat}
    (h : Index.Valid n lab ptn level starts ends) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (v : Fin n) : starts[v.val]! = n ∨ starts[v.val]! ∈ nontrivial (cells ptn level n) := by
  by_cases he : starts[v.val]! = n
  · exact Or.inl he
  · right
    have hv : lab[(l.toPerm.get v).val]! = v.val := by
      rw [← Label.ofArray?_get hl _ (l.toPerm.get v).isLt, Label.get_toPerm_get]
    have hm := index_mem h hs hend (l.toPerm.get v).isLt (by simpa [hv] using he)
    simpa only [hv] using hm

end Hex.GraphIso.Nauty.Sparse.Target
