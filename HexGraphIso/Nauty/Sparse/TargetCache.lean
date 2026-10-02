/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetMaximum

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Two admissible caches agree on every vertex index and every cell endpoint
that the executable reads. Unused endpoint entries may differ. -/
theorem Index.Valid.agree {lab ptn starts ends starts' ends' : Array Nat} {n level : Nat}
    (h : Index.Valid n lab ptn level starts ends)
    (h' : Index.Valid n lab ptn level starts' ends')
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (l : Label n) (hl : Label.ofArray? n lab = some l) :
    starts = starts' ∧ ∀ a, a < n → (a = 0 ∨ ptn[a - 1]! ≤ level) → ends[a]! = ends'[a]! := by
  refine ⟨?_, fun a ha hb => (h.end_eq hs hend ha hb).trans (h'.end_eq hs hend ha hb).symm⟩
  have position (i : Nat) (hi : i < n) : starts[lab[i]!]! = starts'[lab[i]!]! := by
    obtain ⟨a, len, hc, hb, hlo, hhi⟩ := Index.cover hs hend hi
    rw [h.starts_eq a len hc hb (by omega) i hlo hhi,
      h'.starts_eq a len hc hb (by omega) i hlo hhi]
  apply Array.ext (h.starts_size.trans h'.starts_size.symm)
  intro v hv hv'
  have hb : v < n := by rw [h.starts_size] at hv; exact hv
  have hval : lab[(l.toPerm.get ⟨v, hb⟩).val]! = v := by
    rw [← Label.ofArray?_get hl _ (l.toPerm.get ⟨v, hb⟩).isLt, Label.get_toPerm_get]
  have he := position _ (l.toPerm.get ⟨v, hb⟩).isLt
  rw [hval, getElem!_pos _ v hv, getElem!_pos _ v hv'] at he
  exact he

/-- The executed cached selector returns the first maximal partial-join cell. -/
theorem bestcellCached_max (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat)
    (s : Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hidx : Index.Valid n lab ptn level s.cellstart s.cellend) (hsize : s.hits.size = n)
    (hne : Target.nontrivial (cells ptn level n) ≠ []) :
    Target.FirstMax (Target.score (.ofGraph G) lab s (Target.nontrivial (cells ptn level n)))
      (Target.nontrivial (cells ptn level n)) (bestcellCached (.ofGraph G) lab s).1 := by
  rw [bestcellCached_spec G lab ptn level s l hl hptn hend hidx hsize]
  exact Target.best_max _ _ n hne

/-- Initial hit values and unused cache entries do not affect the selected
cell. Both admissible caches compute the same complete join-score sequence. -/
theorem bestcellCached_congr (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat)
    (s t : Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hs : Index.Valid n lab ptn level s.cellstart s.cellend) (hss : s.hits.size = n)
    (ht : Index.Valid n lab ptn level t.cellstart t.cellend) (hts : t.hits.size = n) :
    (bestcellCached (.ofGraph G) lab s).1 = (bestcellCached (.ofGraph G) lab t).1 := by
  obtain ⟨hstarts, hends⟩ := hs.agree ht hptn hend l hl
  have hrows (first : Nat) : Target.row (.ofGraph G) lab s first = Target.row (.ofGraph G) lab t first := by
    simp only [Target.row, hstarts]
  have hscore : Target.score (.ofGraph G) lab s (Target.nontrivial (cells ptn level n)) =
      Target.score (.ofGraph G) lab t (Target.nontrivial (cells ptn level n)) := by
    funext first
    apply List.countP_congr
    intro k hk
    obtain ⟨b, hmem, hlt⟩ := Target.mem_iff.mp hk
    have hcell := cells_isCell (nn := n) (by omega) (by simpa [hptn] using hend) (k, b) hmem
    have hk' := Target.bound hptn hend hk
    simp only [Join.qualifies, hrows, hends k hk' hcell.2.1]
  rw [bestcellCached_spec G lab ptn level s l hl hptn hend hs hss,
    bestcellCached_spec G lab ptn level t l hl hptn hend ht hts, hscore]

end Hex.GraphIso.Nauty.Sparse
