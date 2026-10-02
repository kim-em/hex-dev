/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetFresh

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Fresh and cached sparse best-cell selection agree for any admissible
cache, including arbitrary initial count values and empty partitions. -/
theorem bestcellCached_eq (G : Hex.SparseGraph n) (lab ptn : Array Nat) (level : Nat)
    (s : Scratch) (l : Label n) (hl : Label.ofArray? n lab = some l)
    (hptn : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hidx : Index.Valid n lab ptn level s.cellstart s.cellend) (hsize : s.hits.size = n) :
    (bestcellCached (.ofGraph G) lab s).1 = bestcell (.ofGraph G) lab ptn level := by
  rw [bestcellCached_spec G lab ptn level s l hl hptn hend hidx hsize,
    bestcell_spec G lab ptn level s l hl hptn hend hidx]

namespace Target

theorem open_of_mem {ptn : Array Nat} {n level a : Nat}
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (ha : a ∈ nontrivial (cells ptn level n)) :
    ptn[a]! > level ∧ (a = 0 ∨ ptn[a - 1]! ≤ level) := by
  obtain ⟨b, hm, hlt⟩ := mem_iff.mp ha
  have hc := cells_isCell (nn := n) (by omega) (by simpa [hs] using hend) (a, b) hm
  exact ⟨hc.2.2.1 a (Nat.le_refl _) (by omega), hc.2.1⟩

theorem mem_of_open {ptn : Array Nat} {n level a : Nat}
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level) (ha : a < n)
    (ho : ptn[a]! > level) (hb : a = 0 ∨ ptn[a - 1]! ≤ level) :
    a ∈ nontrivial (cells ptn level n) := by
  have hc := isCell_cellEnd (ptn := ptn) (level := level) (a := a)
    (by omega) hb (by simpa [hs] using hend)
  have he : cellEnd ptn level a < n := by
    simpa [hs] using cellEnd_lt (ptn := ptn) (level := level) (i := a)
      (by omega) (by simpa [hs] using hend)
  have hg : a ≤ cellEnd ptn level a := cellEnd_ge
  have hn : a < cellEnd ptn level a := by
    have hclosed := hc.2.2.2
    by_cases h : a = cellEnd ptn level a
    · simp only [← h, Nat.add_sub_cancel_left, Nat.add_sub_cancel] at hclosed
      omega
    · omega
  apply mem_iff.mpr
  refine ⟨cellEnd ptn level a, ?_, hn⟩
  have hm := cell_mem hs hend hc (by omega)
  simpa only [show a + (cellEnd ptn level a + 1 - a) - 1 = cellEnd ptn level a by omega] using hm

/-- The first open position is the start of the first nontrivial cell. -/
theorem first_mem {ptn : Array Nat} {n level : Nat}
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (hne : nontrivial (cells ptn level n) ≠ []) :
    ((List.range n).find? fun i => ptn[i]! > level).getD 0 ∈ nontrivial (cells ptn level n) := by
  cases hf : (List.range n).find? (fun i => ptn[i]! > level) with
  | none =>
    obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil _ hne
    have ho := (open_of_mem hs hend ha).1
    have hb := bound hs hend ha
    have he := List.find?_eq_none.mp hf a (List.mem_range.mpr hb)
    simp only [decide_eq_true_eq] at he
    omega
  | some a =>
    simp only [Option.getD_some]
    have ha := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    obtain ⟨ho, before, after, heq, hbefore⟩ := List.find?_eq_some_iff_append.mp hf
    simp only [decide_eq_true_eq] at ho
    apply mem_of_open hs hend ha ho
    by_cases he : a = 0
    · exact Or.inl he
    · right
      have hpos := List.eq_of_range'_eq_append_cons (by simpa [List.range_eq_range'] using heq)
      simp only [Nat.one_mul, Nat.zero_add] at hpos
      have ht := congrArg (List.take before.length) heq
      rw [List.take_left, List.take_range, Nat.min_eq_left (by omega), ← hpos] at ht
      have hm : a - 1 ∈ before := by rw [← ht]; simp; omega
      have hp := hbefore (a - 1) hm
      simpa using hp

end Target

end Hex.GraphIso.Nauty.Sparse
