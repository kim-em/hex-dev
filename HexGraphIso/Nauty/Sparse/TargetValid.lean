/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Descent
public import HexGraphIso.Nauty.Sparse.TargetDispatch
public import HexGraphIso.LabelArray

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- A valid partition with fewer than `n` cells has a nontrivial cell. -/
theorem Target.nonempty {n level : Nat} {ptn : Array Nat} (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hc : bcount ptn level n < n) :
    Target.nontrivial (cells ptn level n) ≠ [] := by
  intro he
  have hd : discreteAt ptn level n = true := by
    apply List.all_eq_true.mpr
    intro c hmem
    have hle := cells_le c hmem
    have hn : ¬ c.1 < c.2 := by
      intro hlt
      have hm := Target.mem_iff.mpr ⟨c.2, hmem, hlt⟩
      rw [he] at hm
      exact List.not_mem_nil hm
    exact beq_iff_eq.mpr (by omega)
  have hh := (discreteAt_iff_bcount hs.symm (by simpa only [hs] using hend)).mp hd
  omega

/-- Fresh target selection needs no caller-supplied label parser success or
cache: both are derived from the node's permutation and partition facts. -/
theorem targetcell_nontrivial (G : Hex.SparseGraph n) (lab ptn : Array Nat)
    (level tcLevel : Nat) (hint : Int) (hp : lab.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level) (hc : bcount ptn level n < n) :
    targetcell (.ofGraph G) lab ptn level tcLevel hint ∈ Target.nontrivial (cells ptn level n) := by
  obtain ⟨l, hl⟩ := Label.ofArray?_exists hp
  let idx := indexCells n lab ptn level (.replicate n n) (.replicate n 0)
  let scratch : Scratch := { Scratch.fresh n with cellstart := idx.1, cellend := idx.2 }
  have hi := indexCells_valid lab ptn (.replicate n n) (.replicate n 0) level hs hend
    (fun i hi => perm_bound hp hi) (fun i j hi hj he => perm_injective hp hi hj he)
    (by simp) (by simp)
  exact targetcell_mem G lab ptn level tcLevel hint scratch l hl hs hend hi
    (Target.nonempty hs hend hc)

/-- The fresh target's returned size is the length of a bounded nontrivial
partition cell, including valid hints and both depth-cutoff branches. -/
theorem maketargetcell_valid (G : Hex.SparseGraph n) (lab ptn : Array Nat)
    (level tcLevel : Nat) (hint : Int) (hp : lab.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level) (hc : bcount ptn level n < n) :
    let t := maketargetcell (.ofGraph G) lab ptn level tcLevel hint
    IsCell ptn level t.1 t.2.2 ∧ 1 < t.2.2 ∧ t.1 + t.2.2 ≤ n := by
  have hm := targetcell_nontrivial G lab ptn level tcLevel hint hp hs hend hc
  have hb := Target.bound hs hend hm
  have ho := Target.open_of_mem hs hend hm
  let a := targetcell (.ofGraph G) lab ptn level tcLevel hint
  have hend' : ptn[ptn.size - 1]! ≤ level := by simpa only [hs] using hend
  have hcell := isCell_cellEnd (ptn := ptn) (level := level) (a := a) (by omega) ho.2 hend'
  have he := cellEnd_lt (ptn := ptn) (level := level) (i := a) (by omega) hend'
  have hg : a ≤ cellEnd ptn level a := cellEnd_ge
  have hn : a < cellEnd ptn level a := by
    have hf := hcell.2.2.2
    have hh := ho.1
    change ptn[a]! > level at hh
    by_cases h : a = cellEnd ptn level a
    · simp only [← h, Nat.add_sub_cancel_left, Nat.add_sub_cancel] at hf
      omega
    · omega
  dsimp only [maketargetcell]
  change IsCell ptn level a (cellEnd ptn level a - a + 1) ∧
    1 < cellEnd ptn level a - a + 1 ∧ a + (cellEnd ptn level a - a + 1) ≤ n
  exact ⟨by simpa only [show cellEnd ptn level a + 1 - a = cellEnd ptn level a - a + 1 by omega] using hcell,
    by omega, by omega⟩

/-- Every admissible scratch state yields the same bounded nontrivial target
as the fresh selector, without additional cache or parsing assumptions. -/
theorem maketargetCached_validCell (G : Hex.SparseGraph n) (lab ptn : Array Nat)
    (level tcLevel : Nat) (hint : Int) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level) (hv : Scratch.Valid n lab ptn level scratch)
    (hc : bcount ptn level n < n) :
    let t := maketargetCached (.ofGraph G) lab ptn level tcLevel hint scratch
    IsCell ptn level t.1 t.2.2.1 ∧ 1 < t.2.2.1 ∧ t.1 + t.2.2.1 ≤ n := by
  obtain ⟨l, hl⟩ := Label.ofArray?_exists hp
  have he := maketargetCached_eq G lab ptn level tcLevel hint scratch l hl hs hend hv
    (Target.nonempty hs hend hc)
  have ht := maketargetcell_valid G lab ptn level tcLevel hint hp hs hend hc
  rw [← he] at ht
  exact ht

end Hex.GraphIso.Nauty.Sparse
