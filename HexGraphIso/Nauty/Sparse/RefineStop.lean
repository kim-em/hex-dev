/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineVisit
public import HexGraphIso.Nauty.Sparse.RefineFuel
public import HexGraphIso.Nauty.SmallCell.Transitive
public import HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Distinct active cell starts inject into the partition's cells. -/
theorem active_card (active : VSet n) (ptn : Array Nat) (level : Nat)
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level) :
    active.card ≤ bcount ptn level n := by
  let starts := (List.range n).filter active.mem
  let pairs := starts.map fun v => (v, cellEnd ptn level v)
  have hn : pairs.Nodup := by
    apply List.pairwise_map.mpr
    apply (List.filter_sublist.nodup List.nodup_range).imp
    intro a b hab he
    exact hab (congrArg Prod.fst he)
  have hsub : pairs ⊆ cells ptn level n := by
    intro c hc
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
    obtain ⟨hv, hm⟩ := List.mem_filter.mp hv
    have hv := List.mem_range.mp hv
    have hc := isCell_cellEnd (ptn := ptn) (a := v) (by omega) (ha v hm)
      (by simpa only [hs] using hend)
    have he := cellEnd_lt (ptn := ptn) (level := level) (i := v) (by omega)
      (by simpa only [hs] using hend)
    have hg : v ≤ cellEnd ptn level v := cellEnd_ge
    have hh := mem_cells_of_isCell (nn := n) (by omega)
      (by simpa only [hs] using hend) hc hv (by omega)
    simpa only [show v + (cellEnd ptn level v + 1 - v) - 1 = cellEnd ptn level v by omega] using hh
  have hh := hn.length_le_of_subset hsub
  rw [cells_length_eq_bcount hs (by simpa only [hs] using hend)] at hh
  simpa only [pairs, starts, List.length_map, VSet.card_eq_countBelow, VSet.countBelow,
    List.countP_eq_length_filter] using hh

/-- At every well-formed node, the executed bounded loop reaches an empty
active queue or a discrete partition; its fuel cannot conceal pending work. -/
theorem refineWith_stopped (G : Hex.SparseGraph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n scratch) (hc : numcells = bcount ptn level n) :
    let t := refineWith (.ofGraph G) level lab ptn active numcells scratch
    t.queue.isEmpty = true ∨ discreteAt t.ptn level n = true := by
  have ht := refineWith_state G level lab ptn active numcells scratch hp hs hend ha hb
  have hcount := refineWith_count G level lab ptn active numcells scratch hp hs hend ha hb hc
  have hstop := refineWith_saturated (.ofGraph G) level lab ptn active numcells scratch
    (by rw [hc]; exact active_card active ptn level hs hend ha)
  rcases hstop with hq | hn
  · exact Or.inl hq
  · right
    apply (discreteAt_iff_bcount ht.2.1.symm ?_).mpr
    · have := bcount_le (refineWith (.ofGraph G) level lab ptn active numcells scratch).ptn level n
      omega
    · rw [ht.2.1, ht.2.2.1.closed _ hend]
      exact hend

end Hex.GraphIso.Nauty.Sparse
