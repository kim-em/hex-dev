/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineStop
public import HexGraphIso.Nauty.Sparse.Root

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Refinement preserves every ancestor cell's vertex multiset, and retains
the literal partition value at each boundary inherited from that ancestor. -/
theorem refineWith_frame (G : Hex.SparseGraph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (h : NodeOk n level lab ptn active)
    (hb : Scratch.Bounded n scratch) (ancestor : Array Nat) (base : Nat)
    (hs : ancestor.size = n) (hend : ancestor[n - 1]! ≤ base)
    (hcoarse : ∀ q : Nat, ancestor[q]! ≤ base → ptn[q]! ≤ level) :
    let t := refineWith (.ofGraph G) level lab ptn active numcells scratch
    cellsPerm ancestor base lab t.lab ∧
    ∀ q : Nat, ancestor[q]! ≤ base → t.ptn[q]! = ptn[q]! := by
  have ht := refineWith_state G level lab ptn active numcells scratch hp h.ptnSize
    (by simpa only [h.ptnSize] using h.ptnEnd) h.starts hb
  have hl : (refineWith (.ofGraph G) level lab ptn active numcells scratch).lab.size = n := by
    simpa using ht.1.length_eq
  refine ⟨?_, fun q hq => ht.2.2.1.closed q (hcoarse q hq)⟩
  exact cellsPerm_coarsen (hs.trans h.ptnSize.symm) (h.labSize.trans h.ptnSize.symm)
    (hl.trans h.ptnSize.symm) (cellsPerm_symm ht.2.2.2.1) h.ptnEnd
    (by simpa only [hs] using hend) hcoarse

/-- Every sparse refinement preserves reachability within the original
ordered colour cells. The dense coloured graph here interprets only the
already proved ordered-partition bridge. -/
theorem refineWith_cellsReach (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (level : Nat) (lab ptn : Array Nat) (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (h : NodeOk n level lab ptn active)
    (hb : Scratch.Bounded n scratch) (hr : CellsReach G.toDense lab)
    (hcoarse : ∀ q : Nat, (initPtn n (n + 2) (Nauty.initialPartition G.toDense).2)[q]! ≤ 1 →
      ptn[q]! ≤ level) :
    CellsReach G.toDense (refineWith (.ofGraph G.graph) level lab ptn active numcells scratch).lab := by
  have ho := Nauty.initial_nodeOk G.toDense hn
  have hf := refineWith_frame G.graph level lab ptn active numcells scratch hp h hb
    (initPtn n (n + 2) (Nauty.initialPartition G.toDense).2) 1 ho.ptnSize
    (by simpa only [ho.ptnSize] using ho.ptnEnd) hcoarse
  exact cellsPerm_trans hr hf.1

/-- The actual production visit preserves the original ordered colour
classes under the ancestor-boundary invariant. -/
theorem visit_cellsReach (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (level numcells : Nat) (s : State n) (hp : s.lab.toList.Perm (List.range n))
    (h : NodeOk n level s.lab s.ptn s.active) (hb : Scratch.Bounded n s.canong.scratch)
    (hr : CellsReach G.toDense s.lab)
    (hcoarse : ∀ q : Nat, (initPtn n (n + 2) (Nauty.initialPartition G.toDense).2)[q]! ≤ 1 →
      s.ptn[q]! ≤ level) :
    CellsReach G.toDense (visit (.ofGraph G.graph) level numcells s).2.2.lab :=
  refineWith_cellsReach G hn level s.lab s.ptn s.active numcells s.canong.scratch hp h hb hr hcoarse

end Hex.GraphIso.Nauty.Sparse
