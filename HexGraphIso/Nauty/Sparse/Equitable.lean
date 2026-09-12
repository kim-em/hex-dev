/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.RefineCert
public import HexGraphIso.Nauty.Sparse.RefineStop
public import HexGraphIso.Nauty.Sparse.Root

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- An exhausted sparse queue has no active splitter left. -/
theorem ActiveQueue.empty {active : VSet n} {queue : Array Nat}
    (h : ActiveQueue active queue) (he : queue.isEmpty = true) : active = VSet.empty := by
  have he : queue = #[] := Array.isEmpty_iff.mp he
  apply VSet.eq_empty_iff.mpr
  intro v
  have hm := h.mem v
  simp only [he, Array.toList_empty, List.not_mem_nil, false_iff] at hm
  exact Bool.eq_false_iff.mpr hm

/-- With an accurate cell count the actual bounded sparse refinement returns
an equitable partition. Both discrete and exhausted-queue exits are covered. -/
theorem refineWith_equitable (G : Hex.SparseGraph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (hp : lab.toList.Perm (List.range n)) (hs : ptn.size = n)
    (hend : ptn[n - 1]! ≤ level)
    (ha : ∀ v, active.mem v = true → v = 0 ∨ ptn[v - 1]! ≤ level)
    (hb : Scratch.Bounded n scratch) (hc : numcells = bcount ptn level n)
    (hinv : CertInv (Graph.context G) level
      { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }) :
    let t := refineWith (.ofGraph G) level lab ptn active numcells scratch
    Equitable (Graph.context G) level t.lab t.ptn := by
  have ht := refineWith_state G level lab ptn active numcells scratch hp hs hend ha hb
  have hcert := refineWith_cert G level lab ptn active numcells scratch hp hs hend ha hb hinv
  rcases refineWith_stopped G level lab ptn active numcells scratch hp hs hend ha hb hc with he | hd
  · exact equitable_of_certInv_exit hcert (ht.2.2.2.2.1.set.empty he)
  · apply equitable_of_singletons
    intro c hmem
    have hh := (List.all_eq_true.mp hd) c hmem
    exact (beq_iff_eq.mp hh).symm

/-- The actual sparse root supplies its certificate without a semantic
assumption: every ordered colour cell is initially active. -/
theorem initial_cert (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    CertInv (Graph.context G.graph) 1
      { lab := p.1, ptn := initPtn n (n + 2) p.2, active := initActive n p.2
        numcells := p.2.length, hint := 0, maxpos := 0, longcode := p.2.length } :=
  certInv_of_activeCells (initial_cells_active G hn)

/-- Root refinement is equitable for every nonempty sparse coloured graph. -/
theorem initial_equitable (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    let s := initial (.ofGraph G.graph) p.1 p.2
    let t := refineWith (.ofGraph G.graph) 1 s.lab s.ptn s.active p.2.length s.canong.scratch
    Equitable (Graph.context G.graph) 1 t.lab t.ptn := by
  have h := initial_nodeOk G hn
  dsimp only [initial]
  apply refineWith_equitable
  · exact initialPartition_perm G
  · exact h.ptnSize
  · simpa only [h.ptnSize] using h.ptnEnd
  · exact h.starts
  · exact (Scratch.fresh_valid n #[] #[] 1).toBounded
  · exact (initial_count G).symm
  · exact initial_cert G hn

end Hex.GraphIso.Nauty.Sparse
