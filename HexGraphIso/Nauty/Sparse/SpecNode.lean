/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SpecBound
public import HexGraphIso.Nauty.Sparse.RefineTransport
import all HexGraphIso.Nauty.Equitable.Step

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Entry invariants of the unpruned sparse tree, including the certificate
that supplies equitability after the actual refinement. -/
structure SpecNode (G : Hex.SparseGraph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) : Prop where
  label : lab.toList.Perm (List.range n)
  node : NodeOk n level lab ptn active
  count : numcells = bcount ptn level n
  depth : level ≤ numcells
  cert : CertInv (Graph.context G) level
    { lab, ptn, active, numcells, hint := 0, maxpos := 0, longcode := numcells }

namespace SpecNode

variable {G : Hex.SparseGraph n} {level numcells : Nat} {lab ptn : Array Nat} {active : VSet n}

/-- Executed sparse refinement preserves the tree's entry invariants and
returns an equitable partition, with no equitability premise. -/
theorem refined (h : SpecNode G level lab ptn active numcells) :
    let r := refine (.ofGraph G) level lab ptn active numcells
    SpecNode G level r.lab r.ptn r.active r.numcells ∧
      Equitable (Graph.context G) level r.lab r.ptn := by
  have hb := (Scratch.fresh_valid n lab ptn level).toBounded
  have hend : ptn[n - 1]! ≤ level := by simpa only [h.node.ptnSize] using h.node.ptnEnd
  have hr := refine_node G level lab ptn active numcells h.label h.node h.count
  have hc := refineWith_cert G level lab ptn active numcells (.fresh n)
    h.label h.node.ptnSize hend h.node.starts hb h.cert
  have he := refineWith_equitable G level lab ptn active numcells (.fresh n)
    h.label h.node.ptnSize hend h.node.starts hb h.count h.cert
  exact ⟨⟨hr.1, hr.2.1, hr.2.2.1, Nat.le_trans h.depth hr.2.2.2, hc⟩, he⟩

/-- Every target member supplies the complete next-node invariant through
the actual rotation and singleton activation. -/
theorem child (h : SpecNode G level lab ptn active numcells)
    (heq : Equitable (Graph.context G) level lab ptn) {tc len o : Nat}
    (hc : IsCell ptn level tc len) (hb : tc + len ≤ n) (hn : 1 < len) (ho : o < len) :
    let c := breakout n lab ptn (level + 1) tc lab[tc + o]!
    SpecNode G (level + 1) c.1 c.2.1 c.2.2 (numcells + 1) := by
  have hr := breakout_node h.label h.node h.count h.depth hc hb hn ho
  have hl : level ≤ n := by
    have := h.depth
    have := h.count
    have := bcount_le ptn level n
    omega
  have hweak : ∀ q, q < n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]! := by
    intro q _
    rcases h.node.vals q with hh | hh
    · exact Or.inl hh
    · exact Or.inr (by omega)
  have hmem := mem_cells_of_isCell (nn := n) (Nat.le_of_eq h.node.ptnSize.symm)
    h.node.ptnEnd hc (by omega) (by rw [h.node.ptnSize]; exact hb)
  have hcert := certInv_breakout h.node.labSize h.node.ptnSize h.node.ptnEnd hweak
    (fun i j hi hj he => perm_injective h.label hi hj he) hmem (by omega)
    (by omega : o ≤ tc + len - 1 - tc) heq (numcells := numcells)
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2, hcert⟩

/-- Actual stable colour buckets establish every nonempty root invariant. -/
theorem initial (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    SpecNode G.graph 1 p.1 (initPtn n (n + 2) p.2) (initActive n p.2) p.2.length := by
  have h := initial_nodeOk G hn
  refine ⟨initialPartition_perm G, h, (initial_count G).symm, ?_, initial_cert G hn⟩
  have hp := bcount_pos_of_boundary (ptn := initPtn n (n + 2)
    (initialPartitionWith n k G.coloring.cells.toArray Fin.val).2) (level := 1)
    (nn := n) (q := n - 1) (by omega) (by simpa only [h.ptnSize] using h.ptnEnd)
  have hc := initial_count G
  omega

end SpecNode
end Hex.GraphIso.Nauty.Sparse
