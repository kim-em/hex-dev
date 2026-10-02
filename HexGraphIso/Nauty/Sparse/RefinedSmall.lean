/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PathTransport
public import HexGraphIso.Nauty.Sparse.Renaming
import all HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty.Sparse.RefineSt.Ready

/-- The partition interpretation of a native refined state satisfies the
invariants used by the shared cell-stabilizer and pruning proofs. -/
theorem iter {G : Hex.SparseGraph n} {level : Nat} {s : RefineSt n}
    (h : RefineSt.Ready G level s) : IterOk (Graph.context G) level s.toPartition :=
  ⟨⟨h.spec.node.labSize, h.spec.node.labOk, h.spec.node.ptnSize, h.spec.node.ptnEnd⟩,
    fun _ _ hi hj he => perm_injective h.spec.label hi hj he,
    fun q _ => h.spec.node.vals q,
    Nat.le_trans h.spec.depth (by rw [h.spec.count]; exact bcount_le _ _ _)⟩

/-- The small-cell stabilizer theorem applies to a literal cached-refinement
node through its proved partition interpretation. -/
theorem automorphism {G : Hex.SparseGraph n} {level : Nat} {s : RefineSt n}
    (h : RefineSt.Ready G level s) (hshape : NodeShape n level s.ptn)
    {tc len a b : Nat} (hc : IsCell s.ptn level tc len) (hb : tc + len ≤ n)
    (hn : 1 < len) (ha : a < len) (hb' : b < len) (hab : a ≠ b) :
    ∃ p : Perm n, (∀ i j, G.adj (p.get i) (p.get j) = G.adj i j) ∧
      cellsPerm s.ptn level s.lab (s.lab.map (renamingOf p).toFun) ∧
      s.lab[tc + b]! = renamingOf p s.lab[tc + a]! := by
  have hs : SubtreeOk (Graph.context G) level s.toPartition :=
    ⟨h.iter, h.equitable, h.spec.count.symm, hshape⟩
  have hsymm : ∀ u v, u < n → v < n →
      ((Graph.context G).g[u]!).mem v = ((Graph.context G).g[v]!).mem u := by
    intro u v hu hv
    rw [Graph.context_mem G ⟨u, hu⟩ ⟨v, hv⟩, Graph.context_mem G ⟨v, hv⟩ ⟨u, hu⟩]
    exact G.adj_symm _ _
  have hloop : ∀ v, v < n → ((Graph.context G).g[v]!).mem v = false := by
    intro v hv
    rw [Graph.context_mem G ⟨v, hv⟩ ⟨v, hv⟩]
    exact G.adj_self _
  have hmem := mem_cells_of_isCell (nn := n) (Nat.le_of_eq h.spec.node.ptnSize.symm)
    h.spec.node.ptnEnd hc (by omega) (by rw [h.spec.node.ptnSize]; exact hb)
  obtain ⟨σ, hg, hp, hm⟩ := stabilizer_transitive hs (by simp [Graph.context]) hsymm hloop
    hmem (by omega) (by omega : a ≤ tc + len - 1 - tc) (by omega : b ≤ tc + len - 1 - tc) hab
  have hv : ∀ i, i < s.lab.size → s.lab[i]! < n := h.spec.node.labOk
  have hval : s.lab[tc + a]! < n := perm_bound h.spec.label (by omega)
  refine ⟨σ.toPerm, Graph.context_iso G G σ hg, ?_, ?_⟩
  · rw [σ.map_toPerm s.lab hv]
    exact hp.cells
  · rw [renamingOf_lt σ.toPerm hval, Renaming.get_toPerm]
    exact hm

end Hex.GraphIso.Nauty.Sparse.RefineSt.Ready
