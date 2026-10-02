/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Invariant.Refine
public import HexGraphIso.Sparse.Iso

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Every parsed reachable label has the same ordered position colours. -/
theorem label_colors (G : GraphIso.Sparse.Colored n k) {lab : Array Nat} {l : Label n}
    (hl : Label.ofArray? n lab = some l) (hr : CellsReach G.toDense lab) (i : Fin n) :
    (G.coloring.cells[l.get i]).val = (sortedColorSeq G.toDense)[i.val]! := by
  obtain ⟨hb, he⟩ := achieved_position_colors hr i.val i.isLt
  have hv : (⟨lab[i.val]!, hb⟩ : Fin n) = l.get i :=
    Fin.ext (Label.ofArray?_get hl i.val i.isLt).symm
  change (G.toDense.coloring.cells.get ⟨lab[i.val]!, hb⟩).val = _ at he
  rw [hv] at he
  simpa only [GraphIso.Sparse.Colored.toDense, Hex.Vector.get_eq_getElem] using he

/-- Scattering between two reachable labels preserves the original
ordered colours, independently of the adjacency proof. -/
theorem label_pair_colors (G : GraphIso.Sparse.Colored n k) {lab ref : Array Nat} {l c : Label n}
    (hl : Label.ofArray? n lab = some l) (hc : Label.ofArray? n ref = some c)
    (hrl : CellsReach G.toDense lab) (hrc : CellsReach G.toDense ref) (v : Fin n) :
    G.coloring.cells[(l.perm.comp c.perm.inv).get v] = G.coloring.cells[v] := by
  have he := (label_colors G hl hrl (c.perm.inv.get v)).trans
    (label_colors G hc hrc (c.perm.inv.get v)).symm
  apply Fin.ext
  simpa only [Label.get, Perm.get_inv_get, Perm.get_comp] using he

/-- Equal native leaf graphs and reachable labels give a full coloured
automorphism, with the same direction as the workspace scatter. -/
theorem label_pair_iso (G : GraphIso.Sparse.Colored n k) {lab ref : Array Nat} {l c : Label n}
    (hl : Label.ofArray? n lab = some l) (hc : Label.ofArray? n ref = some c)
    (hrl : CellsReach G.toDense lab) (hrc : CellsReach G.toDense ref)
    (he : G.graph.relabel l.perm = G.graph.relabel c.perm) :
    GraphIso.Sparse.IsIso G G (l.perm.comp c.perm.inv) := by
  apply GraphIso.Sparse.IsIso.mk (label_pair_colors G hl hc hrl hrc)
  intro i j
  have ha := congrArg (fun H : Hex.SparseGraph n => H.adj (c.perm.inv.get i) (c.perm.inv.get j)) he
  simpa only [Hex.SparseGraph.adj_relabel, Perm.get_inv_get, Perm.get_comp] using ha

end Hex.GraphIso.Nauty.Sparse
