/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstStore
public import HexGraphIso.Sparse.Ops

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The actual sparse production root always returns a valid installed
canonical prefix. Its initial blank allocation and first leaf supply every
premise, including the zero-colour empty graph. -/
theorem runState_store (G : GraphIso.Sparse.Colored n k) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    Store G.graph (runState (.ofGraph G.graph) p.1 p.2).2 := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst n
    obtain ⟨l, hl⟩ := canonlab_parse G
    exact ⟨l, hl, blank_prefix G.graph l⟩
  · obtain ⟨last, leaf, path, _, _⟩ := initial_path G hn
    dsimp only
    rw [runState, ite_eq_right (by simpa using Nat.ne_of_gt hn)]
    exact firstPath_store hn path (by omega) (NodeInv.initial G hn) rfl

/-- Finishing fills the remaining rows without changing the checked label. -/
theorem runColored_store (G : GraphIso.Sparse.Colored n k) : Store G.graph (runColored G) :=
  (runState_store G).finish

/-- The complete raw canonical store represents the native public label's
relabelling. Raw row order is retained; normalized row equality is semantic. -/
theorem canong_prefix (G : GraphIso.Sparse.Colored n k) :
    (runColored G).canong.toRows.Prefix (G.graph.relabel (GraphIso.Sparse.label G).perm) n := by
  obtain ⟨c, hc, hp⟩ := runColored_store G
  have he : c = GraphIso.Sparse.label G := Option.some.inj (hc.symm.trans (GraphIso.Sparse.label_parse G))
  subst c
  exact hp

theorem canong_canon (G : GraphIso.Sparse.Colored n k) :
    (runColored G).canong.toRows.Prefix (GraphIso.Sparse.canon G).graph n := by
  rw [← GraphIso.Sparse.relabel_label]
  exact canong_prefix G

/-- Each returned working row has exactly the public canonical graph's
neighbours, including the executable's retained neighbour order. -/
theorem canong_rows (G : GraphIso.Sparse.Colored n k) (i : Fin n) :
    (Hex.SparseGraph.row (runColored G).canong.offsets (runColored G).canong.neighbors i.val).toList.Perm
      (((GraphIso.Sparse.canon G).graph.nbrs i).toList.map Fin.val) :=
  (canong_canon G).rows_perm i i.isLt

end Hex.GraphIso.Nauty.Sparse
