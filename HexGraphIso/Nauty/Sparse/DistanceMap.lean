/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.BfsRun
public import HexGraphIso.Nauty.Sparse.ContextMap

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Native BFS distances commute with an arbitrary supplied isomorphism,
including unreachable vertices and changes to native traversal order. -/
theorem distvals_map (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v) (root v : Fin n) :
    (distvals (.ofGraph H) (p.get root).val)[(p.get v).val]! =
      (distvals (.ofGraph G) root.val)[v.val]! := by
  have he : H = G.relabel p.inv := by
    apply Hex.SparseGraph.ext
    intro u v
    simpa using hiso (p.inv.get u) (p.inv.get v)
  rw [he]
  simpa using distvals_relabel G p.inv (p.get root) (p.get v)

end Hex.GraphIso.Nauty.Sparse
