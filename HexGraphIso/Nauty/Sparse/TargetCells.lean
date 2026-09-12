/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TargetTransport

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Target selection commutes simultaneously with graph renaming and
permutations within corresponding equitable cells. Valid index witnesses
are constructed, and the full position, vertex set and size are transported. -/
theorem maketargetcell_equiv (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ u v, H.adj (p.get u) (p.get v) = G.adj u v)
    (lab out ptn : Array Nat) (level tcLevel : Nat) (hint : Int)
    (hp : lab.toList.Perm (List.range n)) (hq : out.toList.Perm (List.range n))
    (hs : ptn.size = n) (hend : ptn[n - 1]! ≤ level)
    (heq : Equitable (Graph.context H) level out ptn)
    (hperm : cellsPerm ptn level out (lab.map (renamingOf p).toFun))
    (hc : bcount ptn level n < n) :
    let a := maketargetcell (.ofGraph G) lab ptn level tcLevel hint
    maketargetcell (.ofGraph H) out ptn level tcLevel hint =
      (a.1, a.2.1.image (renamingOf p), a.2.2) := by
  obtain ⟨s, hi⟩ := Index.exists_valid hq hs hend
  obtain ⟨t, hj⟩ := Index.exists_valid (perm_map hp p) hs hend
  exact (maketargetcell_perm H out (lab.map (renamingOf p).toFun) ptn level tcLevel hint
    s t hq (perm_map hp p) hs hend hi hj heq hperm hc).trans
    (maketargetcell_map G H p hiso lab ptn level tcLevel hint hp hs hend hc)

end Hex.GraphIso.Nauty.Sparse
