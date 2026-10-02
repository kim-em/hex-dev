/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ChildTransport
public import HexGraphIso.Nauty.Sparse.TargetCells

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Native target selection depends on an equitable partition's ordered
cells, independently of the label order and the witness's saved active set. -/
theorem RefineSt.Ready.target_perm {G : Hex.SparseGraph n} {level : Nat} {s t : RefineSt n}
    (hs : RefineSt.Ready G level s) (ht : RefineSt.Ready G level t)
    (hp : s.ptn = t.ptn) (he : cellsPerm t.ptn level s.lab t.lab)
    (tcLevel : Nat) (hint : Int) :
    targetcell (.ofGraph G) s.lab s.ptn level tcLevel hint =
      targetcell (.ofGraph G) t.lab t.ptn level tcLevel hint := by
  have hend : t.ptn[n - 1]! ≤ level := by
    simpa only [ht.spec.node.ptnSize] using ht.spec.node.ptnEnd
  obtain ⟨a, ha⟩ := Index.exists_valid hs.spec.label ht.spec.node.ptnSize hend
  obtain ⟨b, hb⟩ := Index.exists_valid ht.spec.label ht.spec.node.ptnSize hend
  have heq : Equitable (Graph.context G) level s.lab t.ptn := by rw [← hp]; exact hs.equitable
  rw [hp]
  exact targetcell_perm G s.lab t.lab t.ptn level tcLevel hint a b hs.spec.label ht.spec.label
    ht.spec.node.ptnSize hend ha hb heq he

/-- Equivalent native equitable nodes choose the same target position.
The rule includes the hint and depth cutoff and needs no cache identity. -/
theorem RefineSt.Equiv.target (G H : Hex.SparseGraph n) (p : Perm n)
    (hiso : ∀ i j, H.adj (p.get i) (p.get j) = G.adj i j)
    {level : Nat} {s t : RefineSt n} (hs : RefineSt.Ready G level s)
    (ht : RefineSt.Ready H level t) (he : RefineSt.Equiv (renamingOf p) level s t)
    (tcLevel : Nat) (hint : Int) :
    targetcell (.ofGraph H) t.lab t.ptn level tcLevel hint =
      targetcell (.ofGraph G) s.lab s.ptn level tcLevel hint := by
  have hend : s.ptn[n - 1]! ≤ level := by
    simpa only [hs.spec.node.ptnSize] using hs.spec.node.ptnEnd
  obtain ⟨a, ha⟩ := Index.exists_valid hs.spec.label hs.spec.node.ptnSize hend
  obtain ⟨b, hb⟩ := Index.exists_valid ht.spec.label hs.spec.node.ptnSize hend
  obtain ⟨c, hc⟩ := Index.exists_valid (perm_map hs.spec.label p) hs.spec.node.ptnSize hend
  have hq : Equitable (Graph.context H) level t.lab s.ptn := by rw [← he.ptn]; exact ht.equitable
  rw [he.ptn]
  exact (targetcell_perm H t.lab (s.lab.map (renamingOf p).toFun) s.ptn level tcLevel hint
    b c ht.spec.label (perm_map hs.spec.label p) hs.spec.node.ptnSize hend hb hc hq he.cells).trans
    (targetcell_map G H p hiso s.lab s.ptn level tcLevel hint a c hs.spec.label
      hs.spec.node.ptnSize hend ha hc)

end Hex.GraphIso.Nauty.Sparse
