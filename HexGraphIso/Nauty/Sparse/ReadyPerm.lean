/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FollowsPerm
import all HexGraphIso.Nauty.Policy.Descent
import all HexGraphIso.Nauty.Equitable.Step

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Reordering labels within the cells of a frozen equitable node retains
its node and refinement-certificate invariants. The partition and its saved
active set remain those of the ancestor witness. -/
theorem RefineSt.Ready.setLab {G : Hex.SparseGraph n} {level : Nat} {s : RefineSt n}
    (h : RefineSt.Ready G level s) (lab : Array Nat) (hsize : lab.size = s.lab.size)
    (hcells : cellsPerm s.ptn level lab s.lab) : RefineSt.Ready G level { s with lab } := by
  have hlen : lab.size = n := hsize.trans h.spec.node.labSize
  have hp := cellsPerm_segN_perm hcells (Nat.le_of_eq h.spec.node.ptnSize.symm)
    h.spec.node.ptnEnd (by simpa only [h.spec.node.ptnSize] using h.spec.node.ptnEnd)
  rw [segN_eq_toList hlen, segN_eq_toList h.spec.node.labSize] at hp
  have hperm := hp.trans h.spec.label
  have he : StPerm level { s.toPartition with lab } s.toPartition :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsize.symm, hcells⟩
  have heq : Equitable (Graph.context G) level lab s.ptn :=
    he.equitable h.equitable h.spec.node.ptnSize h.spec.node.ptnEnd
  refine ⟨⟨hperm, ⟨hlen, ?_, h.spec.node.ptnSize, h.spec.node.ptnEnd,
    h.spec.node.starts, h.spec.node.vals⟩, h.spec.count, h.spec.depth, ?_⟩, heq⟩
  · intro i hi
    exact perm_bound hperm (by rw [hlen] at hi; exact hi)
  · intro p hp _ c hc
    refine ⟨VSet.empty, VSet.empty_inter _, ?_, ?_⟩
    · intro d hd
      exact Or.inl (VSet.inter_empty _)
    · simpa only [VSet.union_empty] using splitDone_iff_constOn.mp (heq c hc p hp)

end Hex.GraphIso.Nauty.Sparse
