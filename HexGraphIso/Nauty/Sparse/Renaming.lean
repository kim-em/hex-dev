/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Spec.FiniteRenaming
public import HexGraphIso.Nauty.Sparse.ContextMap
public import HexGraphIso.Nauty.Sparse.SmallCell

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The shared row interpretation of a renaming gives native adjacency
preservation by its finite permutation. -/
theorem Graph.context_iso (G H : Hex.SparseGraph n) (σ : Renaming n)
    (h : RowsMap σ (Graph.context G).g (Graph.context H).g) :
    ∀ i j, H.adj (σ.toPerm.get i) (σ.toPerm.get j) = G.adj i j := by
  intro i j
  have he := congrArg (fun row : VSet n => row.mem (σ j.val)) (h.2.2 i.val i.isLt)
  rw [VSet.mem_image_apply σ _ j.isLt] at he
  rw [← Renaming.get_toPerm σ i, ← Renaming.get_toPerm σ j] at he
  rw [Graph.context_mem H (σ.toPerm.get i) (σ.toPerm.get j), Graph.context_mem G i j] at he
  exact he

/-- The automorphism supplied by the cheap shape can be consumed directly
by native refinement transport, with the same moved vertex and cell action. -/
theorem Ready.automorphism {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hshape : NodeShape n level st.ptn) {tc te a b : Nat}
    (hc : (tc, te) ∈ cells st.ptn level n) (hne : tc < te)
    (ha : a ≤ te - tc) (hb : b ≤ te - tc) (hab : a ≠ b) :
    ∃ p : Perm n, (∀ i j, G.graph.adj (p.get i) (p.get j) = G.graph.adj i j) ∧
      cellsPerm st.ptn level st.lab (st.lab.map (renamingOf p).toFun) ∧
      st.lab[tc + b]! = renamingOf p st.lab[tc + a]! := by
  obtain ⟨σ, hg, hp, hm⟩ := h.transitive hn hl hshape hc hne ha hb hab
  have hv : ∀ i, i < st.lab.size → st.lab[i]! < n := (h.partition hn hl).labOk
  have hpart := h.partition hn hl
  have hte := cells_bound (Nat.le_of_eq hpart.ptnSize.symm) hpart.ptnEnd (tc, te) hc
  have htc := cells_le (tc, te) hc
  have hval : st.lab[tc + a]! < n := hv _ (by rw [hpart.ptnSize] at hte; rw [hpart.labSize]; omega)
  refine ⟨σ.toPerm, Graph.context_iso G.graph G.graph σ hg, ?_, ?_⟩
  · rw [σ.map_toPerm st.lab hv]
    exact hp
  · rw [renamingOf_lt σ.toPerm hval, Renaming.get_toPerm]
    exact hm

end Hex.GraphIso.Nauty.Sparse
