/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReadyFrame
public import HexGraphIso.Nauty.SmallCell.Monotone
import all HexGraphIso.Nauty.SmallCell.Transitive

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The shared partition interpretation of a native search state. This
proof projection is never passed to executable dense refinement or search. -/
@[expose] noncomputable def State.toPartition (numcells : Nat) (st : State n) : Nauty.RefineSt n := {
  lab := st.lab, ptn := st.ptn, active := st.active, numcells
  hint := 0, maxpos := 0, longcode := 0 }

namespace Ready

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}

theorem iterOk (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    IterOk (Graph.context G.graph) level (st.toPartition numcells) := by
  have hp := h.partition hn hl
  refine ⟨⟨hp.labSize, hp.labOk, hp.ptnSize, hp.ptnEnd⟩, ?_, h.ok.vals,
    Nat.le_trans h.ok.bc (bcount_le _ _ _)⟩
  exact fun _ _ hi hj he => perm_injective (isPerm_of_cellsReach h.ok.labSize hn h.ok.reach) hi hj he

/-- A passing cheap guard supplies exactly the shared small-cell shape
for the actual native equitable partition. -/
theorem small (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : cheapautom st.ptn level n = true) :
    SubtreeOk (Graph.context G.graph) level (st.toPartition numcells) :=
  subtreeOk_of_cheapautom (h.iterOk hn hl) h.equitable h.ok.count.symm hc

/-- At a native equitable node with the cheap shape, its cell stabilizer
can carry either selected member of a cell to the other. The shared
finite-graph argument consumes only the proved partition interpretation. -/
theorem transitive (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hshape : NodeShape n level st.ptn) {tc te a b : Nat}
    (hc : (tc, te) ∈ cells st.ptn level n) (hne : tc < te)
    (ha : a ≤ te - tc) (hb : b ≤ te - tc) (hab : a ≠ b) :
    ∃ σ : Renaming n, RowsMap σ (Graph.context G.graph).g (Graph.context G.graph).g ∧
      cellsPerm st.ptn level st.lab (st.lab.map σ.toFun) ∧
      st.lab[tc + b]! = σ st.lab[tc + a]! := by
  have hs : SubtreeOk (Graph.context G.graph) level (st.toPartition numcells) :=
    ⟨h.iterOk hn hl, h.equitable, h.ok.count.symm, hshape⟩
  have hsymm : ∀ u v, u < n → v < n →
      ((Graph.context G.graph).g[u]!).mem v = ((Graph.context G.graph).g[v]!).mem u := by
    intro u v hu hv
    rw [Graph.context_mem G.graph ⟨u, hu⟩ ⟨v, hv⟩, Graph.context_mem G.graph ⟨v, hv⟩ ⟨u, hu⟩]
    exact G.graph.adj_symm _ _
  have hloop : ∀ v, v < n → ((Graph.context G.graph).g[v]!).mem v = false := by
    intro v hv
    rw [Graph.context_mem G.graph ⟨v, hv⟩ ⟨v, hv⟩]
    exact G.graph.adj_self _
  obtain ⟨σ, hg, hp, hm⟩ := stabilizer_transitive hs (by simp [Graph.context]) hsymm hloop hc hne ha hb hab
  exact ⟨σ, hg, hp.cells, hm⟩

end Ready
end Hex.GraphIso.Nauty.Sparse
