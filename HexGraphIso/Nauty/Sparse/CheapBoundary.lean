/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PathState
public import HexGraphIso.Nauty.Sparse.BoundaryControl
public import HexGraphIso.Nauty.Policy.Boundary
import all HexGraphIso.Nauty.Policy.Boundary
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The implicit pair at every strictly older cheap boundary is valid at
the original ordered-colour partition. The logical level determines when
the saved pair is available to pruning. -/
abbrev CheapBoundary (G : GraphIso.Sparse.Colored n k) (level : Nat) (st : State n) : Prop :=
  Nauty.Boundary G.toDense (Graph.context G.graph) level st.frame

/-- An equitable native partition passing the cheap guard supplies the
implicit root pair used by the actual pruning workspace. -/
theorem Ready.pair {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (hc : cheapautom st.ptn level n = true) :
    PairOk (Graph.context G.graph).g
      (initPtn n (n + 2) (Nauty.initialPartition G.toDense).2)
      (Nauty.initialPartition G.toDense).1 1
      (fmptn st.lab st.ptn level n).1 (fmptn st.lab st.ptn level n).2 := by
  have hsymm : ∀ u v, u < n → v < n →
      ((Graph.context G.graph).g[u]!).mem v = ((Graph.context G.graph).g[v]!).mem u := by
    intro u v hu hv
    rw [Graph.context_mem G.graph ⟨u, hu⟩ ⟨v, hv⟩, Graph.context_mem G.graph ⟨v, hv⟩ ⟨u, hu⟩]
    exact G.graph.adj_symm _ _
  have hloop : ∀ v, v < n → ((Graph.context G.graph).g[v]!).mem v = false := by
    intro v hv
    rw [Graph.context_mem G.graph ⟨v, hv⟩ ⟨v, hv⟩]
    exact G.graph.adj_self _
  exact SubtreeOk.pair_ok (ctx := Graph.context G.graph) (G := G.toDense)
    (r := st.toPartition numcells) hn hl (by simp [Graph.context]) hsymm hloop (h.small hn hl hc)
    h.ok.reach h.ok.init1

namespace CheapBoundary

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st out : State n}

theorem congr (h : CheapBoundary G level st) (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (he : out.noncheaplevel = st.noncheaplevel) : CheapBoundary G level out :=
  h.ofFrames hl hp he

/-- Native refinement preserves every strictly older saved pair by its
proved caller-frame effect; the root's strict pair condition is empty. -/
theorem visit (h : CheapBoundary G level st) (hn : 0 < n) (hl : 1 ≤ level)
    (hi : NodeInv G level numcells st) :
    CheapBoundary G level (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 := by
  have hr := hi.visit_ready hn hl
  by_cases hlevel : 1 < level
  · have hx := hi.visit_frame hl (hr.frame rfl rfl (Or.inl rfl) (Or.inl rfl) hr.scratch.toBounded)
    exact Nauty.Boundary.of_out h hlevel hx.effect h.positive (Or.inl rfl)
  · have he : level = 1 := by omega
    subst level
    refine ⟨h.positive, hr.ok.labSize, hr.ok.ptnSize, searchOk_end hn hr.ok hl, ?_⟩
    intro hlt
    have hp := h.positive
    change 0 < st.noncheaplevel at hp
    change st.noncheaplevel < 1 at hlt
    omega

theorem record (h : CheapBoundary G level st) (code : Nat) :
    CheapBoundary G level (recordFirst level code st) := h.congr rfl rfl rfl

theorem compare (h : CheapBoundary G level st) (code : Nat) :
    CheapBoundary G level (compareCodes level code st) := by
  apply h.congr (compareCodes_frame level code st).1 (compareCodes_frame level code st).2.1
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]

theorem target (h : CheapBoundary G level st) (first : Bool) (tcLevel numcells : Nat) :
    CheapBoundary G level (chooseTarget first (.ofGraph G.graph) tcLevel level numcells st).2.2.2 :=
  h.congr (chooseTarget_frame first (.ofGraph G.graph) tcLevel level numcells st).1
    (chooseTarget_frame first (.ofGraph G.graph) tcLevel level numcells st).2.1
    (chooseTarget_controls first (.ofGraph G.graph) tcLevel level numcells st).2

theorem classify (h : CheapBoundary G level st) (numcells : Nat) :
    CheapBoundary G level (Sparse.classify (.ofGraph G.graph) level numcells st).2 :=
  h.congr (classify_frame (.ofGraph G.graph) level numcells st).1
    (classify_frame (.ofGraph G.graph) level numcells st).2.1
    (classify_controls (.ofGraph G.graph) level numcells st).2

theorem leaf (h : CheapBoundary G level st) (leaf : Leaf) :
    CheapBoundary G level (leafExit leaf level st).2 :=
  h.congr (leafExit_frame leaf level st).1 (leafExit_frame leaf level st).2.1 (leafExit_noncheap leaf level st)

/-- A passing native guard establishes the implicit pair, while a failing
guard parks the pair condition at the next child's depth. -/
theorem cheap (h : CheapBoundary G level st) (hn : 0 < n) (hl : 1 ≤ level)
    (hr : Ready G level numcells st) (first : Bool) :
    CheapBoundary G (level + 1) (cheapCheck first level st) := by
  have hh := Nauty.Boundary.cheap h first hl (hr.pair hn hl)
  unfold cheapCheck at hh ⊢
  split at hh <;> split <;> first | exact hh | contradiction

/-- Native individualization and cache invalidation preserve every pair
frozen above the child. -/
theorem child (h : CheapBoundary G (level + 1) st) (hl : 1 ≤ level)
    (first : Bool) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    CheapBoundary G (level + 1) ((policy (n := n)).child first level tc tv st) := by
  change Nauty.Boundary G.toDense (Graph.context G.graph) (level + 1) _
  rw [State.child_frame]
  exact Nauty.Boundary.child h first hl ht hv

/-- Every completed off-path call preserves still-active saved pairs;
only a new boundary at or below that call may replace the old boundary. -/
theorem node (h : CheapBoundary G level st) (hn : 0 < n) (hl : 1 < level)
    (hi : NodeInv G level numcells st) (tcLevel fuel : Nat) :
    CheapBoundary G level (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 :=
  Nauty.Boundary.of_out h hl (node_frame G hn false tcLevel fuel level numcells st (by omega) hi).effect
    (node_noncheap (bound := 0) (by omega) h.positive)
    (node_boundary (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st (by omega))

/-- Recovery revives an older pair, including equality at the next child's
logical level, using the literal native cache-invalidating operation. -/
theorem recover_child (h : CheapBoundary G (level + 1) st) (hl : 1 ≤ level)
    (hi : level < n + 2) :
    CheapBoundary G (level + 1) ((policy (n := n)).recover (n + 2) level st) := by
  change Nauty.Boundary G.toDense (Graph.context G.graph) (level + 1) _
  rw [State.recover_frame, ← recover_eq]
  exact Nauty.Boundary.recover_child h hl hi

end CheapBoundary

/-- Initialization starts at boundary one with no active implicit pair. -/
theorem initial_boundary (G : GraphIso.Sparse.Colored n k) (hn : 0 < n) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    CheapBoundary G 1 (initial (.ofGraph G.graph) p.1 p.2) :=
  CheapOk.root hn (NodeInv.initial G hn).ok rfl

end Hex.GraphIso.Nauty.Sparse
