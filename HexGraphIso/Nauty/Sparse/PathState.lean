/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Fixed
public import HexGraphIso.Nauty.Sparse.Stabilize
public import HexGraphIso.Nauty.Policy.PathState
import all HexGraphIso.Nauty.Policy.Generic.Reach
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The current individualized vertices are singleton cells, and every
root-colour stabilizer fixing them stabilizes the current partition. -/
abbrev PathInv (G : GraphIso.Sparse.Colored n k) (level : Nat) (st : State n) : Prop :=
  Nauty.PathInv G.toDense (Graph.context G.graph) level st.frame

namespace PathInv

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st out : State n}

theorem fields (h : PathInv G level st) (hl : out.lab = st.lab) (hp : out.ptn = st.ptn)
    (hf : out.fixedpts = st.fixedpts) : PathInv G level out :=
  Nauty.PathInv.fields h hl hp hf

/-- Refinement uses the native cached equivariance theorem for the path
stabilizer, together with literal preservation of fixed singletons. -/
theorem visit (h : PathInv G level st) (hi : NodeInv G level numcells st) :
    PathInv G level (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 := by
  refine ⟨fixed_visit hi h.fixed, ?_⟩
  intro gamma hg hroot hfix
  exact cellStab_refineWith G.graph level st.lab st.ptn st.active numcells st.canong.scratch
    hi.spec.label hi.spec.node.ptnSize (by simpa only [hi.spec.node.ptnSize] using hi.spec.node.ptnEnd)
    hi.spec.node.starts hi.scratch hg (h.stab gamma hg hroot hfix)

theorem record (h : PathInv G level st) (code : Nat) :
    PathInv G level (recordFirst level code st) := h.fields rfl rfl rfl

theorem compare (h : PathInv G level st) (code : Nat) :
    PathInv G level (compareCodes level code st) :=
  h.fields (compareCodes_frame level code st).1 (compareCodes_frame level code st).2.1
    (compare_fixed level code st)

theorem target (h : PathInv G level st) (first : Bool) (tcLevel numcells : Nat) :
    PathInv G level (chooseTarget first (.ofGraph G.graph) tcLevel level numcells st).2.2.2 :=
  h.fields (chooseTarget_frame first (.ofGraph G.graph) tcLevel level numcells st).1
    (chooseTarget_frame first (.ofGraph G.graph) tcLevel level numcells st).2.1
    (target_fixed first (.ofGraph G.graph) tcLevel level numcells st)

theorem classify (h : PathInv G level st) (numcells : Nat) :
    PathInv G level (Sparse.classify (.ofGraph G.graph) level numcells st).2 :=
  h.fields (classify_frame (.ofGraph G.graph) level numcells st).1
    (classify_frame (.ofGraph G.graph) level numcells st).2.1
    (classify_fixed (.ofGraph G.graph) level numcells st)

theorem terminal (h : PathInv G level st) : PathInv G level (firstterminal level st) :=
  h.fields rfl rfl rfl

theorem leaf (h : PathInv G level st) (leaf : Leaf) : PathInv G level (leafExit leaf level st).2 :=
  h.fields (leafExit_frame leaf level st).1 (leafExit_frame leaf level st).2.1 (leaf_fixed leaf level st)

theorem cheap (h : PathInv G level st) (first : Bool) : PathInv G level (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.fields rfl rfl rfl

/-- Individualization supplies path stabilization for automorphisms fixing
the selected vertex, without changing the sparse child operation. -/
theorem child (h : PathInv G level st) (hn : 0 < n) (hl : 1 ≤ level)
    (hr : Ready G level numcells st) (first : Bool) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    PathInv G (level + 1) ((policy (n := n)).child first level tc tv st) := by
  have hc := Nauty.PathInv.child h first hn hl hr.ok ht hv
  cases first <;> exact hc

/-- Parent recovery transports the path stabilizer along the actual frame
and the exactly restored fixed-point set. -/
theorem recover (h : PathInv G level st) (hn : 0 < n) (hl : 1 ≤ level)
    (hr : Ready G level numcells st) (hx : FrameOut G level level st out)
    (he : out.fixedpts = st.fixedpts) :
    PathInv G level ((policy (n := n)).recover (n + 2) level out) := by
  have hh := hr.recover hn hl hx
  exact h.ofSearchOut hn hl ((recover_fixed (n + 2) level out).trans he)
    hr.ok hh.1.ok hh.2.effect

/-- A complete native child call, including first descent or a nonlocal
exit, restores the parent's path invariant when its receiving frame is recovered. -/
theorem child_return (h : PathInv G level st) (hn : 0 < n) (hl : 1 ≤ level)
    (hr : Ready G level numcells st) (first descendFirst : Bool) (tcLevel fuel tc tv : Nat)
    (cell : VSet n) (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true) :
    let child := (policy (n := n)).child first level tc tv st
    let out := (Generic.node descendFirst (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) child).2
    PathInv G level ((policy (n := n)).recover (n + 2) level
      ((policy (n := n)).leaveChild tv out)) := by
  dsimp only
  have hi := hr.child hn hl first ht hv
  have hc := h.child hn hl hr first ht hv
  have hx := node_frame G hn descendFirst tcLevel fuel (level + 1) (numcells + 1) _ (by omega) hi
  have he := node_fixed hn descendFirst tcLevel fuel (level + 1) (numcells + 1) _ (by omega) hi hc.fixed
  apply h.recover hn hl hr ((hr.child_frame hn hl first ht hv hx).leave tv)
  apply fixed_restore (st := st)
  · exact he.trans (by cases first <;> rfl)
  · exact (fixed_child first hn hr h.fixed ht hv).1

end PathInv

/-- Stable colour initialization has no fixed vertices and is its own
root stabilization frame. This statement also includes the empty graph. -/
theorem initial_pathInv (G : GraphIso.Sparse.Colored n k) :
    let p := initialPartitionWith n k G.coloring.cells.toArray Fin.val
    PathInv G 1 (initial (.ofGraph G.graph) p.1 p.2) := by
  simp only [initialPartition_eq]
  constructor
  · intro v hv hm
    change VSet.empty.mem v = true at hm
    simp at hm
  · exact PathStab.same (ctx := Graph.context G.graph)
      (st := (initial (.ofGraph G.graph) (Nauty.initialPartition G.toDense).1
        (Nauty.initialPartition G.toDense).2).frame)

end Hex.GraphIso.Nauty.Sparse
