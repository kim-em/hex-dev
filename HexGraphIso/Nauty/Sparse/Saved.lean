/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Trace
public import HexGraphIso.Nauty.Sparse.ComparisonOps
import all HexGraphIso.Nauty.Sparse.FirstRef
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- The installed references and workspace needed to interpret an actual
automorphism verdict. This asserts validity, independently of maximality
or generator soundness. -/
structure Saved (G : GraphIso.Sparse.Colored n k) (st : State n) : Prop where
  first : st.firstlab.size = n ∧ CellsReach G.toDense st.firstlab
  canonical : CanonLabel G st
  store : Store G.graph st
  work : st.workperm.size = n

namespace Saved

variable {G : GraphIso.Sparse.Colored n k} {st out : State n}

theorem congr (h : Saved G st) (hf : out.firstlab = st.firstlab) (hc : out.canonlab = st.canonlab)
    (hs : Store G.graph out) (hw : out.workperm.size = st.workperm.size) : Saved G out :=
  ⟨by rw [hf]; exact h.first, h.canonical.congr hc, hs, hw.trans h.work⟩

theorem visit (h : Saved G st) (level numcells : Nat) :
    Saved G (Sparse.visit (.ofGraph G.graph) level numcells st).2.2 :=
  h.congr rfl rfl (h.store.visit level numcells) rfl

theorem compare (h : Saved G st) (level code : Nat) : Saved G (compareCodes level code st) := by
  have hf := compareCodes_frame level code st
  apply h.congr hf.2.2.1 hf.2.2.2 (h.store.compare level code)
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite (fun s : State n => s.workperm.size), ite_self]

theorem target (h : Saved G st) (tcLevel level numcells : Nat) :
    Saved G (chooseTarget false (.ofGraph G.graph) tcLevel level numcells st).2.2.2 := by
  have hf := chooseTarget_frame false (.ofGraph G.graph) tcLevel level numcells st
  exact h.congr hf.2.2.1 hf.2.2.2 (h.store.target false tcLevel level numcells)
    (chooseTarget_workSize false (.ofGraph G.graph) tcLevel level numcells st)

theorem classify (h : Saved G st) (level numcells : Nat) (l : Label n)
    (hl : Label.ofArray? n st.lab = some l) :
    Saved G (Sparse.classify (.ofGraph G.graph) level numcells st).2 := by
  have hf := classify_frame (.ofGraph G.graph) level numcells st
  exact h.congr hf.2.2.1 hf.2.2.2 (h.store.classify level numcells l hl).1
    (classify_workSize (.ofGraph G.graph) level numcells st)

theorem cheap (h : Saved G st) (first : Bool) (level : Nat) : Saved G (cheapCheck first level st) := by
  unfold cheapCheck
  split <;> exact h.congr rfl rfl (h.store.congr rfl rfl rfl) rfl

theorem child (h : Saved G st) (first : Bool) (level tc tv : Nat) :
    Saved G ((policy (n := n)).child first level tc tv st) := by
  cases first <;> exact h.congr rfl rfl (h.store.child _ level tc tv) rfl

theorem afterChild (h : Saved G st) (level tv : Nat) : Saved G (afterChildFirst level tv st) :=
  h.congr rfl rfl (h.store.afterChild level tv) rfl

theorem leave (h : Saved G st) (tv : Nat) : Saved G ((policy (n := n)).leaveChild tv st) :=
  h.congr rfl rfl (h.store.leave tv) rfl

theorem recover (h : Saved G st) (inf level : Nat) :
    Saved G ((policy (n := n)).recover inf level st) := by
  have hl := recover_labels inf level st
  apply h.congr hl.1 hl.2 (h.store.recover inf level)
  change (recoverLevels level (recoverPtn inf level st)).workperm.size = st.workperm.size
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
    apply_ite (fun s : State n => s.workperm.size), ite_self]

/-- A leaf can replace its incumbent with the reached current label while
retaining all reference, native row-prefix and workspace guarantees. -/
theorem leaf (h : Saved G st) {level numcells : Nat} (hr : Ready G level numcells st)
    (leaf : Leaf) (hc : ∀ sr, leaf = .better sr → Candidate G.graph st sr) :
    Saved G (leafExit leaf level st).2 := by
  have hl := hr.leaf leaf
  refine ⟨?_, hl.frame.canonical h.canonical, h.store.leaf leaf level hc, ?_⟩
  · rw [(leafExit_frame leaf level st).2.2.1]
    exact h.first
  · exact (leafExit_workSize leaf level st).trans h.work

/-- All the saved validity facts survive a complete off-path call using
the independent reference, frame, cache and allocation theorems. -/
theorem node (h : Saved G st) (hn : 0 < n) (tcLevel fuel level numcells : Nat)
    (hl : 1 ≤ level) (hi : NodeInv G level numcells st) :
    Saved G (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  have hr := node_frame G hn false tcLevel fuel level numcells st hl hi
  have hf := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.2)
    (node_reference (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st)
  change (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2.firstlab = st.firstlab at hf
  exact ⟨by rw [hf]; exact h.first, hr.canonical h.canonical,
    node_store G hn false tcLevel fuel level numcells st hl hi h.store,
    (node_workSize false (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).trans h.work⟩

end Saved

/-- The actual first path reaches a native discrete prepared leaf, with
its original colour-cell reachability and cache invariant intact. -/
theorem firstPath_ready {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (hn : 0 < n) (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hl : 1 ≤ level) (hi : NodeInv G level numcells st) : Ready G last n leaf := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    have hr := (hi.prepare (tcLevel := tcLevel) hn hl).1
    rw [hdisc] at hr
    exact hr
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    obtain ⟨hr, ht⟩ := hi.prepare (tcLevel := tcLevel) hn hl
    have hc := hr.cheap true
    have htarget := ht.of_out hc.frame.effect
    exact ih (by omega) (hc.ready.child hn hl true htarget (VSet.nextElem_mem htv))

/-- The completed actual first path supplies both valid reference labels
and the installed native row prefix for subsequent admissions. -/
theorem firstPath_saved {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (hi : NodeInv G level numcells st)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hb : st.canong.toRows = (Graph.ofGraph G.graph).blank) (hw : st.workperm.size = n) :
    Saved G (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  have hf := firstPath_ready hn path hl hi
  have hr := congrArg (fun x : Array Nat × Array Int × Array Nat => x.2.2)
    (firstPath_reference (inf := n + 2) path)
  change (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2.firstlab = leaf.lab at hr
  exact ⟨by rw [hr]; exact ⟨hf.ok.labSize, hf.ok.reach⟩,
    firstPath_canonical hn path hl hi, firstPath_store hn path hl hi hb,
    (node_workSize true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).trans hw⟩

end Hex.GraphIso.Nauty.Sparse
