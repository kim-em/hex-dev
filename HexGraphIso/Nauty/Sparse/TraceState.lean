/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Saved
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- An off-path entry carries a pending history for its actual cached
visit, together with already installed references and a sound trace. -/
structure TraceEntry (G : GraphIso.Sparse.Colored n k) (tcLevel level numcells : Nat) (st : State n) : Prop where
  node : NodeInv G level numcells st
  saved : Saved G st
  trace : TraceOk G st
  ancestor : st.gcaFirst ≤ level
  history : let r := visit (.ofGraph G.graph) level numcells st
    CheapHistory G.graph tcLevel level (level - 1) r.1 r.2.2

/-- A prepared node or recovered sweep has an equitable current partition,
live cheap history, valid references, and a sound emitted trace. -/
structure TraceReady (G : GraphIso.Sparse.Colored n k) (tcLevel level numcells : Nat) (st : State n) : Prop where
  ready : Ready G level numcells st
  saved : Saved G st
  trace : TraceOk G st
  ancestor : st.gcaFirst ≤ level
  history : CheapHistory G.graph tcLevel level level numcells st

theorem TraceEntry.prepare {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat} {st : State n}
    (h : TraceEntry G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    let r := prepareOther (.ofGraph G.graph) tcLevel level numcells st
    TraceReady G tcLevel level r.1 r.2.2.2.2.2 := by
  let v := visit (.ofGraph G.graph) level numcells st
  let c := compareCodes level v.2.1 v.2.2
  have hv := h.node.visit_ready hn hl
  refine ⟨((hv.compare v.2.1).ready.target_frame false tcLevel).ready,
    ((h.saved.visit level numcells).compare level v.2.1).target tcLevel level v.1,
    ((h.trace.visit level numcells).compare level v.2.1).target false tcLevel level v.1, ?_, ?_⟩
  · have ht := (chooseTarget_controls false (.ofGraph G.graph) tcLevel level v.1 c).1
    have hc := (gcaPolicy (.ofGraph G.graph) 0 tcLevel).compare level v.2.1 v.2.2
    change c.gcaFirst = st.gcaFirst at hc
    change (chooseTarget false (.ofGraph G.graph) tcLevel level v.1 c).2.2.2.gcaFirst ≤ level
    rw [ht, hc]
    exact h.ancestor
  · have hb := refineWith_code_lt (.ofGraph G.graph) level st.lab st.ptn st.active numcells st.canong.scratch
    exact (h.history.compare (by omega) hb).target

namespace TraceReady

variable {G : GraphIso.Sparse.Colored n k} {tcLevel level numcells : Nat} {st : State n}

/-- Classifying and executing a leaf action preserves all validity facts,
and every appended automorphism is justified by the native admission proof. -/
theorem classified (h : TraceReady G tcLevel level numcells st) (hn : 0 < n) :
    let c := classify (.ofGraph G.graph) level numcells st
    TraceReady G tcLevel level numcells (leafExit c.1 level c.2).2 := by
  let c := classify (.ofGraph G.graph) level numcells st
  obtain ⟨l, hl⟩ := h.ready.parse hn
  have hr := h.ready.classify
  have hc := h.saved.store.classify level numcells l hl
  have ha := classify_auto hn h.ready h.history h.saved.store h.saved.canonical h.saved.first h.saved.work
  refine ⟨(hr.ready.leaf c.1).ready,
    (h.saved.classify level numcells l hl).leaf hr.ready c.1 hc.2,
    (h.trace.classify level numcells).leaf c.1 level ha, ?_, h.history.classify.leaf c.1⟩
  rw [leafExit_gca, (classify_controls (.ofGraph G.graph) level numcells st).1]
  exact h.ancestor

theorem cheap (h : TraceReady G tcLevel level numcells st) (first : Bool) :
    TraceReady G tcLevel level numcells (cheapCheck first level st) := by
  refine ⟨(h.ready.cheap first).ready, h.saved.cheap first level, h.trace.cheap first level,
    ?_, h.history.cheap first h.ancestor⟩
  change (cheapCheck first level st).gcaFirst ≤ level
  unfold cheapCheck
  split <;> exact h.ancestor

theorem child (h : TraceReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first : Bool) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (hrecord : CheapRecorded level tc st) :
    TraceEntry G tcLevel (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st) := by
  refine ⟨h.ready.child hn hl first ht hv, h.saved.child first level tc tv,
    h.trace.child first level tc tv, ?_, h.history.child first h.ready ht hv hrecord⟩
  have ha := h.ancestor
  cases first <;> change st.gcaFirst ≤ level + 1 <;> omega

/-- A sound trace returned by an actual child combines with independently
proved frame, cache and history effects to establish the next sweep state. -/
theorem child_return (h : TraceReady G tcLevel level numcells st) (hn : 0 < n) (hl : 1 ≤ level)
    (first : Bool) (fuel : Nat) {tc tv : Nat} {cell : VSet n}
    (ht : Generic.Target State.frame level tc cell st) (hv : cell.mem tv = true)
    (htrace : TraceOk G (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2) :
    let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
      (level + 1) (numcells + 1) ((policy (n := n)).child first level tc tv st)).2
    let result := (policy (n := n)).recover (n + 2) level ((policy (n := n)).leaveChild tv out)
    TraceReady G tcLevel level numcells result ∧
      (CheapRecorded level tc st → CheapRecorded level tc result) := by
  let ch := (policy (n := n)).child first level tc tv st
  let out := (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (numcells + 1) ch).2
  let left := (policy (n := n)).leaveChild tv out
  have hch := h.ready.child hn hl first ht hv
  have ho := node_frame G hn false tcLevel fuel (level + 1) (numcells + 1) ch (by omega) hch
  have hf := h.ready.child_frame hn hl first ht hv (by simpa only [Nat.add_sub_cancel] using ho)
  have hh := h.history.child_return (fuel := fuel) first h.ancestor hl h.ready ht hv
  refine ⟨⟨(h.ready.recover hn hl (hf.leave tv)).1,
    (((h.saved.child first level tc tv).node hn tcLevel fuel (level + 1) (numcells + 1) (by omega) hch).leave tv).recover (n + 2) level,
    (htrace.leave tv).recover (n + 2) level, ?_, hh.1⟩, hh.2⟩
  have hr := (gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left
  change ((policy (n := n)).recover (n + 2) level left).gcaFirst = out.gcaFirst at hr
  rw [hr, node_gca]
  cases first <;> exact h.ancestor

end TraceReady
end Hex.GraphIso.Nauty.Sparse
