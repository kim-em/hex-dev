/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxCoset
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Reordering a recovered equitable parent changes neither reference
containment nor stabilization of its cells. This supplies the exact
current ordering used when the next sibling is suspended. -/
theorem TraceFrame.rebase {G : GraphIso.Sparse.Colored n k} {level numcells : Nat}
    {root st : State n} (h : TraceFrame G level root st)
    (hr : Ready G level numcells root) (hs : Ready G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) : TraceFrame G level st st := by
  have hp : st.ptn = root.ptn := h.frame.effect.ptnEq hr.ok hs.ok
  refine ⟨⟨SearchOut.refl _ _ _ hs.ok.reach, hs.scratch.toBounded⟩,
    ⟨h.first.1, ?_⟩, ⟨h.canon.1, ?_⟩, ?_, h.work⟩
  · rw [hp]
    exact cellsPerm_trans (cellsPerm_symm h.frame.effect.perm) h.first.2
  · rw [hp]
    exact cellsPerm_trans (cellsPerm_symm h.frame.effect.perm) h.canon.2
  · intro gamma hg
    rw [hp]
    exact LocalAutos.reindexStab (h.trace gamma hg) h.frame.effect.perm
      hr.ok.ptnSize hr.ok.labSize hs.ok.labSize (searchOk_end hn hr.ok hl)

/-- The current first-sweep trace also stabilizes its original frozen
cell ordering. Recovery permutes labels only within those cells. -/
theorem TraceFrame.freeze {G : GraphIso.Sparse.Colored n k} {level numcells : Nat}
    {root st : State n} (h : TraceFrame G level st st)
    (he : FrameOut G level level root st)
    (hr : Ready G level numcells root) (hs : Ready G level numcells st)
    (hn : 0 < n) (hl : 1 ≤ level) : TraceFrame G level root st := by
  have hp : st.ptn = root.ptn := he.effect.ptnEq hr.ok hs.ok
  refine ⟨he, ⟨h.first.1, ?_⟩, ⟨h.canon.1, ?_⟩, ?_, h.work⟩
  · apply cellsPerm_trans he.effect.perm
    change cellsPerm root.ptn level st.lab st.firstlab
    rw [← hp]
    exact h.first.2
  · apply cellsPerm_trans he.effect.perm
    change cellsPerm root.ptn level st.lab st.canonlab
    rw [← hp]
    exact h.canon.2
  · intro gamma hg
    have ht := h.trace gamma hg
    rw [hp] at ht
    exact LocalAutos.reindexStab ht (cellsPerm_symm he.effect.perm)
      hr.ok.ptnSize hs.ok.labSize hr.ok.labSize (searchOk_end hn hr.ok hl)

namespace Max

/-- Every suspended first sweep contains both saved labels and is
stabilized by the complete emitted trace in the current native state. -/
def Traces (G : GraphIso.Sparse.Colored n k) (st : State n) (parents : Parents n) : Prop :=
  ∀ t p, parents t = some p → p.first = true → TraceFrame G p.node.level p.state st

theorem Traces.root (G : GraphIso.Sparse.Colored n k) (st : State n) : Traces G st (fun _ => none) := by
  intro t p hp
  cases hp

/-- The actual first call establishes every older first ancestor's
reference containment and stabilization directly from its first leaf.
The native parent chain supplies all required incoming frame effects. -/
theorem Traces.first_node {G : GraphIso.Sparse.Colored n k} {tcLevel fuel last : Nat}
    {f : Frame n} {bs : List Nat} {st leaf : State n} {parents : Parents n}
    (hs : Scope G tcLevel f bs st parents) (hf : f.Valid G)
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel f.level f.numcells f.entry last leaf)
    (hw : f.entry.workperm.size = n) (he : f.entry.genTrace = #[]) :
    Traces G (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2 parents := by
  intro t p hp _
  obtain ⟨_, ht, hlevel, hv⟩ := hs.valid t p hp
  have hn : 0 < n := by have := hf.positive; have := hf.depth; omega
  exact firstPath_stabilizes hv.ready hn hv.node.positive path (by omega) hf.node
    (hs.frame hf hp) hw he

/-- Complete descendant calls retain every suspended first ancestor's
native trace frame, including nonlocal returns and truncated calls. -/
theorem Traces.node {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {st : State n} {parents : Parents n}
    (h : Traces G f.entry parents) (hs : Scope G tcLevel f bs st parents) (hf : f.Valid G)
    (first : Bool) (fuel : Nat) :
    Traces G (Generic.node first (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2 parents := by
  intro t p hp hfirst
  obtain ⟨_, ht, hlevel, hv⟩ := hs.valid t p hp
  have hn : 0 < n := by have := hf.positive; have := hf.depth; omega
  exact (h t p hp hfirst).node hv.ready hn hv.node.positive (by omega) hf.node first tcLevel fuel

theorem Traces.prepare {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {f : Frame n} {bs : List Nat} {parents : Parents n}
    (h : Traces G f.entry parents) (hs : Scope G tcLevel f bs f.entry parents) (hf : f.Valid G)
    (tv : Nat) : Traces G (f.otherParent G.graph tcLevel bs tv).state parents := by
  intro t p hp hfirst
  obtain ⟨_, ht, hlevel, hv⟩ := hs.valid t p hp
  have hn : 0 < n := by have := hf.positive; have := hf.depth; omega
  let v := visit (.ofGraph G.graph) f.level f.numcells f.entry
  have hvisit := (h t p hp hfirst).visit hv.ready hf.node hn hv.node.positive (by omega)
  exact ((hvisit.compare f.level v.2.1).target false tcLevel f.level v.1).cheap false f.level

/-- Suspending a first sweep adds its own current trace frame. Native
individualization transports every older frame into the selected child. -/
theorem Traces.child {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {parents : Parents n} (h : Traces G p.state parents)
    (hs : Scope G tcLevel p.node p.bs p.state parents) (hp : p.Valid G tcLevel)
    (hself : p.first = true → TraceFrame G p.node.level p.state p.state) :
    Traces G (p.child G.graph tcLevel).entry (parents.push p) := by
  intro t q hq hfirst
  have hn : 0 < n := by have := hp.node.positive; have := hp.node.depth; omega
  by_cases he : t = p.node.level
  · simp only [Parents.push, ite_eq_left he] at hq
    cases hq
    exact (hself hfirst).child hp.ready hp.ready hn hp.node.positive (Nat.le_refl _)
      p.first hp.target hp.chosen
  · simp only [Parents.push, ite_eq_right he] at hq
    obtain ⟨_, ht, hlevel, hv⟩ := hs.valid t q hq
    exact (h t q hq hfirst).child hv.ready hp.ready hn hv.node.positive (by omega)
      p.first hp.target hp.chosen

/-- Both actual return paths preserve the trace frames of the receiving
parent and all older suspended first sweeps, through fixed-point cleanup
and native partition recovery. -/
theorem Traces.recovered {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {parents : Parents n} {raw : State n}
    (h : Traces G raw (parents.push p)) (hs : Scope G tcLevel p.node p.bs p.state parents)
    (hp : p.Valid G tcLevel) (first : Bool) :
    let left := (policy (n := n)).leaveChild p.chosen
      (if first then afterChildFirst p.node.level p.chosen raw else raw)
    Traces G ((policy (n := n)).recover (n + 2) p.node.level left) (parents.push p) := by
  intro left t q hq hfirst
  have hscope := hs.push hp
  obtain ⟨_, ht, hlevel, hv⟩ := hscope.valid t q hq
  have hn : 0 < n := by have := hp.node.positive; have := hp.node.depth; omega
  have hh : TraceFrame G q.node.level q.state left := by
    cases first with
    | false => exact (h t q hq hfirst).leave p.chosen
    | true => exact ((h t q hq hfirst).afterChild p.node.level p.chosen).leave p.chosen
  apply hh.recover hv.ready hn hv.node.positive _ hp.node.depth
  change t < p.node.level + 1 at ht
  omega

theorem Traces.pop {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat}
    {p : Parent n} {parents : Parents n} {st : State n}
    (h : Traces G st (parents.push p)) (hs : Scope G tcLevel p.node p.bs p.state parents) :
    Traces G st parents := by
  intro t q hq hfirst
  have hb := (hs.valid t q hq).2.1
  apply h t q _ hfirst
  simp only [Parents.push, ite_eq_right (by omega : t ≠ p.node.level)]
  exact hq

end Max
end Hex.GraphIso.Nauty.Sparse
