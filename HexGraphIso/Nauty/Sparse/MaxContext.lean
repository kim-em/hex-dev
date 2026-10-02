/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.MaxTrace
public import HexGraphIso.Nauty.Sparse.LoopCover
public import HexGraphIso.Nauty.Sparse.Capacity
public import HexGraphIso.Nauty.Sparse.PairsState
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.MaxCosetState
import all HexGraphIso.Nauty.Sparse.MaxRank
import all HexGraphIso.Nauty.Sparse.MaxGuides
import all HexGraphIso.Nauty.Sparse.MaxChoice
import all HexGraphIso.Nauty.Sparse.CodeState
import all HexGraphIso.Nauty.Sparse.PairsState
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The local invariants at an actual off-path node. Its saved ancestors
retain reference coverage, cursor ranks and trace stabilization; none of
these fields assumes the node's search result. -/
structure NodeInput (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat)
    (f : Frame n) (bs fs : List Nat) (parents : Parents n) : Prop where
  frame : f.Valid G
  codes : CodeEntry G tcLevel f.level f.numcells f.entry
  pairs : PairsEntry G tcLevel f.level f.numcells f.entry
  machine : Comparison G.graph f.codes bs fs f.entry
  scope : Scope G tcLevel f bs f.entry parents
  guides : Guides G.graph tcLevel f.entry parents
  cosets : Cosets f.entry parents
  ranked : ∀ t p, parents t = some p → p.Ranked G.graph tcLevel
  traces : Traces G f.entry parents
  orbits : OrbitTrace G f.entry
  counters : 0 < f.entry.gcaFirst ∧ f.entry.gcaFirst ≤ f.entry.gcaCanon ∧ f.entry.gcaCanon < f.level
  capacity : 0 < f.entry.wsCap

/-- A native sweep after its first leaf exists. Coverage refers to the
complete actual selected cell and its current cursor; all machine fields
refer to the executed state after preparation or child recovery. -/
structure SweepInput (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat)
    (l : Loop n) (bs fs : List Nat) (cursor : Option Nat) (cell : VSet n)
    (st : State n) (parents : Parents n) : Prop where
  frame : l.node.Valid G
  internal : (visit (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry).1 < n
  selected : (l.cell G.graph tcLevel).Valid G
  codes : CodeReady G tcLevel l.node.level (l.cell G.graph tcLevel).numcells st
  pairs : PairsReady G tcLevel l.node.level (l.cell G.graph tcLevel).numcells st
  machine : Comparison G.graph (l.cell G.graph tcLevel).codes bs fs st
  effect : FrameOut G l.node.level l.node.level (l.cell G.graph tcLevel).entry st
  target : Generic.Target State.frame l.node.level (l.cell G.graph tcLevel).tc cell st
  subset : ∀ v, cell.mem v = true → (l.cell G.graph tcLevel).vertices.mem v = true
  member : ∀ v, cursor = some v → cell.mem v = true
  choice : l.node.Choice G.graph tcLevel (l.cell G.graph tcLevel).tc (State.key G.graph bs st)
  small : st.noncheaplevel ≤ l.node.level → NodeShape n l.node.level st.ptn
  scope : Scope G tcLevel l.node bs st parents
  guides : Guides G.graph tcLevel st parents
  cosets : Cosets st parents
  ranked : ∀ t p, parents t = some p → p.Ranked G.graph tcLevel
  traces : Traces G st parents
  orbits : OrbitTrace G st
  self : l.first = true → TraceFrame G l.node.level st st
  guided : ∀ v, (l.parent G.graph tcLevel st bs cell v).Guided G.graph tcLevel
  counters : 0 < st.gcaFirst ∧ st.gcaFirst ≤ st.gcaCanon ∧ st.gcaCanon ≤ l.node.level
  first : l.first = true → st.gcaFirst = l.node.level
  other : l.first = false → st.gcaFirst < l.node.level
  capacity : 0 < st.wsCap
  recorded : CheapRecorded l.node.level (l.cell G.graph tcLevel).tc st
  route : RouteRecorded G.graph tcLevel l.node.level (l.cell G.graph tcLevel).tc st
  cover : (l.cell G.graph tcLevel).Cover G.graph tcLevel (Remaining cursor cell) (State.key G.graph bs st)
  phase : st.compCanon ≤ 0 ∨ l.first = false ∧ cursor.isSome

/-- A live cursor suspends a valid parent with the literal selected
coordinate. The frozen unhinted target is used only in its choice rule. -/
theorem SweepInput.parent {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    {bs fs : List Nat} {cursor : Option Nat} {cell : VSet n} {st : State n} {parents : Parents n}
    (h : SweepInput G tcLevel l bs fs cursor cell st parents) {tv : Nat} (hv : cell.mem tv = true) :
    (l.parent G.graph tcLevel st bs cell tv).Valid G tcLevel :=
  ⟨h.frame, h.internal, h.codes.ready, h.effect, h.target, hv, h.choice, h.small⟩

/-- Selecting the current cursor assembles every off-path child invariant
from the native sweep state. In particular its suspended rank comes from
the actual filtered-cell coverage, and first-ancestor stabilization is
transported through the executed individualization. -/
theorem SweepInput.child {G : GraphIso.Sparse.Colored n k} {tcLevel : Nat} {l : Loop n}
    {bs fs : List Nat} {cursor : Option Nat} {cell : VSet n} {st : State n} {parents : Parents n}
    (h : SweepInput G tcLevel l bs fs cursor cell st parents) {tv : Nat} (htv : cursor = some tv) :
    let p := l.parent G.graph tcLevel st bs cell tv
    NodeInput G tcLevel (p.child G.graph tcLevel) bs fs (parents.push p) := by
  let p := l.parent G.graph tcLevel st bs cell tv
  have hv := h.member tv htv
  have hp := h.parent hv
  have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
  have hgc : (p.child G.graph tcLevel).entry.gcaFirst = st.gcaFirst := by
    dsimp only [p, Parent.child, Loop.parent]
    cases l.first <;> rfl
  have hga : (p.child G.graph tcLevel).entry.gcaCanon = st.gcaCanon := by
    dsimp only [p, Parent.child, Loop.parent]
    cases l.first <;> rfl
  have hcap : (p.child G.graph tcLevel).entry.wsCap = st.wsCap := by
    dsimp only [p, Parent.child, Loop.parent]
    cases l.first <;> rfl
  have hc := h.cover
  rw [htv] at hc
  refine ⟨hp.child,
    h.codes.child hn h.frame.positive l.first h.target hv h.recorded h.route,
    h.pairs.child hn h.frame.positive l.first h.target hv h.recorded,
    h.machine.child l.first l.node.level (l.cell G.graph tcLevel).tc tv,
    h.scope.push hp, h.guides.child (h.guided tv),
    h.cosets.child h.scope (fun hf => Or.inr (h.first hf)) h.other,
    ?_, h.traces.child h.scope hp h.self,
    (orbitPolicy G (n + 2) tcLevel).child l.first l.node.level (l.cell G.graph tcLevel).tc tv st h.orbits,
    ?_, ?_⟩
  · intro t q hq
    by_cases he : t = l.node.level
    · change (parents.push p) t = some q at hq
      have hlevel : p.node.level = l.node.level := rfl
      simp only [Parents.push, hlevel, ite_eq_left he] at hq
      cases hq
      exact l.ranked h.selected h.effect h.codes.ready hc
    · change (parents.push p) t = some q at hq
      have hlevel : p.node.level = l.node.level := rfl
      simp only [Parents.push, hlevel, ite_eq_right he] at hq
      exact h.ranked t q hq
  · rw [hgc, hga]
    change 0 < st.gcaFirst ∧ st.gcaFirst ≤ st.gcaCanon ∧ st.gcaCanon < l.node.level + 1
    exact ⟨h.counters.1, h.counters.2.1, by have := h.counters.2.2; omega⟩
  · rw [hcap]
    exact h.capacity

/-- The coverage induction concerns the literal native off-path call,
with only smaller recursion bounds used as induction hypotheses. -/
def NodeMax (G : GraphIso.Sparse.Colored n k) (tcLevel fuel : Nat) : Prop :=
  ∀ (f : Frame n) (bs fs : List Nat) (parents : Parents n),
    NodeInput G tcLevel f bs fs parents → n ≤ f.codes.length + fuel →
      MaxResult (f.key G.graph tcLevel) (State.key G.graph bs f.entry)
        (State.best G.graph (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel
          f.level f.numcells f.entry).2) (f.level - 1)
        (Max.Witness G tcLevel parents.frames)
        (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).1

end Hex.GraphIso.Nauty.Sparse.Max
