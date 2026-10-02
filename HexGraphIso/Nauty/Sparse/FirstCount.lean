/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.FirstTail
public import HexGraphIso.Nauty.Sparse.FirstSuffix
public import HexGraphIso.Nauty.Generation.Counted
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxFirstContext
import all HexGraphIso.Nauty.Sparse.MaxFirstResume
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxTarget
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxPrepare
import all HexGraphIso.Nauty.Sparse.MaxScope
import all HexGraphIso.Nauty.Sparse.MaxResume
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.Maximum
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Sparse.Orbits
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Generation.Counted
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The native orbit counter records distinct original target vertices
with checked carriers in the frozen target-cell stabilizer. -/
def Loop.Count (G : Hex.SparseGraph n) (tcLevel guide : Nat) (l : Loop n)
    (previous : Option Nat) (index : Nat) : Prop :=
  let c := l.cell G tcLevel
  Nauty.Generation.Counted (segN c.entry.lab c.tc c.len)
    (fun v => ∃ gamma, checkAutom (Graph.context G).g gamma = true ∧
      CellStab c.entry.ptn l.node.level c.entry.lab gamma ∧ gamma[v]! = guide) previous index

/-- The literal orbit-pointer test supplies the checked carrier for
each counted vertex. Its trace stabilization is read in the original
target frame, independently of the surviving mutable target set. -/
theorem Loop.mark {G : GraphIso.Sparse.Colored n k} {tcLevel guide tv index : Nat}
    {l : Loop n} {ready : State n} {previous : Option Nat}
    (h : (l.cell G.graph tcLevel).Valid G)
    (hc : l.Count G.graph tcLevel guide previous index) (ha : After previous tv)
    (hv : (l.cell G.graph tcLevel).vertices.mem tv = true)
    (ho : OrbitTrace G ready) (ht : TraceOk G ready)
    (hg : TraceFrame G l.node.level (l.cell G.graph tcLevel).entry ready) :
    l.Count G.graph tcLevel guide (some tv)
      (if ready.orbits[tv]! == guide then index + 1 else index) := by
  unfold Loop.Count at hc ⊢
  dsimp only at hc ⊢
  have hn : 0 < n := by have := h.positive; have := h.depth; omega
  apply hc.cellStep ha ((mem_windowSet.mp hv).2) (VSet.mem_lt hv)
    (labOk_of_reach h.ready.ok.labSize h.ready.ok.reach)
    h.ready.ok.ptnSize h.ready.ok.labSize (searchOk_end hn h.ready.ok h.positive) (ho ht)
  · exact fun gamma hm => (ht gamma (Array.mem_toList_iff.mp hm)).checked
  · exact fun gamma hm => hg.trace gamma (Array.mem_toList_iff.mp hm)

/-- Every live sweep cursor is eligible for the same frozen-cell count
rule, including after target-set filtering and label reordering. -/
theorem SweepInput.mark {G : GraphIso.Sparse.Colored n k} {tcLevel guide tv index : Nat}
    {l : Loop n} {bs fs : List Nat} {cell : VSet n} {st ready : State n}
    {parents : Parents n} {previous : Option Nat}
    (h : SweepInput G tcLevel l bs fs (some tv) cell st parents)
    (hc : l.Count G.graph tcLevel guide previous index) (ha : After previous tv)
    (ho : OrbitTrace G ready) (ht : TraceOk G ready)
    (hg : TraceFrame G l.node.level (l.cell G.graph tcLevel).entry ready) :
    l.Count G.graph tcLevel guide (some tv)
      (if ready.orbits[tv]! == guide then index + 1 else index) :=
  Loop.mark h.selected hc ha (h.subset tv (h.member tv rfl)) ho ht hg

/-- The actual later-sibling recursion retains witnesses for every
counter increment. Cursor order prevents counting a vertex twice, and
native trace stabilization justifies both visits and orbit skips. -/
theorem SweepInput.tail_counted {G : GraphIso.Sparse.Colored n k} {tcLevel fuel cfuel guide index : Nat}
    {l : Loop n} {bs fs : List Nat} {cursor previous : Option Nat} {cell : VSet n}
    {st : State n} {parents : Parents n}
    (h : SweepInput G tcLevel l bs fs cursor cell st parents)
    (hf : l.first = true) (heq : st.eqlevFirst = l.node.level)
    (hsame : l.node.level < st.allsamelevel) (hbudget : n ≤ l.node.level + fuel)
    (hpast : Generic.Past l.first guide cursor)
    (hc : l.Count G.graph tcLevel guide previous index)
    (ha : ∀ v, cursor = some v → After previous v) :
    ∃ last, l.Count G.graph tcLevel guide last
      (Generic.sweep l.first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel l.node.level
        (l.cell G.graph tcLevel).numcells (l.cell G.graph tcLevel).tc guide cursor cell index st).2.1 := by
  induction cfuel generalizing bs cursor cell index st previous with
  | zero =>
    cases cursor <;> rw [Generic.sweep] <;> exact ⟨previous, hc⟩
  | succ cfuel ih =>
    cases cursor with
    | none => rw [Generic.sweep]; exact ⟨previous, hc⟩
    | some tv =>
      have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
      let p := l.parent G.graph tcLevel st bs cell tv
      let ch := p.child G.graph tcLevel
      let raw := Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel ch.level ch.numcells ch.entry
      let left := (policy (n := n)).leaveChild tv raw.2
      let back := p.back G.graph tcLevel fuel
      let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
          level numcells tc tv1 cursor cell index st
      have hfirst : (l.first && tv == guide) = false := by
        have := hpast hf tv rfl
        simp only [hf, Bool.true_and, beq_eq_false_iff_ne]
        omega
      have hafter : ∀ v, cell.nextElem (some tv) = some v → After (some tv) v := by
        intro v hv
        have hb := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at hb
        change tv < v
        omega
      have hpast' : Generic.Past l.first guide (cell.nextElem (some tv)) := by
        intro _ v hv
        have := hpast hf tv rfl
        have hh := hafter v hv
        change tv < v at hh
        omega
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [hfirst, Bool.false_eq_true, ite_false, Id.run_pure, apply_ite Id.run,
        apply_ite Prod.fst, apply_ite Prod.snd]
      split
      · have hv := h.member tv rfl
        have hp : p.Valid G tcLevel := h.parent hv
        have hch := h.child rfl
        have hlen : ch.codes.length = l.node.level := by
          change (l.node.codes ++ [_]).length = l.node.level
          simp only [List.length_append, List.length_singleton, h.frame.length]
        have hmax := node_max G tcLevel fuel ch bs fs (parents.push p) hch (by rw [hlen]; exact hbudget)
        have hret : raw.1 = .unwind l.node.level false := h.visit_return hf heq hsame hbudget
        have hcovered : Covers (ch.key G.graph tcLevel) (State.best G.graph raw.2) := by
          have hh := hmax.coverage
          change ExitCover _ _ l.node.level _ raw.1 at hh
          rw [hret] at hh
          simpa only [ExitCover, ↓reduceIte] using hh.2
        obtain ⟨ds, hr, resumed⟩ := Scope.receive (p := p) h.scope hp h.codes h.machine
          h.recorded h.route hbudget
        have hmax' : MaxResult ((l.cell G.graph tcLevel).child l.first st tv |>.key G.graph tcLevel)
            (State.key G.graph bs ((l.cell G.graph tcLevel).child l.first st tv).entry)
            (State.best G.graph raw.2) l.node.level
            (Max.Witness G tcLevel (parents.push p).frames) (.unwind l.node.level false) := by
          change MaxResult (ch.key G.graph tcLevel) (State.key G.graph bs ch.entry)
            (State.best G.graph raw.2) (ch.level - 1) _ _
          rw [← hret]
          exact hmax
        have hcover := h.cover.received h.selected h.effect h.codes.ready (h.subset tv hv) hmax'
        have hbackRead : State.best G.graph back = State.key G.graph ds back := by
          have hh : State.best G.graph back = State.best G.graph raw.2 :=
            recover_best G.graph (n + 2) l.node.level left
          rw [hh, hr.read]
          exact (recover_key G.graph ds (n + 2) l.node.level left).symm
        have hbRead : State.best G.graph back = State.best G.graph raw.2 :=
          recover_best G.graph (n + 2) l.node.level left
        rw [← hbRead, hbackRead] at hcover
        have hs := h.recovered rfl hr resumed hcovered (fun _ hv => hv) hcover
        have heqBack : back.eqlevFirst = l.node.level := by
          have he := recover_eqlev (n + 2) l.node.level left
          change back.eqlevFirst = min raw.2.eqlevFirst l.node.level at he
          rw [he]
          apply Nat.min_eq_right
          have hb := Generic.node_bounded (firstFloor (.ofGraph G.graph) (n + 2) tcLevel l.node.level)
            fuel ch.level ch.numcells ch.entry (by change l.node.level < l.node.level + 1; omega)
            (show l.node.level ≤ ch.entry.allsamelevel ∧ l.node.level ≤ ch.entry.eqlevFirst from ?_)
          · exact hb.2
          · dsimp only [ch, p, Parent.child, Loop.parent]
            rw [hf]
            exact ⟨Nat.le_of_lt hsame, Nat.le_of_eq heq.symm⟩
        have hsameBack : l.node.level < back.allsamelevel := by
          have he := recover_same (n + 2) l.node.level left
          change back.allsamelevel = raw.2.allsamelevel at he
          rw [he, node_same]
          dsimp only [ch, p, Parent.child, Loop.parent]
          rw [hf]
          exact hsame
        have hframe := (hs.self hf).freeze hs.effect hs.selected.ready hs.codes.ready hn h.frame.positive
        have hmark := h.mark hc (ha tv rfl) hs.orbits hs.codes.trace hframe
        have hnext := ih hs heqBack hsameBack hpast' hmark hafter
        change ∃ last, l.Count G.graph tcLevel guide last
          (Generic.advance (n + 2) next l.first l.node.level (l.cell G.graph tcLevel).numcells
            (l.cell G.graph tcLevel).tc guide tv cell index left raw.1).2.1
        rw [hret]
        unfold Generic.advance Generic.resume
        simp only [Nat.lt_irrefl, ite_false, Bool.false_eq_true, hf, Bool.not_true,
          Bool.false_and, Bool.true_and, Id.run_pure]
        rw [show (policy (n := n)).recover (n + 2) l.node.level left = back from rfl]
        change ∃ last, l.Count G.graph tcLevel guide last
          (next true l.node.level (l.cell G.graph tcLevel).numcells (l.cell G.graph tcLevel).tc
            guide (cell.nextElem (some tv)) cell (if back.orbits[tv]! == guide then index + 1 else index) back).2.1
        simpa only [hf, next] using hnext
      · rename_i hskip
        have hs : (!l.first || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hskip
        have hframe := (h.self hf).freeze h.effect h.selected.ready h.codes.ready hn h.frame.positive
        have hmark := h.mark hc (ha tv rfl) h.orbits h.codes.trace hframe
        have hnext := ih (h.skipped hs) heq hsame hpast' hmark hafter
        simpa only [hf, Bool.true_and, policy, Generic.Policy.orbit] using hnext

/-- The complete native first sweep counts only distinct original
vertices carried to its guide. The guiding child's mark and every later
increment use the actual emitted trace and recovered state. -/
theorem FirstInput.counted {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel tv last : Nat} {f : Frame n} {leaf : State n} {parents : Parents n}
    (h : FirstInput G tcLevel f parents)
    (hi : (visit (.ofGraph G.graph) f.level f.numcells f.entry).1 < n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true f.level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel f.level f.numcells f.entry).2.2.2.2).orbits[tv]! = tv)
    (path : let p := f.firstParent G.graph tcLevel [] tv
      let ch := p.child G.graph tcLevel
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel ch.level ch.numcells ch.entry last leaf)
    (hf : n ≤ f.level + fuel) :
    let l : Loop n := ⟨f, true⟩
    let c := l.cell G.graph tcLevel
    let p := f.firstParent G.graph tcLevel [] tv
    ∃ previous, l.Count G.graph tcLevel tv previous
      (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        f.level c.numcells p.tc tv (some tv) p.cell 0 p.state).2.1 := by
  let l : Loop n := ⟨f, true⟩
  let p := f.firstParent G.graph tcLevel [] tv
  let back := p.firstBack G.graph tcLevel fuel
  obtain ⟨bs, fs, hs, heq, hsame, hcall⟩ := h.suffix hi htv horbit path hf
  have hn : 0 < n := by have := h.entry.frame.positive; have := h.entry.frame.depth; omega
  have hselected := l.selected (tcLevel := tcLevel) h.entry.frame hi (by intro he; cases he)
  have hm : (l.cell G.graph tcLevel).vertices.mem tv = true := by
    rw [← hselected.2]
    exact VSet.nextElem_mem htv
  have hframe := (hs.self rfl).freeze hs.effect hs.selected.ready hs.codes.ready hn h.entry.frame.positive
  have hinit : l.Count G.graph tcLevel tv none 0 := Nauty.Generation.Counted.start _ _
  have hmark := Loop.mark hs.selected hinit (show After none tv from trivial) hm hs.orbits hs.codes.trace hframe
  have hafter : ∀ v, p.cell.nextElem (some tv) = some v → After (some tv) v := by
    intro v hv
    have hb := (VSet.nextElem_eq_some_iff.mp hv).2.1
    change tv + 1 ≤ v at hb
    change tv < v
    omega
  have hpast : Generic.Past l.first tv (p.cell.nextElem (some tv)) := fun _ v hv => hafter v hv
  have hcount := hs.tail_counted (cfuel := n) rfl heq hsame hf hpast hmark hafter
  dsimp only
  rw [hcall]
  exact hcount

/-- Reaching the original target size supplies a checked stabilizing
carrier for every original vertex, regardless of later target filtering. -/
theorem Loop.Count.full {G : Hex.SparseGraph n} {tcLevel guide index : Nat} {l : Loop n}
    {previous : Option Nat} (h : l.Count G tcLevel guide previous index)
    (hfull : (l.cell G tcLevel).len ≤ index) :
    ∀ v ∈ segN (l.cell G tcLevel).entry.lab (l.cell G tcLevel).tc (l.cell G tcLevel).len,
      ∃ gamma, checkAutom (Graph.context G).g gamma = true ∧
        CellStab (l.cell G tcLevel).entry.ptn l.node.level (l.cell G tcLevel).entry.lab gamma ∧
        gamma[v]! = guide := by
  unfold Loop.Count at h
  exact h.full (by rw [segN_length]; exact hfull)

end Hex.GraphIso.Nauty.Sparse.Max
