/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.TraceNode
import all HexGraphIso.Nauty.Sparse.CheapHistory
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

theorem prepareFirst_workSize (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2.workperm.size = st.workperm.size :=
  chooseTarget_workSize true g tcLevel level (visit g level numcells st).1
    (recordFirst level (visit g level numcells st).2.1 (visit g level numcells st).2.2)

/-- A sound first-child trace establishes every invariant for the actual
recovered parent and all later siblings, using its executed first path. -/
theorem firstChild_trace {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel level numcells tv last : Nat} {st leaf : State n}
    (hn : 0 < n) (hl : 1 ≤ level) (hi : NodeInv G level numcells st)
    (hshape : FirstShape G.graph level numcells st)
    (ht : n < st.firsttc.size) (hc : n + 1 < st.firstcode.size)
    (hb : st.canong.toRows = (Graph.ofGraph G.graph).blank) (hw : st.workperm.size = n)
    (hopen : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).1 ≠ n)
    (htv : (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.1.nextElem none = some tv)
    (horbit : (cheapCheck true level
      (Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st).2.2.2.2).orbits[tv]! = tv)
    (hpath : let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      Generic.FirstPath (.ofGraph G.graph) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2)) last leaf)
    (htrace : let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      TraceOk G (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
        ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2) :
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1)
      ((policy (n := n)).child true level r.2.1.toNat tv (cheapCheck true level r.2.2.2.2))).2
    let result := (policy (n := n)).recover (n + 2) level
      ((policy (n := n)).leaveChild tv (afterChildFirst level tv out))
    TraceReady G tcLevel level r.1 result ∧ CheapRecorded level r.2.1.toNat result := by
  let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
  let ready := cheapCheck true level r.2.2.2.2
  let ch := (policy (n := n)).child true level r.2.1.toNat tv ready
  let out := (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch).2
  let left := (policy (n := n)).leaveChild tv (afterChildFirst level tv out)
  have hp := hi.prepare (tcLevel := tcLevel) hn hl
  have hready := hp.1.cheap true
  have htarget := hp.2.of_out hready.frame.effect
  have hmem := VSet.nextElem_mem htv
  have hch := hready.ready.child hn hl true htarget hmem
  have hblank : ch.canong.toRows = (Graph.ofGraph G.graph).blank := by
    change ready.canong.toRows = _
    unfold ready cheapCheck
    split <;> exact (prepareFirst_rows (.ofGraph G.graph) tcLevel level numcells st).trans hb
  have hwork : ch.workperm.size = n := by
    change ready.workperm.size = n
    unfold ready cheapCheck
    split <;> exact (prepareFirst_workSize (.ofGraph G.graph) tcLevel level numcells st).trans hw
  have hs := firstPath_saved hn (by omega) hch hpath hblank hwork
  have ho := node_frame G hn true tcLevel fuel (level + 1) (r.1 + 1) ch (by omega) hch
  have hf := hready.ready.child_frame hn hl true htarget hmem
    (by simpa only [Nat.add_sub_cancel] using ho)
  have hr := hready.ready.recover hn hl ((hf.afterChild level tv).leave tv)
  have hh := firstChild_history hn hl hi hshape ht hc hopen htv horbit hpath
  refine ⟨⟨hr.1, ((hs.afterChild level tv).leave tv).recover (n + 2) level,
    ((htrace.afterChild level tv).leave tv).recover (n + 2) level, ?_, hh⟩, ?_⟩
  · have he := (gcaPolicy (.ofGraph G.graph) (n + 2) tcLevel).recover level left
    change ((policy (n := n)).recover (n + 2) level left).gcaFirst = level at he
    exact Nat.le_of_eq he
  · intro _ _
    exact firstChild_target hn hl hi ht hopen hpath

/-- A sound child trace and a proved recovered sweep frame suffice for
every resume or nonlocal exit, including short and long target filtering. -/
theorem trace_advance (G : GraphIso.Sparse.Colored n k) (hn : 0 < n)
    (tcLevel fuel cfuel level numcells tc tv1 tv index : Nat) (first : Bool)
    (cell : VSet n) (st : State n) (exit : Generic.Exit) (hl : 1 ≤ level)
    (htrace : TraceOk G st)
    (h : TraceReady G tcLevel level numcells ((policy (n := n)).recover (n + 2) level st))
    (ht : Generic.Target State.frame level tc cell ((policy (n := n)).recover (n + 2) level st))
    (hrecord : CheapRecorded level tc ((policy (n := n)).recover (n + 2) level st))
    (hpast : ∀ smaller : VSet n, Generic.Past first tv1 (smaller.nextElem (some tv))) :
    TraceOk G (Generic.advance (n + 2)
      (fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel
          level numcells tc tv1 cursor cell index st)
      first level numcells tc tv1 tv cell index st exit).2.2 := by
  let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
    Generic.sweep first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st
  have hcontinue : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) → ∀ index,
      TraceOk G (next first level numcells tc tv1 (smaller.nextElem (some tv)) smaller index
        ((policy (n := n)).recover (n + 2) level st)).2.2 := by
    intro smaller hs index
    exact trace_sweep G hn tcLevel fuel (node_trace G hn tcLevel fuel) cfuel first level numcells tc tv1 index
      _ smaller _ hl h (ht.subset hs) (fun _ hv => VSet.nextElem_mem hv) (hpast smaller) hrecord
  have hresume : ∀ smaller, (∀ v, smaller.mem v = true → cell.mem v = true) →
      TraceOk G (Generic.resume (n + 2) next first level numcells tc tv1 tv smaller index st).2.2 := by
    intro smaller hs
    unfold Generic.resume
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact hcontinue _ (fun _ hv => hs _ (Nauty.longprune_subset hv)) _
    · exact hcontinue smaller hs _
  cases exit with
  | fuel => exact htrace
  | done => exact hresume cell (fun _ hv => hv)
  | unwind target short =>
    unfold Generic.advance
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
    split
    · exact htrace
    · split
      · exact hresume _ (fun _ hv => Nauty.shortprune_subset (st := st.frame) hv)
      · exact hresume cell (fun _ hv => hv)

/-- The first descent seeds every later sibling's admission history, so
its full production call preserves trace soundness without any generator
validity premise for work performed by descendants. -/
theorem firstPath_trace {G : GraphIso.Sparse.Colored n k} (hn : 0 < n)
    {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hl : 1 ≤ level) (hi : NodeInv G level numcells st) (hshape : FirstShape G.graph level numcells st)
    (htsize : n < st.firsttc.size) (hcsize : n + 1 < st.firstcode.size)
    (hblank : st.canong.toRows = (Graph.ofGraph G.graph).blank) (hwork : st.workperm.size = n)
    (htrace : TraceOk G st) :
    TraceOk G (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    have ht := (((htrace.visit level numcells).record level
      (visit (.ofGraph G.graph) level numcells st).2.1).target true tcLevel level
      (visit (.ofGraph G.graph) level numcells st).1).terminal level
    unfold Generic.prepareFirst at hdisc
    dsimp only at hdisc
    rw [Generic.node]
    unfold Generic.nodeStep
    dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
      Generic.Policy.chooseTarget, Generic.Policy.firstterminal] at hdisc ⊢
    simpa only [ite_true, hdisc, beq_self_eq_true, Id.run_pure] using ht
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let ready := cheapCheck true level r.2.2.2.2
    let ch := (policy (n := n)).child true level r.2.1.toNat tv ready
    let raw := Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch
    let left := (policy (n := n)).leaveChild tv (afterChildFirst level tv raw.2)
    obtain ⟨hr, ht⟩ := hi.prepare (tcLevel := tcLevel) hn hl
    have hready := hr.cheap true
    have htarget := ht.of_out hready.frame.effect
    have hmem := VSet.nextElem_mem htv
    have hch := hready.ready.child hn hl true htarget hmem
    have hs := hshape.child hi hn hl hmem
    have hct : n < ch.firsttc.size := by
      change n < ready.firsttc.size
      unfold ready cheapCheck
      split
      all_goals rw [(prepareFirst_store (.ofGraph G.graph) tcLevel level numcells st).2, Array.size_set!]
      all_goals exact htsize
    have hcc : n + 1 < ch.firstcode.size := by
      change n + 1 < ready.firstcode.size
      unfold ready cheapCheck
      split
      all_goals rw [(prepareFirst_store (.ofGraph G.graph) tcLevel level numcells st).1, Array.size_set!]
      all_goals exact hcsize
    have hcb : ch.canong.toRows = (Graph.ofGraph G.graph).blank := by
      change ready.canong.toRows = _
      unfold ready cheapCheck
      split <;> exact (prepareFirst_rows (.ofGraph G.graph) tcLevel level numcells st).trans hblank
    have hcw : ch.workperm.size = n := by
      change ready.workperm.size = n
      unfold ready cheapCheck
      split <;> exact (prepareFirst_workSize (.ofGraph G.graph) tcLevel level numcells st).trans hwork
    have hcp : TraceOk G ch :=
      (((((htrace.visit level numcells).record level (visit (.ofGraph G.graph) level numcells st).2.1).target
        true tcLevel level (visit (.ofGraph G.graph) level numcells st).1).cheap true level).child
        true level r.2.1.toNat tv)
    have hchild : TraceOk G raw.2 := ih (by omega) hch hs hct hcc hcb hcw hcp
    have hback := firstChild_trace hn hl hi hshape htsize hcsize hblank hwork hopen htv horbit tail hchild
    have ho := node_frame G hn true tcLevel fuel (level + 1) (r.1 + 1) ch (by omega) hch
    have hf := hready.ready.child_frame hn hl true htarget hmem
      (by simpa only [Nat.add_sub_cancel] using ho)
    have hrestore := (hready.ready.recover hn hl ((hf.afterChild level tv).leave tv)).2
    have hadv := trace_advance G hn tcLevel fuel n level r.1 r.2.1.toNat tv tv 0 true r.2.2.1 left raw.1 hl
      ((hchild.afterChild level tv).leave tv) hback.1 (htarget.of_out hrestore.effect) hback.2 (by
        intro smaller _ v hv
        have hv := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at hv
        omega)
    have hsweep : TraceOk G (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 ready).2.2 := by
      have horbit' : Generic.Policy.orbit (n := n) ready tv = tv := horbit
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [Bool.not_true, horbit', beq_self_eq_true, Bool.or_true, Bool.and_self, ite_true]
      exact hadv
    rw [Generic.node]
    unfold Generic.nodeStep
    change TraceOk G (Id.run do
      let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
      if r.1 == n then
        return (.unwind (level - 1) false, Generic.Policy.firstterminal (n := n) level r.2.2.2.2)
      let s := Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
        level r.1 r.2.1.toNat ((r.2.2.1.nextElem none).getD 0) (r.2.2.1.nextElem none) r.2.2.1 0
        (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2)
      match s.1 with
      | .done => return (.unwind (level - 1) false,
          Generic.Policy.afterSweep (n := n) true level r.2.2.2.1 s.2.1 s.2.2)
      | _ => return (s.1, s.2.2)).2
    simp only [beq_eq_false_iff_ne.mpr hopen, Bool.false_eq_true, ite_false, htv, Option.getD_some]
    generalize he : Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
      level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0
      (Generic.Policy.cheapCheck (n := n) true level r.2.2.2.2) = result at hsweep ⊢
    obtain ⟨exit, index, out⟩ := result
    cases exit with
    | fuel => exact hsweep
    | unwind => exact hsweep
    | done => exact hsweep.afterSweep true level r.2.2.2.1 index

end Hex.GraphIso.Nauty.Sparse
