/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.CodeAdvance
public import HexGraphIso.Nauty.Sparse.FirstRoute
public import HexGraphIso.Nauty.Sparse.FirstTrace
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse

private theorem firstPath_le {g : Graph n} {tcLevel fuel level numcells last : Nat} {st leaf : State n}
    (path : Generic.FirstPath g tcLevel fuel level numcells st last leaf) : level ≤ last := by
  induction path with
  | leaf => exact Nat.le_refl _
  | step _ _ _ _ ih => omega

/-- The actual first descent supplies settled comparisons to every
ancestor's later siblings. The leaf comparison is initialized separately
from its recorded native codes; recovery reads their exact ancestor prefix. -/
theorem firstPath_returned {G : GraphIso.Sparse.Colored n k} (hn : 0 < n)
    {tcLevel fuel level numcells last : Nat} {st leaf : State n} {fs : List Nat}
    (path : Generic.FirstPath (.ofGraph G.graph) tcLevel fuel level numcells st last leaf)
    (hl : 1 ≤ level) (hi : NodeInv G level numcells st) (hshape : FirstShape G.graph level numcells st)
    (htsize : n < st.firsttc.size) (hcsize : n + 1 < st.firstcode.size)
    (hblank : st.canong.toRows = (Graph.ofGraph G.graph).blank) (hwork : st.workperm.size = n)
    (htrace : TraceOk G st) (hfuel : n + 1 ≤ level + fuel)
    (hflen : fs.length = last) (hterminal : Comparison G.graph fs fs fs (firstterminal last leaf)) :
    ∃ bs, ReturnCodes G.graph (fs.take (level - 1)) bs fs
      (Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel level numcells st).2 := by
  induction path with
  | leaf fuel level numcells st hdisc =>
    have hr := (hterminal.returned (by change (0 : Int) ≤ 0; decide)).prefix
      (show fs.take (level - 1) <+: fs from ⟨_, List.take_append_drop _ _⟩)
    refine ⟨fs, ?_⟩
    unfold Generic.prepareFirst at hdisc hr
    dsimp only at hdisc
    rw [Generic.node]
    unfold Generic.nodeStep
    dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
      Generic.Policy.chooseTarget, Generic.Policy.firstterminal] at hdisc hr ⊢
    simpa only [ite_true, hdisc, beq_self_eq_true, Id.run_pure] using hr
  | @step fuel level numcells last st leaf tv hopen htv horbit tail ih =>
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    let ready := cheapCheck true level r.2.2.2.2
    let ch := (policy (n := n)).child true level r.2.1.toNat tv ready
    let raw := Generic.node true (.ofGraph G.graph) (n + 2) tcLevel fuel (level + 1) (r.1 + 1) ch
    let left := (policy (n := n)).leaveChild tv (afterChildFirst level tv raw.2)
    let back := (policy (n := n)).recover (n + 2) level left
    let cs := fs.take level
    have hlength : cs.length = level := by
      have hb := firstPath_le tail
      simp only [cs, List.length_take, hflen, Nat.min_eq_left (by omega : level ≤ last)]
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
    obtain ⟨bs, hchild⟩ := ih (by omega) hch hs hct hcc hcb hcw hcp (by omega) hflen hterminal
    have hchild' : ReturnCodes G.graph cs bs fs raw.2 := by
      simp only [Nat.add_sub_cancel] at hchild
      exact hchild
    have hchildtrace := firstPath_trace hn tail (by omega) hch hs hct hcc hcb hcw hcp
    have hback := firstChild_trace hn hl hi hshape htsize hcsize hblank hwork hopen htv horbit tail hchildtrace
    have hroute := firstChild_route hn hl hi htsize hcsize hopen htv horbit tail
    have hrecord := firstChild_recorded hn hl hi htsize hopen tail
    have hb : CodeReady G tcLevel level r.1 back := ⟨hback.1, hroute⟩
    have ho := node_frame G hn true tcLevel fuel (level + 1) (r.1 + 1) ch (by omega) hch
    have hframe := hready.ready.child_frame hn hl true htarget hmem
      (by simpa only [Nat.add_sub_cancel] using ho)
    have hrestore := (hready.ready.recover hn hl ((hframe.afterChild level tv).leave tv)).2
    have hbacktarget : Generic.Target State.frame level r.2.1.toNat r.2.2.1 back :=
      htarget.of_out hrestore.effect
    have hleft : ReturnCodes G.graph cs bs fs left := (hchild'.afterChild level tv).leave tv
    have hadv := codes_advance G hn tcLevel fuel n r.1 r.2.1.toNat tv tv 0 true cs bs fs r.2.2.1
      left raw.1 (by omega) hleft
      (by simpa only [hlength] using hb)
      (by simpa only [hlength] using hbacktarget)
      (by simpa only [hlength] using hback.2)
      (by simpa only [hlength] using hrecord)
      (by intro smaller _ v hv
          have hv := (VSet.nextElem_eq_some_iff.mp hv).2.1
          change tv + 1 ≤ v at hv
          omega)
      (by omega) (by omega)
    simp only [hlength] at hadv
    have hsweep : ∃ ds, ReturnCodes G.graph cs ds fs
        (Generic.sweep true (.ofGraph G.graph) (n + 2) tcLevel fuel (n + 1)
          level r.1 r.2.1.toNat tv (some tv) r.2.2.1 0 ready).2.2 := by
      have horbit' : Generic.Policy.orbit (n := n) ready tv = tv := horbit
      rw [Generic.sweep]
      unfold Generic.sweepStep
      simp only [Bool.not_true, horbit', beq_self_eq_true, Bool.or_true, Bool.and_self, ite_true]
      obtain ⟨ds, hr, _⟩ := hadv
      exact ⟨ds, hr⟩
    have hp : fs.take (level - 1) <+: cs := by
      have hp : cs.take (level - 1) <+: cs := ⟨_, List.take_append_drop _ _⟩
      simpa only [cs, List.take_take, Nat.min_eq_left (Nat.sub_le level 1)] using hp
    rw [Generic.node]
    unfold Generic.nodeStep
    change ∃ ds, ReturnCodes G.graph (fs.take (level - 1)) ds fs (Id.run do
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
    obtain ⟨ds, hr⟩ := hsweep
    cases exit with
    | fuel => exact ⟨ds, hr.prefix hp⟩
    | unwind => exact ⟨ds, hr.prefix hp⟩
    | done => exact ⟨ds, (hr.afterSweep true level r.2.2.2.1 index).prefix hp⟩

end Hex.GraphIso.Nauty.Sparse
