/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ReferenceLoop
public import HexGraphIso.Nauty.Sparse.ReferencePrepare
public import HexGraphIso.Nauty.Sparse.SmallUniform
public import HexGraphIso.Nauty.Sparse.UniformReturn
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxEmit
import all HexGraphIso.Nauty.Sparse.MaxControl
import all HexGraphIso.Nauty.Sparse.Uniform
import all HexGraphIso.Nauty.Sparse.LeafPath
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- Every actual off-path node containing its matching reference returns
checked emitted evidence. The fuel induction discharges the smaller-child
premise of the native sweep theorem; cheap and boundary-uniform subtrees
use their proved literal reference emission. -/
theorem reference_complete (G : GraphIso.Sparse.Colored n k) (tcLevel : Nat) :
    ∀ fuel (f : Frame n) bs fs parents boundary targets key,
      NodeInput G tcLevel f bs fs parents → n < f.level + fuel →
      Generation.RefPath G.graph tcLevel boundary f.level
        (State.refined (.ofGraph G.graph) f.level f.numcells f.entry) targets key →
      Generation.Matches G.graph f.level f.entry targets key →
      f.entry.eqlevFirst = f.level - 1 → boundary ≤ f.entry.allsamelevel →
      ∀ target short,
        (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).1 =
          .unwind target short →
        RefReturn (Graph.context G.graph) target
          (Generic.node false (.ofGraph G.graph) (n + 2) tcLevel fuel f.level f.numcells f.entry).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro f bs fs parents boundary targets key h hf
    have := h.frame.depth
    omega
  | succ fuel ih =>
    intro f bs fs parents boundary targets key h hf href hm heq hsame target short hret
    let g := Graph.ofGraph G.graph
    let rs := State.refined g f.level f.numcells f.entry
    have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
    have hr : RefineSt.Ready G.graph f.level rs := h.frame.node.refined
    have hg : f.entry.gcaFirst < f.level := by have := h.counters; omega
    have emit : Generation.Uniform G.graph tcLevel f.level rs targets key →
        RefReturn (Graph.context G.graph) target
          (Generic.node false g (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).2 := by
      intro hu
      have he := uniform_reference (n + 2) tcLevel hn (fuel + 1) f.level f.numcells f.entry
        targets key h.frame.positive h.frame.node hu h.codes.saved.work h.codes.saved.first.2 hm heq hg hf
      dsimp only at he
      rw [hret] at he
      cases he.1
      apply RefReturn.first
      · rw [node_gca]
      · have hl := congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.2)
          (node_reference g (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry)
        change (Generic.node false g (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry).2.firstlab =
          f.entry.firstlab at hl
        rw [hl]
        exact he.2
    by_cases hb : boundary ≤ f.level
    · exact emit (href.uniform hr hb)
    have hocc := href.occurs
    by_cases hc : cheapautom rs.ptn f.level n = true
    · have hshape : NodeShape n f.level rs.ptn :=
        ((h.frame.node.visit_ready hn h.frame.positive).small hn h.frame.positive hc).shape
      exact emit (hocc.small hr hshape)
    cases href with
    | leaf label hd hp => exact emit (Generation.Uniform.leaf hr hd hp)
    | @step _ tc len o _ scratch rest tail hcell hrange hnon ho hscratch htarget hchild hu =>
      change IsCell rs.ptn f.level tc len at hcell
      have hnc : rs.numcells < n := by
        have hcount := hr.spec.count
        have hle := bcount_le rs.ptn f.level n
        by_cases he : rs.numcells = n
        · have hall : List.countP (fun q => decide (rs.ptn[q]! ≤ f.level)) (List.range n) =
              (List.range n).length := by
            rw [List.length_range]
            exact hcount.symm.trans he
          have hclosed := List.countP_eq_length.mp hall tc (List.mem_range.mpr (by omega))
          have hopen := hcell.2.2.1 tc (Nat.le_refl _) (by omega)
          simp only [decide_eq_true_eq] at hclosed
          omega
        · omega
      let l : Loop n := ⟨f, false⟩
      let p := l.prepare G.graph tcLevel
      let c := l.cell G.graph tcLevel
      let q := prepareOther g tcLevel f.level f.numcells f.entry
      have hprep := matching_prepare hn h.frame.positive h.frame.node hocc hm heq hnc
      have hclass : classify g f.level q.1 q.2.2.2.2.2 = (.internal, q.2.2.2.2.2) := hprep.1
      have hs := h.prepare (congrArg Prod.fst hclass)
      change SweepInput G tcLevel l bs fs (p.2.2.1.nextElem none) p.2.2.1 p.2.2.2.2 parents at hs
      have htc : c.tc = tc := by
        change q.2.2.1.toNat = tc
        rw [hprep.2.1]
        simpa using congrArg Int.toNat (hm.targets 0 (by simp))
      have hlen : c.len = len := by
        have hh : IsCell rs.ptn f.level c.tc c.len := hs.selected.window
        have hsize : 1 < c.len := hs.selected.size
        rw [htc] at hh
        rcases isCell_disjoint_or_eq hh hcell with hh | hh | hh
        · omega
        · omega
        · exact hh.2
      have hset : p.2.2.1 = windowSet n rs.lab c.tc c.len :=
        (l.selected h.frame hnc (fun _ => congrArg Prod.fst hclass)).2
      have hpreq : p.2.2.2.2.eqlevFirst = f.level := hprep.2.2
      have hpref : p.2.2.2.2.reference = f.entry.reference := by
        let v := visit g f.level f.numcells f.entry
        let compared := compareCodes f.level v.2.1 v.2.2
        exact ((referencePolicy g 0 tcLevel).cheap false f.level q.2.2.2.2.2).trans
          ((chooseTarget_reference g tcLevel f.level v.1 compared).trans
            ((referencePolicy g 0 tcLevel).compare f.level v.2.1 v.2.2))
      have hpsame : p.2.2.2.2.allsamelevel = f.entry.allsamelevel := by
        change (cheapCheck false f.level q.2.2.2.2.2).allsamelevel = f.entry.allsamelevel
        unfold cheapCheck
        split <;> change (chooseTarget false g tcLevel f.level
          (visit g f.level f.numcells f.entry).1
          (compareCodes f.level (visit g f.level f.numcells f.entry).2.1
            (visit g f.level f.numcells f.entry).2.2)).2.2.2.allsamelevel = _
        all_goals rw [target_same, compare_same]
        all_goals rfl
      have hptn : q.2.2.2.2.2.ptn = rs.ptn :=
        (chooseTarget_frame false g tcLevel f.level (visit g f.level f.numcells f.entry).1
          (compareCodes f.level (visit g f.level f.numcells f.entry).2.1
            (visit g f.level f.numcells f.entry).2.2)).2.1.trans (compareCodes_frame ..).2.1
      have hpark : f.level < p.2.2.2.2.noncheaplevel := by
        change f.level < (cheapCheck false f.level q.2.2.2.2.2).noncheaplevel
        unfold cheapCheck
        simp only [hptn, Bool.eq_false_iff.mpr hc, Bool.not_false, Bool.true_or,
          Bool.and_self, ite_true]
        omega
      have hvisit : ∀ {tv cell st bs}, SweepInput G tcLevel l bs fs (some tv) cell st parents →
          Generation.Matches G.graph (f.level + 1) st rest tail → st.eqlevFirst = f.level →
          boundary ≤ st.allsamelevel → ∀ j, j < c.len → c.entry.lab[c.tc + j]! = tv →
          Generation.ChildPath G.graph tcLevel boundary f.level rs c.tc rest tail j →
          let out := Generic.node false g (n + 2) tcLevel fuel (f.level + 1) (c.numcells + 1)
            ((policy (n := n)).child false f.level c.tc tv st)
          ∀ target short, out.1 = .unwind target short → RefReturn (Graph.context G.graph) target out.2 := by
        intro tv cell st bs hh hmatch heq' hsame' j hj hat hpath
        let parent := l.parent G.graph tcLevel st bs cell tv
        let ch := parent.child G.graph tcLevel
        have hi := hh.child rfl
        have href := hh.reference_child hj hat hpath
        have hmatch' : Generation.Matches G.graph ch.level ch.entry rest tail := hmatch.congr rfl
        exact ih ch bs fs (parents.push parent) boundary rest tail hi (by
          change n < f.level + 1 + fuel
          omega) href hmatch' (by change st.eqlevFirst = f.level + 1 - 1; omega) hsame'
      have hcover : Generation.PathCover G.graph tcLevel boundary f.level rs c.tc c.len
          rest tail p.2.2.1 none := by
        rw [hset]
        apply Generation.PathCover.start
        intro j hj
        exact perm_bound hr.spec.label (by have hb : c.tc + c.len ≤ n := hs.selected.range; omega)
      have hhas : ∃ j, j < c.len ∧ Generation.ChildPath G.graph tcLevel boundary f.level rs c.tc rest tail j := by
        refine ⟨o, by omega, ?_⟩
        rw [htc]
        exact (Generation.ChildPath.cached hr hcell hrange hnon ho hscratch).mpr hchild
      have hpast : Nauty.Generation.CanonPast f.level c.tc none p.2.2.2.2 := by
        apply Nauty.Generation.CanonPast.start
        have he := (f.otherParent_refs G.graph tcLevel bs 0).2.2.2
        change p.2.2.2.2.gcaCanon = f.entry.gcaCanon at he
        rw [he]
        exact h.counters.2.2
      have hloop := hs.reference (fuel := fuel) (cfuel := n + 1)
        (tv1 := (p.2.2.1.nextElem none).getD 0) (index := 0) rfl (by change n ≤ f.level + fuel; omega)
        (fun _ _ => by omega) (by change f.level < boundary; omega) hvisit rfl hcover hhas hpast
        (hm.tail.congr hpref) hpreq (by rw [hpsame]; exact hsame) hpark
      let swept := Generic.sweep false g (n + 2) tcLevel fuel (n + 1) f.level
        c.numcells c.tc ((p.2.2.1.nextElem none).getD 0) (p.2.2.1.nextElem none) p.2.2.1 0 p.2.2.2.2
      obtain ⟨t, s, hexit, _, hreturn⟩ := hloop
      change swept.1 = .unwind t s at hexit
      change RefReturn (Graph.context G.graph) t swept.2.2 at hreturn
      have hemit : f.emit G.graph tcLevel = (.done, q.2.2.2.2.2) := by
        change leafExit (classify g f.level q.1 q.2.2.2.2.2).1 f.level
          (classify g f.level q.1 q.2.2.2.2.2).2 = _
        rw [hclass]
        rfl
      have hcall : Generic.node false g (n + 2) tcLevel (fuel + 1) f.level f.numcells f.entry =
          (.unwind t s, swept.2.2) := by
        rw [Generic.node, f.sweep_step _ (congrArg Prod.fst hemit)]
        dsimp only
        rw [hemit]
        change (match swept.1 with | .done => _ | _ => (swept.1, swept.2.2)) = _
        rw [hexit]
      rw [hcall] at hret ⊢
      cases hret
      exact hreturn

end Hex.GraphIso.Nauty.Sparse.Max
