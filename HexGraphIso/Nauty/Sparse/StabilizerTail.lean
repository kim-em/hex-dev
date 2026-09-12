/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GeneratedVisit
public import HexGraphIso.Nauty.Sparse.FirstTail
public import HexGraphIso.Nauty.Sparse.ReferenceResume
public import HexGraphIso.Nauty.Sparse.OrbitMark
public import HexGraphIso.Nauty.Generation.Counter
import all HexGraphIso.Nauty.Sparse.MaxContext
import all HexGraphIso.Nauty.Sparse.MaxLoop
import all HexGraphIso.Nauty.Sparse.MaxCell
import all HexGraphIso.Nauty.Sparse.MaxFrame
import all HexGraphIso.Nauty.Sparse.MaxParent
import all HexGraphIso.Nauty.Sparse.MaxTrace
import all HexGraphIso.Nauty.Sparse.Orbits
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generated.Cover
import all HexGraphIso.Nauty.Policy.Generated.Trace
import all HexGraphIso.Nauty.Policy.Generic.Fuel
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty.Sparse.Max

/-- The executed sibling suffix counts every vertex of the guide's
true stabilizer orbit exactly once. Coverage uses the generators emitted
at each counter update, rather than generators discovered afterwards. -/
theorem SweepInput.index_tail {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel cfuel boundary index : Nat} {l : Loop n} {bs fs : List Nat}
    {cursor previous : Option Nat} {cell : VSet n} {st : State n} {parents : Parents n}
    {targets : List Nat} {key : Key n} {base : List (Fin n)} {guide : Fin n}
    [DecidablePred (Aut.Orbit G.toDense base guide)]
    (h : SweepInput G tcLevel l bs fs cursor cell st parents)
    (hf : l.first = true) (hbudget : n ≤ l.node.level + fuel)
    (hcursor : Generic.CursorFuel n cfuel cursor) (hpast : Generic.Past l.first guide.val cursor)
    (hm : Generation.Matches G.graph (l.node.level + 1) st targets key)
    (heq : st.eqlevFirst = l.node.level)
    (hboundary : l.node.level < boundary) (hsame : boundary ≤ st.allsamelevel) :
    let c := l.cell G.graph tcLevel
    let R := State.refined (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
    (∀ v : Fin n, Aut.Orbit G.toDense base guide v → ∀ o, o < c.len →
      R.lab[c.tc + o]! = v.val →
      Generation.ChildPath G.graph tcLevel boundary l.node.level R c.tc targets key o) →
    (∀ gamma, CellStab R.ptn l.node.level R.lab gamma → ∀ b ∈ base, gamma[b.val]! = b.val) →
    (∀ v, Aut.Orbit G.toDense base guide v → cell.mem v.val = true) →
    (∀ v, Aut.Orbit G.toDense base guide v → guide.val ≤ v.val) →
    cell.nextElem previous = cursor →
    Nauty.Generation.CanonPast l.node.level c.tc previous st →
    Nauty.Generation.Cover G.toDense st.generators base guide cell previous →
    st.firstlab[c.tc]! = guide.val →
    OrbitReplay st → Nauty.Generation.Counter (Aut.Orbit G.toDense base guide) previous index →
    (Generic.sweep l.first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel l.node.level
      c.numcells c.tc guide.val cursor cell index st).2.1 =
        (List.finRange n).countP (fun v => decide (Aut.Orbit G.toDense base guide v)) := by
  intro c R hmove hfixFrame hwindow hmin hnext hcanon hcover hfirst hreplay hcount
  induction cfuel generalizing bs cursor previous cell index st with
  | zero =>
    cases cursor with
    | none => rw [Generic.sweep]; exact hcount.finish hwindow hnext
    | some tv =>
      have := hcursor tv rfl
      have := VSet.mem_lt (h.member tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none => rw [Generic.sweep]; exact hcount.finish hwindow hnext
    | some tv =>
      have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
      let g := Graph.ofGraph G.graph
      let ch := (policy (n := n)).child l.first l.node.level c.tc tv st
      let raw := Generic.node false g (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1) ch
      let left := (policy (n := n)).leaveChild tv raw.2
      let back := (policy (n := n)).recover (n + 2) l.node.level left
      let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first g (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st
      let v : Fin n := ⟨tv, VSet.mem_lt (h.member tv rfl)⟩
      have orbit_eq (s : State n) (v : Nat) : (policy (n := n)).orbit s v = s.orbits[v]! := rfl
      have hchildFirst : (l.first && tv == guide.val) = false := by
        have := hpast hf tv rfl
        simp only [hf, Bool.true_and, beq_eq_false_iff_ne]
        omega
      have hpast' : Generic.Past l.first guide.val (cell.nextElem (some tv)) := by
        intro _ v hv
        have := hpast hf tv rfl
        have hh := (VSet.nextElem_eq_some_iff.mp hv).2.1
        change tv + 1 ≤ v at hh
        omega
      by_cases hg : (!l.first || st.orbits[tv]! == tv) = true
      · have hret : raw.1 = .unwind l.node.level false := h.visit_return hf heq (by omega) hbudget
        have hcall : Generic.node false g (n + 2) tcLevel fuel
            (l.node.level + 1) (c.numcells + 1) ch = (.unwind l.node.level false, raw.2) :=
          Prod.ext hret rfl
        obtain ⟨ds, hs⟩ := h.received (tv1 := guide.val) hbudget hcall
        simp only [hf, Bool.false_eq_true, ite_false, Bool.not_true, Bool.false_and] at hs
        change SweepInput G tcLevel l ds fs (cell.nextElem (some tv)) cell back parents at hs
        let nextIndex := if back.orbits[tv]! == guide.val then index + 1 else index
        have hstep : Generic.sweep l.first g (n + 2) tcLevel fuel (cfuel + 1) l.node.level
            c.numcells c.tc guide.val (some tv) cell index st =
            Generic.sweep l.first g (n + 2) tcLevel fuel cfuel l.node.level c.numcells c.tc guide.val
              (cell.nextElem (some tv)) cell nextIndex back := by
          rw [Generic.sweep]
          unfold Generic.sweepStep
          simp only [orbit_eq, hchildFirst, hg, Bool.false_eq_true, ite_false, ite_true, Id.run_pure]
          change Generic.advance (n + 2) next l.first l.node.level c.numcells c.tc guide.val tv cell index left raw.1 = _
          rw [hret]
          unfold Generic.advance Generic.resume
          simp only [Nat.lt_irrefl, ite_false, Bool.false_eq_true, hf, Bool.not_true,
            Bool.false_and, Bool.true_and, Id.run_pure]
          rfl
        have hrawBack : ∀ gamma ∈ raw.2.genTrace, gamma ∈ back.genTrace := fun gamma hm =>
          (tracePolicy g (n + 2) tcLevel gamma).recover l.node.level left hm
        have hsub : ∀ gamma ∈ st.genTrace, gamma ∈ back.genTrace := by
          intro gamma hm
          apply hrawBack
          exact node_contains false g (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1) ch
            ((tracePolicy g (n + 2) tcLevel gamma).child l.first l.node.level c.tc tv st hm)
        have hrawTrace : Generation.Realizes G back.generators raw.2.genTrace.toList :=
          (Generation.realized hs.codes.trace).mono (fun gamma hm =>
            Array.mem_toList_iff.mpr (hrawBack gamma (Array.mem_toList_iff.mp hm)))
        have hadv := h.generated_visit hf hbudget hm heq hsame hmove hfixFrame hnext hcanon
          (hcover.mono (State.generators_mono hsub)) hfirst hcall hrawTrace
        have hr : OrbitReplay back :=
          (orbitReplayPolicy g (n + 2) tcLevel).recover l.node.level left
            ((orbitReplayPolicy g (n + 2) tcLevel).leave tv raw.2
              (node_orbitReplay false g (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1) ch
                ((orbitReplayPolicy g (n + 2) tcLevel).child l.first l.node.level c.tc tv st hreplay)))
        have hframe := (hs.self hf).freeze hs.effect hs.selected.ready hs.codes.ready hn h.frame.positive
        have hfix : ∀ gamma ∈ back.genTrace, ∀ b ∈ base, gamma[b.val]! = b.val :=
          fun gamma hg => hfixFrame gamma (hframe.trace gamma hg)
        have hmark : (back.orbits[tv]! == guide.val) = true ↔ Aut.Orbit G.toDense base guide v := by
          rw [beq_iff_eq]
          exact hr.mark (tv := v) hs.codes.trace hs.orbits hadv (h.member tv rfl) hfix hmin
        have hcount' := hcount.advance hwindow hnext hmark
        have hreference : back.reference = st.reference := by
          have hh := node_reference g (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1) ch
          have hc : ch.reference = st.reference := by dsimp only [ch]; rw [hf]; rfl
          exact ((referencePolicy g (n + 2) tcLevel).recover l.node.level left).trans (hh.trans hc)
        have heqBack : back.eqlevFirst = l.node.level := by
          have he := recover_eqlev (n + 2) l.node.level left
          change back.eqlevFirst = min raw.2.eqlevFirst l.node.level at he
          rw [he]
          apply Nat.min_eq_right
          have hb := Generic.node_bounded (firstFloor g (n + 2) tcLevel l.node.level)
            fuel (l.node.level + 1) (c.numcells + 1) ch (by omega)
            (show l.node.level ≤ ch.allsamelevel ∧ l.node.level ≤ ch.eqlevFirst from ?_)
          · exact hb.2
          · dsimp only [ch]
            rw [hf]
            change l.node.level ≤ st.allsamelevel ∧ l.node.level ≤ st.eqlevFirst
            exact ⟨by omega, Nat.le_of_eq heq.symm⟩
        have hsameBack : boundary ≤ back.allsamelevel := by
          have he := recover_same (n + 2) l.node.level left
          change back.allsamelevel = raw.2.allsamelevel at he
          rw [he, node_same]
          dsimp only [ch]
          rw [hf]
          exact hsame
        have hcanonBack : Nauty.Generation.CanonPast l.node.level c.tc (some tv) back :=
          h.codes.ready.canon_past hn h.frame.positive l.first false h.target hcanon hnext
        have hfirstBack : back.firstlab[c.tc]! = guide.val := by
          have hh := congrArg (fun r : Array Nat × Array Int × Array Nat => r.2.2) hreference
          change back.firstlab = st.firstlab at hh
          rw [hh]
          exact hfirst
        rw [hstep]
        exact ih (index := nextIndex) hs (Generic.CursorFuel.next (hcursor tv rfl)) hpast'
          (hm.congr hreference) heqBack hsameBack hwindow rfl hcanonBack hadv hfirstBack hr hcount'
      · have hskip : (!l.first || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hg
        let nextIndex := if st.orbits[tv]! == guide.val then index + 1 else index
        have hstep : Generic.sweep l.first g (n + 2) tcLevel fuel (cfuel + 1) l.node.level
            c.numcells c.tc guide.val (some tv) cell index st =
            Generic.sweep l.first g (n + 2) tcLevel fuel cfuel l.node.level c.numcells c.tc guide.val
              (cell.nextElem (some tv)) cell nextIndex st := by
          rw [Generic.sweep]
          unfold Generic.sweepStep
          simp only [orbit_eq, hskip, Bool.false_eq_true, ite_false, Id.run_pure]
          rw [hf]
          simp only [Bool.true_and]
          rfl
        have hframe := (h.self hf).freeze h.effect h.selected.ready h.codes.ready hn h.frame.positive
        have hfix : ∀ gamma ∈ st.genTrace, ∀ b ∈ base, gamma[b.val]! = b.val :=
          fun gamma hg => hfixFrame gamma (hframe.trace gamma hg)
        have hadv := hcover.orbitSkip (tv := v) hnext (h.orbits h.codes.trace)
          (Generation.realized h.codes.trace)
          (fun gamma hg => hfix gamma (Array.mem_toList_iff.mp hg))
          (by simpa only [hf, Bool.not_true, Bool.false_or, beq_eq_false_iff_ne] using hskip)
        have hmark : (st.orbits[tv]! == guide.val) = true ↔ Aut.Orbit G.toDense base guide v := by
          rw [beq_iff_eq]
          exact hreplay.mark (tv := v) h.codes.trace h.orbits hadv (h.member tv rfl) hfix hmin
        have hcount' := hcount.advance hwindow hnext hmark
        rw [hstep]
        exact ih (index := nextIndex) (h.skipped hskip) (Generic.CursorFuel.next (hcursor tv rfl)) hpast'
          hm heq hsame hwindow rfl (hcanon.advance (nextElem_after hnext)) hadv hfirst hreplay hcount'

end Hex.GraphIso.Nauty.Sparse.Max
