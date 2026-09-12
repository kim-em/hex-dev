/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.GeneratedVisit
public import HexGraphIso.Nauty.Sparse.FirstTail
public import HexGraphIso.Nauty.Sparse.ReferenceResume
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

/-- The complete native first-path sibling suffix covers the guide's
true stabilizer orbit in any group containing its emitted generators.
Actual child returns supply reference carriers; orbit skips use words in
the recorded trace, and the proof follows every literal cursor advance. -/
theorem SweepInput.generated_tail {G : GraphIso.Sparse.Colored n k}
    {tcLevel fuel cfuel boundary tv1 index : Nat} {l : Loop n} {bs fs : List Nat}
    {cursor previous : Option Nat} {cell : VSet n} {st : State n} {parents : Parents n}
    {targets : List Nat} {key : Key n} {gs : List (Perm n)} {base : List (Fin n)} {guide : Fin n}
    (h : SweepInput G tcLevel l bs fs cursor cell st parents)
    (hf : l.first = true) (hbudget : n ≤ l.node.level + fuel)
    (hcursor : Generic.CursorFuel n cfuel cursor) (hpast : Generic.Past l.first tv1 cursor)
    (hm : Generation.Matches G.graph (l.node.level + 1) st targets key)
    (heq : st.eqlevFirst = l.node.level)
    (hboundary : l.node.level < boundary) (hsame : boundary ≤ st.allsamelevel) :
    let c := l.cell G.graph tcLevel
    let R := State.refined (.ofGraph G.graph) l.node.level l.node.numcells l.node.entry
    (∀ v : Fin n, Aut.Orbit G.toDense base guide v → ∀ o, o < c.len →
      R.lab[c.tc + o]! = v.val →
      Generation.ChildPath G.graph tcLevel boundary l.node.level R c.tc targets key o) →
    (∀ gamma, CellStab R.ptn l.node.level R.lab gamma → ∀ b ∈ base, gamma[b.val]! = b.val) →
    cell.nextElem previous = cursor →
    Nauty.Generation.CanonPast l.node.level c.tc previous st →
    Nauty.Generation.Cover G.toDense gs base guide cell previous →
    st.firstlab[c.tc]! = guide.val →
    Generation.Realizes G gs
      (Generic.sweep l.first (.ofGraph G.graph) (n + 2) tcLevel fuel cfuel l.node.level
        c.numcells c.tc tv1 cursor cell index st).2.2.genTrace.toList →
    ∀ v, Aut.Orbit G.toDense base guide v → Nauty.Generation.Carries G.toDense gs base guide v := by
  intro c R hmove hfixFrame hnext hcanon hcover hfirst htrace
  induction cfuel generalizing bs cursor previous cell index st with
  | zero =>
    cases cursor with
    | none => exact hcover.finish hnext
    | some tv =>
      have := hcursor tv rfl
      have := VSet.mem_lt (h.member tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none => exact hcover.finish hnext
    | some tv =>
      have hn : 0 < n := by have := h.frame.positive; have := h.frame.depth; omega
      let g := Graph.ofGraph G.graph
      let ch := (policy (n := n)).child l.first l.node.level c.tc tv st
      let raw := Generic.node false g (n + 2) tcLevel fuel (l.node.level + 1) (c.numcells + 1) ch
      let left := (policy (n := n)).leaveChild tv raw.2
      let back := (policy (n := n)).recover (n + 2) l.node.level left
      let next : Generic.SweepFn (State n) n := fun first level numcells tc tv1 cursor cell index st =>
        Generic.sweep first g (n + 2) tcLevel fuel cfuel level numcells tc tv1 cursor cell index st
      have orbit_eq (s : State n) (v : Nat) : (policy (n := n)).orbit s v = s.orbits[v]! := rfl
      have hchildFirst : (l.first && tv == tv1) = false := by
        have := hpast hf tv rfl
        simp only [hf, Bool.true_and, beq_eq_false_iff_ne]
        omega
      have hpast' : Generic.Past l.first tv1 (cell.nextElem (some tv)) := by
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
        obtain ⟨ds, hs⟩ := h.received (tv1 := tv1) hbudget hcall
        simp only [hf, Bool.false_eq_true, ite_false, Bool.not_true, Bool.false_and] at hs
        change SweepInput G tcLevel l ds fs (cell.nextElem (some tv)) cell back parents at hs
        let nextIndex := if back.orbits[tv]! == tv1 then index + 1 else index
        have hstep : Generic.sweep l.first g (n + 2) tcLevel fuel (cfuel + 1) l.node.level
            c.numcells c.tc tv1 (some tv) cell index st =
            Generic.sweep l.first g (n + 2) tcLevel fuel cfuel l.node.level c.numcells c.tc tv1
              (cell.nextElem (some tv)) cell nextIndex back := by
          rw [Generic.sweep]
          unfold Generic.sweepStep
          simp only [orbit_eq, hchildFirst, hg, Bool.false_eq_true, ite_false, ite_true, Id.run_pure]
          change Generic.advance (n + 2) next l.first l.node.level c.numcells c.tc tv1 tv cell index left raw.1 = _
          rw [hret]
          unfold Generic.advance Generic.resume
          simp only [Nat.lt_irrefl, ite_false, Bool.false_eq_true, hf, Bool.not_true,
            Bool.false_and, Bool.true_and, Id.run_pure]
          rfl
        rw [hstep] at htrace
        have hrawTrace : Generation.Realizes G gs raw.2.genTrace.toList := by
          apply htrace.mono
          intro gamma hgamma
          have hg : gamma ∈ back.genTrace := (tracePolicy g (n + 2) tcLevel gamma).recover
            l.node.level left (Array.mem_toList_iff.mp hgamma)
          exact Array.mem_toList_iff.mpr (sweep_contains l.first g (n + 2) tcLevel fuel cfuel
            l.node.level c.numcells c.tc tv1 nextIndex _ cell back hg)
        have hadv := h.generated_visit hf hbudget hm heq hsame hmove hfixFrame hnext hcanon hcover
          hfirst hcall hrawTrace
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
        exact ih (index := nextIndex) hs (Generic.CursorFuel.next (hcursor tv rfl)) hpast'
          (hm.congr hreference) heqBack hsameBack rfl hcanonBack hadv hfirstBack htrace
      · have hskip : (!l.first || st.orbits[tv]! == tv) = false := Bool.eq_false_iff.mpr hg
        let nextIndex := if st.orbits[tv]! == tv1 then index + 1 else index
        have hstep : Generic.sweep l.first g (n + 2) tcLevel fuel (cfuel + 1) l.node.level
            c.numcells c.tc tv1 (some tv) cell index st =
            Generic.sweep l.first g (n + 2) tcLevel fuel cfuel l.node.level c.numcells c.tc tv1
              (cell.nextElem (some tv)) cell nextIndex st := by
          rw [Generic.sweep]
          unfold Generic.sweepStep
          simp only [orbit_eq, hskip, Bool.false_eq_true, ite_false, Id.run_pure]
          rw [hf]
          simp only [Bool.true_and]
          rfl
        rw [hstep] at htrace
        have hstTrace : Generation.Realizes G gs st.genTrace.toList := by
          apply htrace.mono
          intro gamma hgamma
          exact Array.mem_toList_iff.mpr (sweep_contains l.first g (n + 2) tcLevel fuel cfuel
            l.node.level c.numcells c.tc tv1 nextIndex _ cell st (Array.mem_toList_iff.mp hgamma))
        have hframe := (h.self hf).freeze h.effect h.selected.ready h.codes.ready hn h.frame.positive
        let v : Fin n := ⟨tv, VSet.mem_lt (h.member tv rfl)⟩
        have hadv := hcover.orbitSkip (tv := v) hnext (h.orbits h.codes.trace) hstTrace
          (fun gamma hg => hfixFrame gamma (hframe.trace gamma (Array.mem_toList_iff.mp hg)))
          (by simpa only [hf, Bool.not_true, Bool.false_or, beq_eq_false_iff_ne] using hskip)
        exact ih (index := nextIndex) (h.skipped hskip) (Generic.CursorFuel.next (hcursor tv rfl)) hpast'
          hm heq hsame rfl (hcanon.advance (nextElem_after hnext)) hadv hfirst htrace

end Hex.GraphIso.Nauty.Sparse.Max
