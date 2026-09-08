/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Generation.Matching
public import HexGraphIso.Nauty.Policy.ReferenceSweep
import all HexGraphIso.Nauty.Policy.ReferenceSweep
import all HexGraphIso.Nauty.Policy.ReferenceReturn
import all HexGraphIso.Nauty.Policy.FirstWitness
import all HexGraphIso.Nauty.Policy.FirstBounds
import all HexGraphIso.Nauty.Policy.MaxReturnTrace
import all HexGraphIso.Nauty.Policy.MaxRestore
import all HexGraphIso.Nauty.Policy.MaxResume
import all HexGraphIso.Nauty.Policy.MaxReceive
import all HexGraphIso.Nauty.Policy.MaxEntry
import all HexGraphIso.Nauty.Policy.MaxContract
import all HexGraphIso.Nauty.Policy.MaxContext
import all HexGraphIso.Nauty.Policy.EarlyReturn
import all HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine.Max

variable {n k : Nat}

/-- An actual off-path sweep containing a matching reference returns
emitted evidence. The child premise is restricted to the actual smaller
calls; reception and both workspace filters preserve reference absence. -/
theorem SweepInput.reference {G : Colored n k} {tcLevel fuel cfuel boundary : Nat}
    {level numcells tc tv1 index : Nat} {cursor : Option Nat} {cell : VSet n}
    {st : Search n} {l : Loop n} {bs fs : List Nat} {parents : Parents n}
    (h : SweepInput G { g := rowsOf G } tcLevel fuel cfuel false level numcells tc tv1 cursor
      cell index st l bs fs parents)
    (hn : (contract G tcLevel).nodeValid fuel
      (Generic.nodeCall { g := rowsOf G } (n + 2) tcLevel fuel))
    {R : RefineSt n} {targets : List Nat} {key : Key n}
    (hit : IterOk { g := rowsOf G } level R)
    (hlab : R.lab = (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.lab)
    (hptn : R.ptn = (l.prepare { g := rowsOf G } tcLevel).2.2.2.2.ptn)
    (hboundary : level < boundary)
    (hvisit : ∀ {cfuel tv index cell st bs fs},
      SweepInput G { g := rowsOf G } tcLevel fuel cfuel false level numcells tc tv1 (some tv)
        cell index st l bs fs parents →
      Generation.Matches { g := rowsOf G } (level + 1) st.view targets key →
      st.eqlevFirst = level → boundary ≤ st.allsamelevel → st.gcaFirst < level →
      ∀ o, o < (l.prepare { g := rowsOf G } tcLevel).2.2.2.1 → R.lab[tc + o]! = tv →
      Generation.ChildPath { g := rowsOf G } tcLevel boundary level R tc targets key o →
      let out := Engine.node false { g := rowsOf G } (n + 2) tcLevel fuel
        (level + 1) (numcells + 1) (child false level tc tv st)
      ∀ target short, out.1 = .unwind target short → RefReturn { g := rowsOf G } target out.2)
    {previous : Option Nat}
    (hnext : cell.nextElem previous = cursor)
    (hcover : Generation.PathCover { g := rowsOf G } tcLevel boundary level R tc
      (l.prepare { g := rowsOf G } tcLevel).2.2.2.1 targets key cell previous)
    (hocc : ∃ o, o < (l.prepare { g := rowsOf G } tcLevel).2.2.2.1 ∧
      Generation.ChildPath { g := rowsOf G } tcLevel boundary level R tc targets key o)
    (hpast : Generation.CanonPast level tc previous st.view)
    (hm : Generation.Matches { g := rowsOf G } (level + 1) st.view targets key)
    (heq : st.eqlevFirst = level) (hsame : boundary ≤ st.allsamelevel)
    (hguide : st.gcaFirst < level) (hcheap : level < st.noncheaplevel) :
    ∃ target short out,
      Engine.sweep false { g := rowsOf G } (n + 2) tcLevel fuel cfuel
        level numcells tc tv1 cursor cell index st = (.unwind target short, out) ∧
      target < level ∧ RefReturn { g := rowsOf G } target out.2 := by
  induction cfuel generalizing cursor cell index st bs fs previous with
  | zero =>
    cases cursor with
    | none =>
      obtain ⟨o, ho, hp⟩ := hocc
      exact (hcover.finish hnext o ho hp).elim
    | some tv =>
      have hh := h.cursor_fuel tv rfl
      have ht := VSet.mem_lt (h.cursor_mem tv rfl)
      omega
  | succ cfuel ih =>
    cases cursor with
    | none =>
      obtain ⟨o, ho, hp⟩ := hocc
      exact (hcover.finish hnext o ho hp).elim
    | some tv =>
      let ctx : Ctx n := { g := rowsOf G }
      have hn0 : 0 < n := by have := h.node.positive; have := h.node.depth; omega
      obtain ⟨target, short, out, hcall⟩ := h.child_exit
        (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
      simp only [Bool.false_and] at hcall
      have hi := (h.push (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)).stored
        (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G)
      dsimp only [Parent.child] at hi
      rw [← h.first_eq, ← h.level_eq, ← h.numcells_eq, ← h.tc_eq] at hi
      simp only [Bool.false_and] at hi
      rw [hcall] at hi
      have hnoncheap : level < out.noncheaplevel := by
        have hh := node_noncheap (ctx := ctx) (inf := n + 2) (tcLevel := tcLevel) (fuel := fuel)
          (level := level + 1) (numcells := numcells + 1) (st := child false level tc tv st)
          (by omega : level < level + 1) hcheap
        rw [hcall] at hh
        exact hh
      have hsameOut : out.allsamelevel = st.allsamelevel := by
        have hh := node_same ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
          (child false level tc tv st)
        rw [hcall] at hh
        exact hh
      by_cases ht : target < level
      · have hr := node_early ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
          (child false level tc tv st) (congrArg Prod.fst hcall) (by omega)
        rw [hcall] at hr
        have href := hr.reference hn0 hi ht hnoncheap (by rw [hsameOut]; omega)
        refine ⟨target, short, (index, { out with fixedpts := out.fixedpts.erase tv }), ?_, ht, href.fixed _⟩
        rw [Engine.sweep]
        simp only [Bool.not_false, Bool.true_or, ↓reduceIte, Bool.false_and, hcall,
          Bool.false_eq_true, ht, Id.run_pure]
      · have hresult := h.child_result hn
        simp only [Bool.false_and] at hresult
        rw [hcall] at hresult
        have htarget : target ≤ level := hresult.coverage.1
        have he : target = level := by omega
        subst target
        let left := { out with fixedpts := out.fixedpts.erase tv }
        let ready := recoverLevels level (recoverPtn (n + 2) level left)
        let small := if short then shortprune cell left else cell
        let filtered := if tv == tv1 then Nauty.longprune small left.fixedpts left.autos else small
        have hc : Engine.node (false && tv == tv1) ctx (n + 2) tcLevel fuel
            (level + 1) (numcells + 1) (child false level tc tv st) = (.unwind level short, out) := hcall
        obtain ⟨hgen, hanc⟩ := h.received_generators hn hc
        obtain ⟨bs', fs', hs, _, _⟩ := h.received_input hn (by simp) hc hgen hanc
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and] at hs
        change SweepInput G ctx tcLevel fuel cfuel false level numcells tc tv1
          (filtered.nextElem (some tv)) filtered index ready l bs' fs' parents at hs
        have hadv := h.reference_visit hit hlab hptn hcover hpast hnext hguide hcall
          hi.canonical.1 (size_rowsOf G) (fun o ho hat href => by
            have hh := hvisit h hm heq hsame hguide o ho hat href level short (congrArg Prod.fst hcall)
            rw [hcall] at hh
            exact hh)
        have hf := h.reference_filters hit hlab hptn hadv
          (size_rowsOf G) (rowsOf_symm G) (rowsOf_loopless G) hc
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and] at hf
        change Generation.PathCover ctx tcLevel boundary level R tc (l.prepare ctx tcLevel).2.2.2.1
          targets key filtered (some tv) at hf
        have hp := h.canon_past hpast hnext
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hp
        rw [hcall] at hp
        change Generation.CanonPast level tc (some tv) ready.view at hp
        have hr : ready.reference = st.reference := by
          have hh := node_reference ctx (n + 2) tcLevel fuel (level + 1) (numcells + 1)
            (child false level tc tv st)
          rw [hcall] at hh
          exact ((referencePolicy ctx (n + 2) tcLevel).recover level left).trans hh
        have heq' : ready.eqlevFirst = level := by
          have hh := Generic.node_bounded (firstFloor ctx (n + 2) tcLevel level)
            fuel (level + 1) (numcells + 1) (child false level tc tv st) (by omega)
            (show level ≤ st.allsamelevel ∧ level ≤ st.eqlevFirst from ⟨by omega, by omega⟩)
          rw [← node_eq_generic, hcall] at hh
          rw [recover_eqlev]
          change min out.eqlevFirst level = level
          exact Nat.min_eq_right hh.2
        have hsame' : boundary ≤ ready.allsamelevel := by
          rw [recover_same]
          change boundary ≤ out.allsamelevel
          rwa [hsameOut]
        have hg' : ready.gcaFirst < level := by
          have hh := h.recovered_control
          simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte] at hh
          rw [hcall] at hh
          exact hh.2 trivial
        have hn' : level < ready.noncheaplevel := by
          rw [recover_noncheap]
          change level < if level < out.noncheaplevel then level + 1 else out.noncheaplevel
          rw [ite_eq_left hnoncheap]
          omega
        obtain ⟨t, s, result, he, htl, href⟩ := ih hs rfl hf hp
          (matches_reference hm hr) heq' hsame' hg' hn'
        refine ⟨t, s, result, ?_, htl, href⟩
        have hstep := (h.receive_call hn (by simp) hc
          (Generic.sweepCall ctx (n + 2) tcLevel fuel cfuel)).1
        unfold Generic.nodeCall Generic.sweepCall at hstep
        rw [sweep_eq_generic, Generic.sweep, hstep]
        simp only [Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
        rw [← sweep_eq_generic]
        dsimp only [ready, left, filtered, small] at he ⊢
        exact he

end Hex.GraphIso.Nauty.Engine.Max
