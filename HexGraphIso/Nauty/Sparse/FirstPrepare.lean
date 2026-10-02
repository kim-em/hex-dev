/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Reach
public import HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Policy.Generic.Leftmost
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Borrowing target scratch and saving the first target leaves the orbit
array untouched. This concerns the native sparse dispatch. -/
theorem chooseTarget_orbits (first : Bool) (g : Graph n)
    (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.orbits = st.orbits := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.orbits = st.orbits)
  mvcgen
  all_goals simp_all +zetaDelta

theorem prepareFirst_orbits (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (Generic.prepareFirst g tcLevel level numcells st).2.2.2.2.orbits = st.orbits := by
  unfold Generic.prepareFirst
  change (chooseTarget true g tcLevel level _ _).2.2.2.orbits = _
  rw [chooseTarget_orbits]
  rfl

/-- Every open first-path target contains a current vertex. The cache
agreement theorem supplies the exact workset used by the executable. -/
theorem Ready.first_nonempty {G : GraphIso.Sparse.Colored n k}
    {tcLevel level numcells : Nat} {st : State n}
    (h : Ready G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) (hc : numcells < n) :
    (chooseTarget true (.ofGraph G.graph) tcLevel level numcells st).2.1 ≠ VSet.empty := by
  have hp := isPerm_of_cellsReach h.ok.labSize hn h.ok.reach
  obtain ⟨label, hlabel⟩ := Label.ofArray?_exists hp
  have hend : st.ptn[n - 1]! ≤ level := by
    have he := searchOk_end hn h.ok hl
    change st.ptn[st.ptn.size - 1]! ≤ level at he
    have hs : st.ptn.size = n := h.ok.ptnSize
    rwa [hs] at he
  have hcount : bcount st.ptn level n < n := by
    have he : numcells = bcount st.ptn level n := h.ok.count
    omega
  have he := maketargetCached_eq G.graph st.lab st.ptn level tcLevel (-1) st.canong.scratch
    label hlabel h.ok.ptnSize hend h.scratch (Target.nonempty h.ok.ptnSize hend hcount)
  have hset := congrArg (fun t : Nat × VSet n × Nat => t.2.1) he
  have hv := maketargetcell_valid G.graph st.lab st.ptn level tcLevel (-1) hp h.ok.ptnSize hend hcount
  let tc := targetcell (.ofGraph G.graph) st.lab st.ptn level tcLevel (-1)
  have hne : (numcells != n) = true := bne_iff_ne.mpr (by omega)
  simp only [chooseTarget, hne, Bool.not_true, Bool.false_and, Bool.false_eq_true,
    ite_true, ite_false, Id.run_pure]
  rw [hset]
  refine mem_ne_empty (v := st.lab[tc]!) ?_
  rw [maketargetcell, mem_worksetOf, Bool.and_eq_true]
  have htc : tc < n := by
    have hh := hv.2.2
    have hn := hv.2.1
    change tc + _ ≤ n at hh
    omega
  refine ⟨decide_eq_true (cellsReach_lt h.ok.reach tc htc), ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨st.lab[tc]!, mem_segN_iff.mpr ⟨0, ?_, by rw [Nat.add_zero]⟩, by simp⟩
  have hb := cellEnd_ge (ptn := st.ptn) (level := level) (i := tc)
  change 0 < cellEnd st.ptn level tc + 1 - tc
  omega

/-- Preparation establishes an equitable parent and the actual target's
membership contract, starting with the production entry invariant. -/
theorem NodeInv.prepare {G : GraphIso.Sparse.Colored n k}
    {tcLevel level numcells : Nat} {st : State n}
    (h : NodeInv G level numcells st) (hn : 0 < n) (hl : 1 ≤ level) :
    let r := Generic.prepareFirst (.ofGraph G.graph) tcLevel level numcells st
    Ready G level r.1 r.2.2.2.2 ∧
      Generic.Target State.frame level r.2.1.toNat r.2.2.1 r.2.2.2.2 := by
  have hv := h.visit_ready hn hl
  have hr := (hv.record (visit (.ofGraph G.graph) level numcells st).2.1).ready
  exact ⟨(hr.target_frame true tcLevel).ready, hr.target hn hl true tcLevel⟩

end Hex.GraphIso.Nauty.Sparse
