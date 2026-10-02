/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.LocalFrame
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Native classification preserves the partition and saved reference labels,
including branches that install canonical rows or scatter an automorphism. -/
theorem classify_frame (g : Graph n) (level numcells : Nat) (st : State n) :
    let out := (classify g level numcells st).2
    out.lab = st.lab ∧ out.ptn = st.ptn ∧ out.firstlab = st.firstlab ∧ out.canonlab = st.canonlab := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq]
  simp only [apply_ite SearchState.lab, apply_ite SearchState.ptn,
    apply_ite SearchState.firstlab, apply_ite SearchState.canonlab, ite_self]
  trivial

/-- Borrowing target scratch and recording target hints changes no partition
or saved label field in the actual sparse dispatch. -/
theorem chooseTarget_frame (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    let out := (chooseTarget first g tcLevel level numcells st).2.2.2
    out.lab = st.lab ∧ out.ptn = st.ptn ∧ out.firstlab = st.firstlab ∧ out.canonlab = st.canonlab := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.lab = st.lab ∧ out.2.2.2.ptn = st.ptn ∧
    out.2.2.2.firstlab = st.firstlab ∧ out.2.2.2.canonlab = st.canonlab)
  mvcgen
  all_goals simp_all +zetaDelta

namespace Ready

variable {G : GraphIso.Sparse.Colored n k} {level numcells : Nat} {st : State n}

theorem classify (h : Ready G level numcells st) :
    Local G level numcells st (Sparse.classify (.ofGraph G.graph) level numcells st).2 := by
  obtain ⟨hl, hp, hf, hc⟩ := classify_frame (.ofGraph G.graph) level numcells st
  apply h.step hl hp (Or.inl hf) (Or.inl hc)
  rw [hl, hp, classify_scratch]
  exact h.scratch

theorem target_frame (h : Ready G level numcells st) (first : Bool) (tcLevel : Nat) :
    Local G level numcells st (chooseTarget first (.ofGraph G.graph) tcLevel level numcells st).2.2.2 := by
  obtain ⟨hl, hp, hf, hc⟩ := chooseTarget_frame first (.ofGraph G.graph) tcLevel level numcells st
  exact h.step hl hp (Or.inl hf) (Or.inl hc)
    (chooseTarget_valid first (.ofGraph G.graph) tcLevel level numcells st h.scratch)

end Ready
end Hex.GraphIso.Nauty.Sparse
