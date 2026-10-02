/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.ScratchSearch
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

/-- Individualization retains allocated scratch and invalidates the indices
in the actual sparse policy before exposing the child partition. -/
theorem child_valid (first : Bool) (level tc tv : Nat) (st : State n)
    (h : Scratch.Bounded n st.canong.scratch) :
    let out := (policy (n := n)).child first level tc tv st
    Scratch.Valid n out.lab out.ptn (level + 1) out.canong.scratch := by
  have he : (Nauty.child first level tc tv st).canong = st.canong := by
    cases first <;> simp [Nauty.child]
  change Scratch.Valid n _ _ (level + 1) (Nauty.child first level tc tv st).canong.invalidate.scratch
  apply Storage.invalidate_valid
  rw [he]
  exact h

/-- The sparse policy's recovery invalidates indices after reopening the
parent partition, preserving the allocation and generation bounds. -/
theorem recover_valid (inf level : Nat) (st : State n)
    (h : Scratch.Bounded n st.canong.scratch) :
    let out := (policy (n := n)).recover inf level st
    Scratch.Valid n out.lab out.ptn level out.canong.scratch := by
  have he : (Nauty.recover inf level st).canong = st.canong := by
    rw [Nauty.recover, recoverLevels, recoverPtn]
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.canong, ite_self]
  change Scratch.Valid n _ _ level (Nauty.recover inf level st).canong.invalidate.scratch
  apply Storage.invalidate_valid
  rw [he]
  exact h

open Std.Do
set_option mvcgen.warning false

/-- Target selection's guards, optional hint, borrowed hit array, and
bookkeeping updates all preserve scratch validity for the returned state. -/
theorem chooseTarget_valid (first : Bool) (g : Graph n) (tcLevel level numcells : Nat)
    (st : State n) (h : Scratch.Valid n st.lab st.ptn level st.canong.scratch) :
    let out := (chooseTarget first g tcLevel level numcells st).2.2.2
    Scratch.Valid n out.lab out.ptn level out.canong.scratch := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun t : Int × VSet n × Nat × State n =>
    Scratch.Valid n t.2.2.2.lab t.2.2.2.ptn level t.2.2.2.canong.scratch)
  mvcgen
  all_goals
    simp_all +zetaDelta
    try exact maketargetCached_valid _ _ _ _ _ _ _ h

/-- The target policy preserves allocation and generation bounds independently
of cell-index correctness. -/
theorem chooseTarget_bounded (first : Bool) (g : Graph n) (tcLevel level numcells : Nat)
    (st : State n) (h : Scratch.Bounded n st.canong.scratch) :
    Scratch.Bounded n (chooseTarget first g tcLevel level numcells st).2.2.2.canong.scratch := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun t : Int × VSet n × Nat × State n =>
    Scratch.Bounded n t.2.2.2.canong.scratch)
  mvcgen
  all_goals
    simp_all +zetaDelta
    try exact maketargetCached_bounded _ _ _ _ _ _ _ h

end Hex.GraphIso.Nauty.Sparse
