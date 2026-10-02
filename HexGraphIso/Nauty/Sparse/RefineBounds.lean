/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.SplitBounds
public import HexGraphIso.Nauty.Sparse.GraphProps
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false
set_option maxHeartbeats 800000

/-- Index rebuilding retains both allocations, independently of index
contents and partition validity. -/
theorem indexCells_size (n : Nat) (lab ptn : Array Nat) (level : Nat)
    (starts ends : Array Nat) :
    let out := indexCells n lab ptn level starts ends
    out.1.size = starts.size ∧ out.2.size = ends.size := by
  unfold indexCells
  apply Id.of_wp_run_eq rfl (fun t : Array Nat × Array Nat =>
    t.1.size = starts.size ∧ t.2.size = ends.size)
  mvcgen
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜state.1.size = starts.size ∧ state.2.1.size = ends.size⌝)
      | exact (⇓⟨_, state⟩ => ⌜(state : Array Nat).size = starts.size⌝)
  all_goals simp_all +zetaDelta

/-- The complete executed refinement preserves scratch allocation and mark
generation bounds, including distance initialization and both splitter paths. -/
theorem refineWith_bounded (g : Graph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) (scratch : Scratch)
    (h : Scratch.Bounded n scratch) :
    Scratch.Bounded n (refineWith g level lab ptn active numcells scratch).toScratch := by
  unfold refineWith
  apply Id.of_wp_run_eq rfl (fun t : RefineSt n => Scratch.Bounded n t.toScratch)
  mvcgen
  all_goals try
    guard_target = Invariant _ _ _
    first
      | exact (⇓⟨_, state⟩ => ⌜Scratch.Bounded n state.1.toScratch⌝)
      | exact (⇓⟨_, state⟩ => ⌜Scratch.Bounded n state.toScratch⌝)
      | exact (⇓⟨_, _⟩ => ⌜True⌝)
  all_goals
    simp_all +zetaDelta [RefineSt.hash, RefineSt.toScratch]
    try grind [Scratch.Bounded, indexCells_size]
  all_goals try first
    | (apply splitCounts_bounded; assumption)
    | (apply splitSingleton_bounded; assumption)
    | (apply splitNontrivial_bounded; assumption)
  case vc8.post.success.isFalse.isTrue.pre =>
    have hi := indexCells_size n lab ptn level scratch.cellstart scratch.cellend
    exact ⟨hi.1.trans h.starts_size, hi.2.trans h.ends_size, distvals_size _ _,
      h.marks_size, h.vmarks_size, h.marks_le, h.vmarks_le⟩

theorem refine_bounded (g : Graph n) (level : Nat) (lab ptn : Array Nat)
    (active : VSet n) (numcells : Nat) :
    Scratch.Bounded n (refine g level lab ptn active numcells).toScratch :=
  refineWith_bounded g level lab ptn active numcells (.fresh n)
    (Scratch.fresh_valid n lab ptn level).toBounded

/-- Visiting a production-search node retains the same persistent bounds. -/
theorem visit_bounded (g : Graph n) (level numcells : Nat) (st : State n)
    (h : Scratch.Bounded n st.canong.scratch) :
    Scratch.Bounded n (visit g level numcells st).2.2.canong.scratch :=
  refineWith_bounded g level st.lab st.ptn st.active numcells st.canong.scratch h

end Hex.GraphIso.Nauty.Sparse
