/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.PolicyScratch
public import HexGraphIso.Nauty.Sparse.RefineBounds
public import HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Policy.Preserve
public import HexGraphIso.Nauty.Policy.Storage
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Sparse leaf classification may update canonical rows and scatter a
permutation, but retains the independent refinement scratch exactly. -/
theorem classify_scratch (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.canong.scratch = st.canong.scratch := by
  unfold classify
  apply Id.of_wp_run_eq rfl (fun out : Leaf × State n => out.2.canong.scratch = st.canong.scratch)
  mvcgen
  all_goals simp_all +zetaDelta [SearchState.scatter_storage, Storage.update]

/-- Every actual sparse policy operation preserves persistent allocations and
mark bounds. No partition-validity or recursive-correctness premise is needed. -/
theorem boundsPolicy (g : Graph n) (inf tcLevel : Nat) :
    Generic.Preserve g inf tcLevel (fun st : State n => Scratch.Bounded n st.canong.scratch) where
  visit := fun level numcells st h => visit_bounded g level numcells st h
  record := fun _ _ _ h => h
  compare := by
    intro level code st h
    change Scratch.Bounded n (compareCodes level code st).canong.scratch
    rw [SearchState.compare_storage]
    exact h
  target := fun first level numcells st h => chooseTarget_bounded first g tcLevel level numcells st h
  terminal := by
    intro level st h
    change Scratch.Bounded n (firstterminal level st).canong.scratch
    rw [SearchState.terminal_storage]
    exact h
  classify := by
    intro level numcells st h
    change Scratch.Bounded n (classify g level numcells st).2.canong.scratch
    rw [classify_scratch]
    exact h
  leaf := by
    intro leaf level st h
    change Scratch.Bounded n (leafExit leaf level st).2.canong.scratch
    rw [SearchState.leaf_storage]
    exact h
  cheap := by
    intro first level st h
    change Scratch.Bounded n (cheapCheck first level st).canong.scratch
    unfold cheapCheck
    split <;> exact h
  child := fun first level tc tv st h => (child_valid first level tc tv st h).toBounded
  afterChild := fun _ _ _ h => h
  leave := fun _ _ h => h
  recover := fun level st h => (recover_valid inf level st h).toBounded
  afterSweep := by
    intro first level size index st h
    change Scratch.Bounded n
      (if first then { (afterSweep first level size index st) with
        order := (afterSweep first level size index st).order * index }
      else afterSweep first level size index st).canong.scratch
    cases first <;> simp only [ite_true, Bool.false_eq_true, ite_false]
    all_goals unfold afterSweep; split <;> exact h

/-- The real production node preserves scratch bounds on first and later
paths, for every fuel value and every kind of return. -/
theorem node_bounded (g : Graph n) (first : Bool) (inf tcLevel fuel level numcells : Nat)
    (st : State n) (h : Scratch.Bounded n st.canong.scratch) :
    Scratch.Bounded n (Generic.node first g inf tcLevel fuel level numcells st).2.canong.scratch :=
  Generic.node_sound (boundsPolicy g inf tcLevel).sound first fuel level numcells st h

theorem sweep_bounded (g : Graph n) (first : Bool)
    (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat) (cursor : Option Nat)
    (cell : VSet n) (st : State n) (h : Scratch.Bounded n st.canong.scratch) :
    Scratch.Bounded n
      (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.canong.scratch :=
  Generic.sweep_sound (boundsPolicy g inf tcLevel).sound first fuel cfuel level numcells
    tc tv1 cursor cell index st h

/-- Root initialization establishes the invariant, so production execution
needs no external scratch hypothesis. Finishing canonical rows retains it. -/
theorem run_bounded (g : Graph n) (lab : Array Nat) (ends : List Nat) :
    Scratch.Bounded n (run g lab ends).canong.scratch := by
  have h : Scratch.Bounded n (initial g lab ends).canong.scratch :=
    (Scratch.fresh_valid n lab (initPtn n (n + 2) ends) 1).toBounded
  change Scratch.Bounded n (runState g lab ends).2.canong.scratch
  unfold runState
  split
  · exact h
  · exact node_bounded g true (n + 2) 100 (n + 2) 1 ends.length _ h

end Hex.GraphIso.Nauty.Sparse
