/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Search
public import HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Policy.Preserve
public import HexGraphIso.Nauty.Policy.Workspace
import all HexGraphIso.Nauty.Policy.Generic.Sound
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Native target selection retains the pruning workspace capacity. -/
theorem chooseTarget_capacity (first : Bool) (g : Graph n)
    (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.wsCap = st.wsCap := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.wsCap = st.wsCap)
  mvcgen
  all_goals simp_all +zetaDelta

/-- Both native automorphism scatters retain the pruning workspace capacity. -/
theorem classify_capacity (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.wsCap = st.wsCap := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd,
    apply_ite (fun s : State n => s.wsCap), scatter_eq, ite_self]

/-- Every executed policy operation preserves the pair capacity, on the first
descent as well as later siblings and nonlocal returns. -/
theorem capacityPolicy (g : Graph n) (inf tcLevel size : Nat) :
    Generic.Preserve g inf tcLevel (fun st : State n => st.wsCap = size) where
  visit := fun _ _ _ h => h
  record := fun _ _ _ h => h
  compare := by
    intro level code st h
    change (compareCodes level code st).wsCap = size
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run,
      apply_ite (fun s : State n => s.wsCap), ite_self]
    exact h
  target := by
    intro first level numcells st h
    change (chooseTarget first g tcLevel level numcells st).2.2.2.wsCap = size
    rw [chooseTarget_capacity]
    exact h
  terminal := fun _ _ h => h
  classify := by
    intro level numcells st h
    change (classify g level numcells st).2.wsCap = size
    rw [classify_capacity]
    exact h
  leaf := by
    intro leaf level st h
    change (leafExit leaf level st).2.wsCap = size
    rw [leafExit_capacity]
    exact h
  cheap := by
    intro first level st h
    change (cheapCheck first level st).wsCap = size
    unfold cheapCheck
    split <;> exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  afterChild := fun _ _ _ h => h
  leave := fun _ _ h => h
  recover := by
    intro level st h
    change (recoverLevels level (recoverPtn inf level st)).wsCap = size
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run,
      apply_ite (fun s : State n => s.wsCap), ite_self]
    exact h
  afterSweep := by
    intro first level count index st h
    change (if first then { (afterSweep first level count index st) with
      order := (afterSweep first level count index st).order * index }
      else afterSweep first level count index st).wsCap = size
    cases first <;> simp only [ite_true, Bool.false_eq_true, ite_false]
    all_goals unfold afterSweep; split <;> exact h

theorem node_capacity (first : Bool) (g : Graph n)
    (inf tcLevel fuel level numcells : Nat) (st : State n) :
    (Generic.node first g inf tcLevel fuel level numcells st).2.wsCap = st.wsCap :=
  Generic.node_sound (capacityPolicy g inf tcLevel st.wsCap).sound
    first fuel level numcells st rfl

theorem sweep_capacity (first : Bool) (g : Graph n)
    (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) :
    (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.wsCap =
      st.wsCap :=
  Generic.sweep_sound (capacityPolicy g inf tcLevel st.wsCap).sound
    first fuel cfuel level numcells tc tv1 cursor cell index st rfl

/-- The initialized native search retains its pinned 500-pair capacity,
including order zero, independently of label or graph validity. -/
theorem runState_capacity (g : Graph n) (lab : Array Nat) (ends : List Nat) :
    (runState g lab ends).2.wsCap = 500 := by
  unfold runState
  split
  · rfl
  · rw [node_capacity]
    rfl

theorem run_capacity (g : Graph n) (lab : Array Nat) (ends : List Nat) :
    (run g lab ends).wsCap = 500 :=
  runState_capacity g lab ends

end Hex.GraphIso.Nauty.Sparse
