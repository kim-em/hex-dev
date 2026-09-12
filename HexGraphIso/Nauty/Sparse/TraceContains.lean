/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Trace
public import HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Policy.Preserve
import all HexGraphIso.Nauty.Sparse.Trace
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Native target selection never removes an emitted generator. -/
theorem chooseTarget_trace (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.genTrace = st.genTrace := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n => out.2.2.2.genTrace = st.genTrace)
  mvcgen
  all_goals simp_all +zetaDelta

/-- Every literal policy transition retains each previously emitted
array, including the first descent, first-child bookkeeping and recovery. -/
theorem tracePolicy (g : Graph n) (inf tcLevel : Nat) (gamma : Array Nat) :
    Generic.Preserve g inf tcLevel (fun st : State n => gamma ∈ st.genTrace) where
  visit := fun _ _ _ h => h
  record := fun _ _ _ h => h
  compare := by
    intro level code st h
    change gamma ∈ (compareCodes level code st).genTrace
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace, ite_self]
    exact h
  target := by
    intro first level numcells st h
    change gamma ∈ (chooseTarget first g tcLevel level numcells st).2.2.2.genTrace
    rwa [chooseTarget_trace]
  terminal := fun _ _ h => h
  classify := by
    intro level numcells st h
    change gamma ∈ (classify g level numcells st).2.genTrace
    rwa [classify_trace]
  leaf := by
    intro leaf level st h
    change gamma ∈ (leafExit leaf level st).2.genTrace
    rw [leafExit_trace]
    cases leaf <;> first | exact h | exact Array.mem_push.mpr (Or.inl h)
  cheap := by
    intro first level st h
    change gamma ∈ (cheapCheck first level st).genTrace
    unfold cheapCheck
    split <;> exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  afterChild := fun _ _ _ h => h
  leave := fun _ _ h => h
  recover := by
    intro level st h
    change gamma ∈ (recoverLevels level (recoverPtn inf level st)).genTrace
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.genTrace, ite_self]
    exact h
  afterSweep := by
    intro first level size index st h
    change gamma ∈ (if first then { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).genTrace
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> exact h

/-- Both complete native node calls retain their incoming trace, even
when fuel expires or a return crosses multiple suspended parents. -/
theorem node_contains (first : Bool) (g : Graph n) (inf tcLevel fuel level numcells : Nat)
    (st : State n) {gamma : Array Nat} (h : gamma ∈ st.genTrace) :
    gamma ∈ (Generic.node first g inf tcLevel fuel level numcells st).2.genTrace :=
  Generic.node_sound (tracePolicy g inf tcLevel gamma).sound first fuel level numcells st h

/-- A native sibling continuation retains every generator already
received from a child, irrespective of its first-sweep flag. -/
theorem sweep_contains (first : Bool) (g : Graph n) (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) {gamma : Array Nat} (h : gamma ∈ st.genTrace) :
    gamma ∈ (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.genTrace :=
  Generic.sweep_sound (tracePolicy g inf tcLevel gamma).sound first fuel cfuel level numcells tc tv1 cursor cell index st h

end Hex.GraphIso.Nauty.Sparse
