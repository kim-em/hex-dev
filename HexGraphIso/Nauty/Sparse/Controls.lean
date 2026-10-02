/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Divergence
public import HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.Bounds
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Actual target dispatch preserves the frozen ancestor and cheap boundary. -/
theorem chooseTarget_controls (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    let out := (chooseTarget first g tcLevel level numcells st).2.2.2
    out.gcaFirst = st.gcaFirst ∧ out.noncheaplevel = st.noncheaplevel := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n =>
    out.2.2.2.gcaFirst = st.gcaFirst ∧ out.2.2.2.noncheaplevel = st.noncheaplevel)
  mvcgen
  all_goals simp_all +zetaDelta

theorem classify_controls (g : Graph n) (level numcells : Nat) (st : State n) :
    let out := (classify g level numcells st).2
    out.gcaFirst = st.gcaFirst ∧ out.noncheaplevel = st.noncheaplevel := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.gcaFirst, apply_ite SearchState.noncheaplevel, ite_self]
  trivial

/-- Outside the first descent the actual sparse engine retains its frozen
first ancestor through every operation and every descendant call. -/
theorem gcaPolicy (g : Graph n) (inf tcLevel : Nat) :
    Generic.ReferencePolicy g inf tcLevel (fun st : State n => st.gcaFirst) where
  visit := fun _ _ _ => rfl
  compare := by
    intro level code st
    change (compareCodes level code st).gcaFirst = st.gcaFirst
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.gcaFirst, ite_self]
  target := fun level numcells st => (chooseTarget_controls false g tcLevel level numcells st).1
  classify := fun level numcells st => (classify_controls g level numcells st).1
  leaf := leafExit_gca
  cheap := by
    intro first level st
    change (cheapCheck first level st).gcaFirst = st.gcaFirst
    unfold cheapCheck
    split <;> rfl
  child := by intro first level tc tv st; cases first <;> rfl
  leave := fun _ _ => rfl
  recover := by
    intro level st
    change (recoverLevels level (recoverPtn inf level st)).gcaFirst = st.gcaFirst
    unfold recoverLevels recoverPtn
    simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite SearchState.gcaFirst, ite_self]
  afterSweep := by
    intro first level size index st
    change (if first then { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).gcaFirst = st.gcaFirst
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> rfl

theorem node_gca (g : Graph n) (inf tcLevel fuel level numcells : Nat) (st : State n) :
    (Generic.node false g inf tcLevel fuel level numcells st).2.gcaFirst = st.gcaFirst :=
  Generic.node_reference (gcaPolicy g inf tcLevel) fuel level numcells st

theorem sweep_gca (first : Bool) (g : Graph n) (inf tcLevel fuel cfuel level numcells tc tv1 index : Nat)
    (cursor : Option Nat) (cell : VSet n) (st : State n) (hpast : Generic.Past first tv1 cursor) :
    (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.gcaFirst =
      st.gcaFirst :=
  Generic.sweep_reference (gcaPolicy g inf tcLevel) first fuel cfuel level numcells tc tv1 index cursor cell st hpast

/-- A failed guard at an ancestor remains failed below that ancestor,
including the native cache invalidation and group-order accumulator updates. -/
theorem noncheapPolicy (g : Graph n) (inf tcLevel bound : Nat) :
    Generic.BoundedPolicy g inf tcLevel bound (fun st : State n => bound < st.noncheaplevel) where
  visit := fun _ _ _ h => h
  compare := by
    intro level code st _ h
    change bound < (compareCodes level code st).noncheaplevel
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run, apply_ite SearchState.noncheaplevel, ite_self]
    exact h
  target := by
    intro level numcells st _ h
    change bound < (chooseTarget false g tcLevel level numcells st).2.2.2.noncheaplevel
    rw [(chooseTarget_controls false g tcLevel level numcells st).2]
    exact h
  classify := by
    intro level numcells st h
    change bound < (classify g level numcells st).2.noncheaplevel
    rw [(classify_controls g level numcells st).2]
    exact h
  leaf := by
    intro leaf level st _ h
    change bound < (leafExit leaf level st).2.noncheaplevel
    rw [leafExit_noncheap]
    exact h
  cheap := by
    intro first level st hl h
    change bound < (cheapCheck first level st).noncheaplevel
    unfold cheapCheck
    split
    · change bound < level + 1; omega
    · exact h
  child := by intro first level tc tv st h; cases first <;> exact h
  leave := fun _ _ h => h
  recover := by
    intro level st hl h
    change bound < (Nauty.recover inf level st).noncheaplevel
    rw [recover_noncheap]
    split <;> omega
  afterSweep := by
    intro first level size index st _ h
    change bound < (if first then { (Nauty.afterSweep first level size index st) with
      order := (Nauty.afterSweep first level size index st).order * index }
      else Nauty.afterSweep first level size index st).noncheaplevel
    cases first <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    all_goals unfold Nauty.afterSweep; split <;> exact h

theorem node_noncheap {g : Graph n} {inf tcLevel fuel level numcells bound : Nat} {st : State n}
    (hl : bound < level) (h : bound < st.noncheaplevel) :
    bound < (Generic.node false g inf tcLevel fuel level numcells st).2.noncheaplevel :=
  Generic.node_bounded (noncheapPolicy g inf tcLevel bound) fuel level numcells st hl h

theorem sweep_noncheap {g : Graph n} {first : Bool}
    {inf tcLevel fuel cfuel level numcells tc tv1 index bound : Nat} {cursor : Option Nat}
    {cell : VSet n} {st : State n} (hpast : Generic.Past first tv1 cursor) (hl : bound ≤ level)
    (h : bound < st.noncheaplevel) :
    bound < (Generic.sweep first g inf tcLevel fuel cfuel level numcells tc tv1 cursor cell index st).2.2.noncheaplevel :=
  Generic.sweep_bounded (noncheapPolicy g inf tcLevel bound) first fuel cfuel level numcells
    tc tv1 index cursor cell st hpast hl h

end Hex.GraphIso.Nauty.Sparse
