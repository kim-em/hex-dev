/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import HexGraphIso.Nauty.Sparse.Controls
public import HexGraphIso.Nauty.Sparse.ComparisonOps
public import HexGraphIso.Nauty.Policy.Coset
import all HexGraphIso.Nauty.Sparse.Search
import all HexGraphIso.Nauty.Policy.Generic.Calls
import all HexGraphIso.Nauty.Policy.Coset
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.First.State
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.State
import Std.Tactic.Do

public section

namespace Hex.GraphIso.Nauty.Sparse

open Std.Do
set_option mvcgen.warning false

/-- Native target selection borrows scratch without changing the index
selected by the most recent first-path descent. -/
theorem chooseTarget_coset (first : Bool) (g : Graph n) (tcLevel level numcells : Nat) (st : State n) :
    (chooseTarget first g tcLevel level numcells st).2.2.2.cosetindex = st.cosetindex := by
  unfold chooseTarget
  apply Id.of_wp_run_eq rfl (fun out : Int × VSet n × Nat × State n => out.2.2.2.cosetindex = st.cosetindex)
  mvcgen
  all_goals simp_all +zetaDelta

theorem classify_coset (g : Graph n) (level numcells : Nat) (st : State n) :
    (classify g level numcells st).2.cosetindex = st.cosetindex := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite SearchState.cosetindex, ite_self]

private def cosetContract : Generic.Contract (State n) n where
  nodePre _ first _ _ _ := first = false
  nodePost _ _ _ _ st out := out.2.cosetindex = st.cosetindex
  sweepPre _ _ first _ _ _ _ _ _ _ _ := first = false
  sweepPost _ _ _ _ _ _ _ _ _ _ st out := out.2.2.cosetindex = st.cosetindex

private theorem coset_node (g : Graph n) (tcLevel fuel : Nat)
    (next : Generic.SweepFn (State n) n)
    (hs : (cosetContract (n := n)).sweepValid fuel (n + 1) next)
    (first : Bool) (level numcells : Nat) (st : State n) (hf : first = false) :
    (Generic.nodeStep g tcLevel next first level numcells st).2.cosetindex = st.cosetindex := by
    cases hf
    let p := prepareOther g tcLevel level numcells st
    let c := classify g level p.1 p.2.2.2.2.2
    let out := leafExit c.1 level c.2
    have he : out.2.cosetindex = st.cosetindex := by
      rw [leafExit_coset, classify_coset]
      dsimp only [p, prepareOther]
      rw [chooseTarget_coset, compare_coset]
      rfl
    have hcheap : (cheapCheck false level out.2).cosetindex = out.2.cosetindex := by
      unfold cheapCheck
      split <;> rfl
    have hh := hs false level p.1 p.2.2.1.toNat ((p.2.2.2.1.nextElem none).getD 0)
      (p.2.2.2.1.nextElem none) p.2.2.2.1 0 (cheapCheck false level out.2) rfl
    change (next false level p.1 p.2.2.1.toNat
      ((p.2.2.2.1.nextElem none).getD 0) (p.2.2.2.1.nextElem none) p.2.2.2.1 0
      (cheapCheck false level out.2)).2.2.cosetindex = _ at hh
    rw [hcheap, he] at hh
    unfold Generic.nodeStep
    dsimp only [policy, Generic.Policy.visit, Generic.Policy.recordFirst,
      Generic.Policy.compareCodes, Generic.Policy.chooseTarget, Generic.Policy.classify,
      Generic.Policy.leafExit, Generic.Policy.cheapCheck, Generic.Policy.afterSweep]
    dsimp only [out, c, p, prepareOther] at he hh
    generalize hv : visit g level numcells st = v at he hh ⊢
    obtain ⟨nc, code, ready⟩ := v
    simp only [Bool.false_eq_true, ite_false]
    generalize ht : chooseTarget false g tcLevel level nc (compareCodes level code ready) = t at he hh ⊢
    obtain ⟨tc, cell, len, prepared⟩ := t
    generalize hc : leafExit (classify g level nc prepared).1 level
      (classify g level nc prepared).2 = result at he hh ⊢
    obtain ⟨exit, result⟩ := result
    cases exit with
    | fuel => exact he
    | unwind => exact he
    | done =>
      dsimp only
      split <;> exact hh

private theorem coset_sweep (inf fuel cfuel : Nat)
    (descend : Generic.NodeFn (State n)) (next : Generic.SweepFn (State n) n)
    (hn : (cosetContract (n := n)).nodeValid fuel descend)
    (hs : (cosetContract (n := n)).sweepValid fuel cfuel next)
    (first : Bool) (level numcells tc tv1 tv : Nat) (cell : VSet n) (index : Nat)
    (st : State n) (hf : first = false) :
    (Generic.sweepStep inf descend next first level numcells tc tv1 tv cell index st).2.2.cosetindex =
      st.cosetindex := by
    cases hf
    let child := (policy (n := n)).child false level tc tv st
    let raw := descend false (level + 1) (numcells + 1) child
    let left := (policy (n := n)).leaveChild tv raw.2
    let ready := (policy (n := n)).recover inf level left
    have hd := hn false (level + 1) (numcells + 1) child rfl
    change raw.2.cosetindex = st.cosetindex at hd
    have hr : ready.cosetindex = raw.2.cosetindex := recover_coset inf level left
    have hh : ∀ cell, (next false level numcells tc tv1
        (cell.nextElem (some tv)) cell index ready).2.2.cosetindex = st.cosetindex := by
      intro cell
      have he := hs false level numcells tc tv1 (cell.nextElem (some tv)) cell index ready rfl
      change (next false level numcells tc tv1
        (cell.nextElem (some tv)) cell index ready).2.2.cosetindex = ready.cosetindex at he
      exact he.trans (hr.trans hd)
    change (Generic.sweepStep inf _ _ false level numcells tc tv1 tv cell index st).2.2.cosetindex = _
    unfold Generic.sweepStep Generic.advance Generic.resume
    simp only [Bool.not_false, Bool.true_or, Bool.false_and, Bool.false_eq_true, Bool.true_and, ite_false, ite_true]
    dsimp only [raw, child, ready, left] at hd hh
    generalize hraw : descend false (level + 1) (numcells + 1)
      ((policy (n := n)).child false level tc tv st) = result at hd hh ⊢
    obtain ⟨exit, state⟩ := result
    cases exit with
    | fuel => exact hd
    | done =>
      simp only [Id.run_pure]
      split <;> exact hh _
    | unwind target short =>
      simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
      split
      · exact hd
      · cases short <;> simp only [Bool.false_eq_true, ite_false, ite_true]
        all_goals split <;> exact hh _

private theorem cosetPolicy (g : Graph n) (inf tcLevel : Nat) :
    Generic.SoundPolicy g inf tcLevel (cosetContract (n := n)) where
  node_zero := by intros; rfl
  sweep_none := by intros; rfl
  sweep_zero := by intros; rfl
  node_step := coset_node g tcLevel
  sweep_step := coset_sweep inf

/-- Complete native off-path recursion retains the suspended first
child's index through every filter, recovery and nonlocal return. -/
theorem node_coset (g : Graph n) (inf tcLevel fuel level numcells : Nat) (st : State n) :
    (Generic.node false g inf tcLevel fuel level numcells st).2.cosetindex = st.cosetindex :=
  Generic.node_sound (cosetPolicy g inf tcLevel) false fuel level numcells st rfl

end Hex.GraphIso.Nauty.Sparse
