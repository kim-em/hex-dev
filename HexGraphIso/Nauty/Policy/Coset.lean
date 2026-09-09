/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Calls
public import HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Calls
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.Prepared
import all HexGraphIso.Nauty.Policy.First
import all HexGraphIso.Nauty.Policy.Engine
import all HexGraphIso.Nauty.Search.Generic
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Leaf actions preserve the coset index selected by first-path descent. -/
theorem leafExit_coset (leaf : Leaf) (level : Nat) (st : Search n) :
    (leafExit leaf level st).2.cosetindex = st.cosetindex := by
  cases leaf <;> unfold leafExit pruneReturn admit pushAuto install
  all_goals simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd]
  all_goals repeat' split
  all_goals rfl

/-- Local off-path operations retain the coset index. -/
theorem compare_coset (level code : Nat) (st : Search n) :
    (compareCodes level code st).cosetindex = st.cosetindex := by
  unfold compareCodes
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Search.cosetindex, ite_self]

/-- Classification changes scratch data without changing the coset index. -/
theorem classify_coset (ctx : Ctx n) (level numcells : Nat) (st : Search n) :
    (classify ctx level numcells st).2.cosetindex = st.cosetindex := by
  unfold classify
  simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.snd, scatter_eq,
    apply_ite Search.cosetindex, ite_self]

/-- Recovery preserves the current coset index. -/
theorem recover_coset (inf level : Nat) (st : Search n) :
    (recoverLevels level (recoverPtn inf level st)).cosetindex = st.cosetindex := by
  unfold recoverLevels recoverPtn
  simp only [Id.run_bind, Id.run_pure, apply_ite Id.run, apply_ite Search.cosetindex, ite_self]

private def cosetContract : Generic.Contract (Search n) n where
  nodePre _ first _ _ _ := first = false
  nodePost _ _ _ _ st out := out.2.cosetindex = st.cosetindex
  sweepPre _ _ first _ _ _ _ _ _ _ _ := first = false
  sweepPost _ _ _ _ _ _ _ _ _ _ st out := out.2.2.cosetindex = st.cosetindex

private theorem cosetPolicy (ctx : Ctx n) (inf tcLevel : Nat) :
    Generic.CallPolicy ctx inf tcLevel (cosetContract (n := n)) where
  node_zero := by intros; rfl
  sweep_none := by intros; rfl
  sweep_zero := by intros; rfl
  node_step := by
    intro fuel hs first level numcells st hf
    cases hf
    let p := prepareOther ctx tcLevel level numcells st
    let c := classify ctx level p.1 p.2.2.2.2.2
    let out := leafExit c.1 level c.2
    have he : out.2.cosetindex = st.cosetindex := by
      rw [leafExit_coset, classify_coset]
      dsimp only [p, prepareOther]
      rw [chooseTarget_fields, compare_coset]
      rfl
    have hcheap : (cheapCheck false level out.2).cosetindex = out.2.cosetindex := by
      unfold cheapCheck
      split <;> rfl
    have hh := hs false level p.1 p.2.2.1.toNat ((p.2.2.2.1.nextElem none).getD 0)
      (p.2.2.2.1.nextElem none) p.2.2.2.1 0 (cheapCheck false level out.2) rfl
    change (Generic.sweepCall ctx inf tcLevel fuel (n + 1) false level p.1 p.2.2.1.toNat
      ((p.2.2.2.1.nextElem none).getD 0) (p.2.2.2.1.nextElem none) p.2.2.2.1 0
      (cheapCheck false level out.2)).2.2.cosetindex = _ at hh
    rw [hcheap, he] at hh
    change (Generic.nodeStep ctx tcLevel _ false level numcells st).2.cosetindex = _
    unfold Generic.nodeStep
    change (match out.1 with
      | .done =>
        let r := Generic.sweepCall ctx inf tcLevel fuel (n + 1) false level p.1 p.2.2.1.toNat
          ((p.2.2.2.1.nextElem none).getD 0) (p.2.2.2.1.nextElem none) p.2.2.2.1 0
          (cheapCheck false level out.2)
        match r.1 with
        | .done => (Generic.Exit.unwind (level - 1) false, afterSweep false level p.2.2.2.2.1 r.2.1 r.2.2)
        | _ => (r.1, r.2.2)
      | _ => out).2.cosetindex = _
    cases hx : out.1 with
    | fuel => exact he
    | unwind => exact he
    | done =>
      dsimp only
      split <;> exact hh
  sweep_step := by
    intro fuel cfuel hn hs first level numcells tc tv1 tv cell index st hf
    cases hf
    let raw := Generic.nodeCall ctx inf tcLevel fuel false (level + 1) (numcells + 1)
      (child false level tc tv st)
    have hd := hn false (level + 1) (numcells + 1) (child false level tc tv st) rfl
    change raw.2.cosetindex = st.cosetindex at hd
    have hh : ∀ cell, (Generic.sweepCall ctx inf tcLevel fuel cfuel false level numcells tc tv1
        (cell.nextElem (some tv)) cell index
        (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv }))).2.2.cosetindex = st.cosetindex := by
      intro cell
      have hr := hs false level numcells tc tv1 (cell.nextElem (some tv)) cell index
        (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv })) rfl
      change (Generic.sweepCall ctx inf tcLevel fuel cfuel false level numcells tc tv1
        (cell.nextElem (some tv)) cell index
        (recoverLevels level (recoverPtn inf level { raw.2 with fixedpts := raw.2.fixedpts.erase tv }))).2.2.cosetindex = _ at hr
      rw [recover_coset] at hr
      exact hr.trans hd
    change (Generic.sweepStep inf _ _ false level numcells tc tv1 tv cell index st).2.2.cosetindex = _
    unfold Generic.sweepStep Generic.advance Generic.resume
    simp only [Bool.not_false, Bool.true_or, Bool.false_and, Bool.false_eq_true, Bool.true_and, ↓reduceIte]
    dsimp only [raw] at hd hh
    generalize hraw : Generic.nodeCall ctx inf tcLevel fuel false (level + 1) (numcells + 1)
      (child false level tc tv st) = result at hd hh ⊢
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
      · cases short <;> simp only [Bool.false_eq_true, ↓reduceIte]
        all_goals split <;> exact hh _

/-- Off-path recursion never overwrites the suspended first child's index. -/
theorem node_coset (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat) (st : Search n) :
    (node false ctx inf tcLevel fuel level numcells st).2.cosetindex = st.cosetindex := by
  rw [node_eq_generic]
  exact Generic.node_calls (cosetPolicy ctx inf tcLevel) false fuel level numcells st rfl

end Hex.GraphIso.Nauty
