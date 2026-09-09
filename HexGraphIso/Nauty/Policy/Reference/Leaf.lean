/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.GenerationRef
public import HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.GenerationRef
import all HexGraphIso.Nauty.Policy.Trace
import all HexGraphIso.Nauty.Policy.Classify
import all HexGraphIso.Nauty.Policy.Scatter
import all HexGraphIso.Nauty.Policy.Controls
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Generation.Match
import all HexGraphIso.Nauty.Generation.Matching
import all HexGraphIso.Nauty.Invariant.Cursor
import all HexGraphIso.Nauty.Invariant.Carrier
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Search.State

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Equal reference rows at a matching leaf force the actual code-one
classification, with its checked permutation in the emitted trace. -/
theorem rows_emit {ctx : Ctx n} {level : Nat} {st : Search n}
    (hgsz : ctx.g.size = n) (hwork : st.workperm.size = n)
    (hfirst : st.firstlab.size = n) (hfirstPerm : st.firstlab.toList.Perm (List.range n))
    (hlab : st.lab.size = n) (hlabPerm : st.lab.toList.Perm (List.range n))
    (hrows : leafRows ctx st.firstlab = leafRows ctx st.lab)
    (heq : st.eqlevFirst = level) :
    let c := classify ctx level n st
    let out := leafExit c.1 level c.2
    c.1 = .autoFirst ∧ out.1 = .unwind st.gcaFirst false ∧
      LabelCarrier ctx st.firstlab out.2.lab out.2.genTrace := by
  have hc := scatter_checked hwork hfirst hfirstPerm hlab hlabPerm hrows
  have hi := Generation.isautom_of_checked hgsz hc
  have hclass : classify ctx level n st = (.autoFirst, scatter st.firstlab st) := by
    rw [classify_eq]
    simp only [heq, beq_self_eq_true, bne_self_eq_false, Bool.false_and, Bool.false_eq_true,
      ite_false, ite_true]
    simp only [hi, Bool.or_true, ite_true]
  dsimp only
  rw [hclass]
  refine ⟨rfl, ?_, ?_⟩
  · unfold leafExit
    simp only [Id.run_pure, apply_ite Id.run, apply_ite Prod.fst, admit_gca]
    split <;> rfl
  · refine ⟨(scatter st.firstlab st).workperm, ?_, hc, ?_⟩
    · rw [leafExit_trace]
      exact Array.mem_push_self
    · have hm := scatter_map hwork hfirst hfirstPerm
      have hl := (leafExit_frame .autoFirst level (scatter st.firstlab st)).1
      rw [hl]
      exact hm

/-- A discrete matching node emits its first-reference carrier in the
actual search call, including refinement and comparison preparation. -/
theorem matching_leaf {ctx : Ctx n} {inf tcLevel fuel level numcells : Nat}
    {st : Search n} {targets : List Nat} {key : Key n}
    (hgsz : ctx.g.size = n) (hwork : st.workperm.size = n)
    (hfirst : st.firstlab.size = n) (hfirstPerm : st.firstlab.toList.Perm (List.range n))
    (hit : IterOk ctx level (st.refined ctx level numcells))
    (hnum : (st.refined ctx level numcells).numcells = n)
    (hdisc : ∀ q, q < n → (st.refined ctx level numcells).ptn[q]! ≤ level)
    (hm : Generation.Matches ctx level st targets key)
    (hp : Generation.HasLeaf ctx tcLevel level (st.refined ctx level numcells) targets key)
    (heq : st.eqlevFirst = level - 1) :
    let out := node false ctx inf tcLevel (fuel + 1) level numcells st
    out.1 = .unwind st.gcaFirst false ∧
      LabelCarrier ctx st.firstlab out.2.lab out.2.genTrace := by
  let rs := st.refined ctx level numcells
  let visited := (visit ctx level numcells st).2.2
  let compared := compareCodes level rs.longcode visited
  have hfields : compared.lab = rs.lab ∧ compared.firstlab = st.firstlab ∧
      compared.workperm = st.workperm ∧ compared.gcaFirst = st.gcaFirst := by
    dsimp only [compared]
    unfold compareCodes
    simp only [Id.run_pure, apply_ite Id.run]
    repeat' split
    all_goals exact ⟨rfl, rfl, rfl, rfl⟩
  have hm' : Generation.Matches ctx level visited targets key := hm.stateEq rfl rfl rfl
  have hc : compared.eqlevFirst = level := by
    have h := hm'.prep hp heq

    exact h
  have hr : leafRows ctx compared.firstlab = leafRows ctx compared.lab := by
    rw [hfields.1, hfields.2.1]
    exact (hm.discrete hp hit hdisc).2
  have emit := rows_emit hgsz (hfields.2.2.1 ▸ hwork) (hfields.2.1 ▸ hfirst)
    (hfields.2.1 ▸ hfirstPerm) (hfields.1 ▸ hit.ok.labSize)
    (hfields.1 ▸ labInj_perm_range hit.ok.labSize hit.ok.labOk hit.inj) hr hc
  dsimp only at emit
  let c := classify ctx level n compared
  let result := leafExit c.1 level c.2
  have hret : result.1 = .unwind st.gcaFirst false := emit.2.1.trans (by rw [hfields.2.2.2])
  have ht : chooseTarget false ctx tcLevel level n compared = (-1, VSet.empty, 0, compared) := by
    simp [chooseTarget]
  have hcall : node false ctx inf tcLevel (fuel + 1) level numcells st = result := by
    rw [node]
    change (Id.run do
      let (tc, cell, len, ready) := chooseTarget false ctx tcLevel level rs.numcells compared
      let (leaf, state) := classify ctx level rs.numcells ready
      let (exit, state) := leafExit leaf level state
      match exit with
      | .done =>
        let state := cheapCheck false level state
        let tv := cell.nextElem none
        let (exit, index, state) := sweep false ctx inf tcLevel fuel (n + 1)
          level rs.numcells tc.toNat (tv.getD 0) tv cell 0 state
        match exit with
        | .done => pure (.unwind (level - 1) false, afterSweep false level len index state)
        | _ => pure (exit, state)
      | _ => pure (exit, state)) = result
    rw [hnum, ht]
    change (match result.1 with
      | .done => _
      | _ => result) = result
    rw [hret]
  dsimp only
  rw [hcall]
  exact ⟨hret, hfields.2.1 ▸ emit.2.2⟩

end Hex.GraphIso.Nauty
