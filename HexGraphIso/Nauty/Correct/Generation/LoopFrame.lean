/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Reorder
public import HexGraphIso.Nauty.Correct.Generation.Tree
public import HexGraphIso.Nauty.Correct.OffPath.Loop

public section

namespace Hex.GraphIso.Nauty

open Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}
    {tcLevel specFuel level numcells tc len : Nat} {tcell : VSet n}
    {codes bs fs : List Nat} {rsLab rsPtn : Array Nat}
    {cursor : Option Nat} {base st : SearchSt n} {best : Option (Key n)}
    {trail : FrameTrail}

/-- A valid sweep freezes a valid refined tree, including its depth bound. -/
theorem LoopInv.tree
    (h : Nauty.LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail) :
    TreeOk ctx level (Nauty.LoopInv.frame rsLab rsPtn numcells) := by
  constructor
  · refine ⟨⟨h.frozenLabSize, h.frozenLabOk, h.frozenPtnSize, h.frozenEnd⟩, ?_, ?_, ?_⟩
    · rw [← h.baseLab]
      exact labInj_of_reach h.baseOk.labSize h.nonempty h.baseOk.reach
    · intro q _
      exact h.values q
    · exact Nat.le_of_lt h.levelLt
  · exact h.equitable
  · change bcount rsPtn level n = numcells
    rw [← h.basePtn]
    exact h.baseOk.count.symm
  · have hc := h.baseOk.count
    have hb := h.baseOk.bc
    change level ≤ numcells
    omega

/-- A frozen child reference follows the same vertex through any
cell reordering performed by the preceding sibling visits. -/
theorem LoopInv.childPath
    (h : Nauty.LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    {boundary o current : Nat} {targets : List Nat} {key : Key n}
    (hgsz : ctx.g.size = n) (ho : o < len) (hc : current < len)
    (hat : st.lab[tc + current]! = rsLab[tc + o]!)
    (hp : RefPath ctx tcLevel boundary (level + 1)
      (childSt ctx level (Nauty.LoopInv.frame rsLab rsPtn numcells) tc rsLab[tc + o]!) targets key) :
    RefPath ctx tcLevel boundary (level + 1)
      (childSt ctx level (Nauty.LoopInv.frame st.lab st.ptn numcells) tc st.lab[tc + current]!) targets key := by
  have hcell : (tc, tc + len - 1) ∈ cells rsPtn level n :=
    isCell_mem_cells h.cell (by rw [h.frozenPtnSize]; exact Nat.le_refl _) h.frozenEnd (by have := h.range; omega)
  have hlen := h.lenTwo
  have hp' := hp.reorderChild hgsz h.tree.it h.levelLt h.run.searchOk.labSize
    (cellsPerm_symm h.labPerm) hcell (by omega) (by omega) (by omega) hat
  rw [h.ptnEq]
  exact hp'

/-- The selected vertex occupies a singleton cell at child entry. -/
theorem LoopInv.picked
    (h : Nauty.LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    {current tv : Nat} {child : SearchSt n}
    (hc : current < len) (hat : st.lab[tc + current]! = tv)
    (he : child = { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv }) :
    IsCell child.ptn (level + 1) tc 1 ∧ child.lab[tc]! = tv := by
  have hrange := h.range
  have hlen := h.lenTwo
  rw [he]
  constructor
  · exact isCell_breakout_target (n := n) (lab := st.lab) (tv := tv) (by rw [h.run.searchOk.ptnSize]; omega) h.currentCell.2.1
  · rw [← hat]
    exact breakout_at_target (n := n) (ptn := st.ptn) (level := level)
      (by rw [h.run.searchOk.labSize]; exact labInj_of_reach h.run.searchOk.labSize h.nonempty h.run.searchOk.reach)
      (by rw [h.run.searchOk.labSize]; omega)

/-- A child's reached labelling remains in the frozen parent cell frame,
with its individualized vertex still at the target position. -/
theorem LoopInv.returned
    (h : Nauty.LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    {current tv : Nat} {child out : SearchSt n}
    (hc : current < len) (hat : st.lab[tc + current]! = tv)
    (he : child = { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv })
    (hout : SearchOut G level (level + 1) child out) :
    cellsPerm rsPtn level rsLab out.lab ∧ out.lab[tc]! = tv := by
  have hparent : SearchOut G level level st out := by
    apply breakout_child_out h.nonempty h.run.searchOk h.positive h.currentCell h.lenTwo
      h.range hc hout
    · rw [he, hat]
    · rw [he]
      exact breakout_ptn (n := n) st.lab st.ptn (level + 1) tc tv
    · rw [he]
    · rw [he]
  have hfrozen := h.effect.trans hparent
  obtain ⟨hsingle, hpicked⟩ := h.picked hc hat he
  constructor
  · rw [← h.basePtn, ← h.baseLab]
    exact hfrozen.perm
  · exact (hout.atSingleton hsingle).trans hpicked

/-- Every retained ledger pair accepted by this frame's fixed points
stabilizes its frozen cells, independently of the mutable target set. -/
theorem LoopInv.localPairs
    (h : Nauty.LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hp : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st) :
    ∀ p ∈ st.autos.toList, st.fixedpts.subset p.1 = true →
      PairOk ctx.g rsPtn rsLab level p.1 p.2 := by
  intro p hm hf
  have hpair := hp.autos h.run p hm hf
  rw [h.ptnEq] at hpair
  exact LocalAutos.reindexPair hpair (cellsPerm_symm h.labPerm)
    h.frozenPtnSize h.run.searchOk.labSize h.frozenLabSize h.frozenEnd

/-- Every recorded sweep fragment exposes its entry invariant. -/
theorem OtherSweep.hyp {inf runFuel tv1 e loopFuel : Nat}
    (h : OtherSweep G ctx inf tcLevel specFuel runFuel level numcells tc len tv1 e
      codes fs rsLab rsPtn base loopFuel cursor tcell st best trail) :
    ∃ bs, OtherLoopHyp G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor e base st best trail := by
  cases h with
  | done hyp next => exact ⟨_, hyp⟩
  | visit hyp next offsetLt atOffset childEq call run keep continuation => exact ⟨_, hyp⟩

end Hex.GraphIso.Nauty
