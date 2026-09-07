/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.CanonReceipt
public import HexGraphIso.Nauty.Correct.Generation.Return
public import HexGraphIso.Nauty.Correct.Generation.LoopFrame

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- A child that stays at an off-path sweep either lacks the sought
reference or returns a canonical carrier from an earlier child. Both
cases advance reference coverage without asserting exhaustive search. -/
theorem PathCover.visit {tcLevel specFuel runFuel boundary level numcells tc len tv current : Nat}
    {codes bs fs targets : List Nat} {rsLab rsPtn : Array Nat} {key : Key n}
    {tcell : VSet n} {cursor : Option Nat} {base st child out : SearchSt n}
    {best outBest : Option (Key n)} {trail childTrail eventTrail : FrameTrail} {r : Int}
    (h : PathCover ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells)
      tc len targets key tcell cursor)
    (hinv : LoopInv G ctx tcLevel specFuel level codes bs fs numcells
      rsLab rsPtn tc len tcell cursor base st best trail)
    (hgsz : ctx.g.size = n) (hnext : tcell.nextElem cursor = some tv)
    (hpast : CanonPast level tc cursor st)
    (hcurrent : current < len) (hat : st.lab[tc + current]! = tv)
    (hchild : child = { st with
      lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
      ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
      active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
      fixedpts := st.fixedpts.insert tv })
    (hrun : OtherRun G ctx tcLevel specFuel runFuel (level + 1) codes fs child out
      (numcells + 1) best outBest childTrail eventTrail r)
    (hout : SearchOut G level (level + 1) child out)
    (hguide : st.gcaFirst < level) (hstay : ¬ r < Int.ofNat level)
    (hreceipt : ∀ o, o < len → rsLab[tc + o]! = tv →
      ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key o →
      RefReturn ctx out r) :
    PathCover ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells)
      tc len targets key tcell (some tv) := by
  classical
  by_cases hex : ∃ o, o < len ∧ rsLab[tc + o]! = tv ∧
      ChildPath ctx tcLevel boundary level (LoopInv.frame rsLab rsPtn numcells) tc targets key o
  · obtain ⟨o, ho, hatFrozen, hp⟩ := hex
    have hret := hreceipt o ho hatFrozen hp
    have hfirst : out.gcaFirst = st.gcaFirst := by rw [hrun.firstGuide, hchild]
    have hbelow := hrun.node.exit.below (by omega)
    have hlen := hinv.lenTwo
    have hrange := hinv.range
    have hcell : (tc, tc + len - 1) ∈ cells rsPtn level n :=
      isCell_mem_cells hinv.cell (by rw [hinv.frozenPtnSize]; exact Nat.le_refl _)
        hinv.frozenEnd (by omega)
    cases hret with
    | first returned carrier =>
      rw [returned, hfirst] at hstay
      exact (hstay (Int.ofNat_lt.mpr hguide)).elim
    | orbit returned payload =>
      rw [returned, hfirst] at hstay
      exact (hstay (Int.ofNat_lt.mpr hguide)).elim
    | canon returned carrier =>
      have he : level = out.gcaCanon := by
        simp only [returned, Int.ofNat_eq_natCast] at hbelow hstay
        omega
      obtain ⟨hperm, hpicked⟩ := hinv.returned hcurrent hat hchild hout
      exact h.canon hnext hinv.tree.it hinv.levelLt hgsz hcell (by omega) (by omega)
        hpast hinv.refs (by rw [hchild]) (by rw [hchild]) hrun.guide he carrier
        hrun.node.event.canonSize hperm hpicked
  · apply h.advance hnext
    intro o ho hat hp
    exact hex ⟨o, ho, hat, hp⟩

end Hex.GraphIso.Nauty.Generation
