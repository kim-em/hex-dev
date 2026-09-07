/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Selection
public import HexGraphIso.Nauty.Invariant.TargetCell
import all HexGraphIso.Nauty.Search.Engine

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- A nonnegative canonical comparison uses the specification's unhinted
target on an equitable partition. -/
theorem chooseTarget_unhinted {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (hnc : numcells < n) (hcomp : 0 ≤ st.compCanon)
    (heq : Equitable ctx level st.lab st.ptn)
    (hlab : LabOk st.lab n) (hlsz : st.lab.size = n)
    (hpsz : st.ptn.size = n) (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    (chooseTarget false ctx tcLevel level numcells st).1 =
      Int.ofNat (specTargetcell ctx st.lab st.ptn level tcLevel) := by
  have hm := maketargetcell_eq_spec (tcLevel := tcLevel) heq hlab hlsz hpsz hend
  simp only [chooseTarget, hnc, decide_true, hcomp, Bool.or_true,
    Bool.and_self, Bool.false_eq_true, Bool.not_false, Bool.true_and,
    Bool.false_and, ite_true, ite_false, show ¬ st.compCanon < 0 by omega,
    decide_false, hm, Id.run_pure, specMaketargetcell]

/-- In the hinted arm, retaining first-code agreement forces the selected
position to be the recorded first-path target. -/
theorem chooseTarget_hinted {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (hnc : numcells < n) (hlevel : 0 < level)
    (heq : st.eqlevFirst = level) (hcomp : st.compCanon < 0)
    (hkeep : (chooseTarget false ctx tcLevel level numcells st).2.2.2.eqlevFirst = level) :
    (chooseTarget false ctx tcLevel level numcells st).1 = st.firsttc[level]! := by
  unfold chooseTarget at hkeep ⊢
  simp only [hnc, decide_true, heq, beq_self_eq_true, Bool.true_or,
    Bool.and_self, Bool.false_eq_true, Bool.not_false, Bool.true_and,
    hcomp, ite_true, ite_false] at hkeep ⊢
  simp only [apply_ite Id.run, Id.run_pure, apply_ite Prod.snd,
    apply_ite Search.eqlevFirst, apply_ite Prod.fst, ite_self] at hkeep ⊢
  split at hkeep
  · omega
  · rename_i hmatch
    simpa only [bne_iff_ne, ne_eq, Decidable.not_not] using hmatch

/-- Both target-selection arms follow the stored position while first-code
agreement survives, provided the unhinted choice follows the reference. -/
theorem chooseTarget_match {ctx : Ctx n} {tcLevel level numcells : Nat}
    {st : Search n} (hnc : numcells < n) (hlevel : 0 < level)
    (heq : st.eqlevFirst = level)
    (hkeep : (chooseTarget false ctx tcLevel level numcells st).2.2.2.eqlevFirst = level)
    (hchoice : Int.ofNat (specTargetcell ctx st.lab st.ptn level tcLevel) =
      st.firsttc[level]!)
    (hequitable : Equitable ctx level st.lab st.ptn)
    (hlab : LabOk st.lab n) (hlsz : st.lab.size = n)
    (hpsz : st.ptn.size = n) (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    (chooseTarget false ctx tcLevel level numcells st).1 = st.firsttc[level]! := by
  by_cases hcomp : st.compCanon < 0
  · exact chooseTarget_hinted hnc hlevel heq hcomp hkeep
  · exact (chooseTarget_unhinted hnc (by omega) hequitable hlab hlsz hpsz hend).trans hchoice

/-- Off-path target selection changes only first-code agreement and the
target-size counter; in particular the reference target history is frozen. -/
theorem chooseTarget_fields (ctx : Ctx n) (tcLevel level numcells : Nat)
    (st : Search n) :
    let out := (chooseTarget false ctx tcLevel level numcells st).2.2.2
    out = { st with eqlevFirst := out.eqlevFirst, tctotal := out.tctotal } := by
  unfold chooseTarget
  simp only [Bool.false_eq_true, ite_false, apply_ite Id.run, Id.run_pure,
    apply_ite Prod.snd]
  repeat' split
  all_goals rfl

end Hex.GraphIso.Nauty.Engine
