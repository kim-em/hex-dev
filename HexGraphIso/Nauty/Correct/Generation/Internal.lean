/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Leaf
import all HexGraphIso.Nauty.Correct.Base
import all HexGraphIso.Nauty.Correct.Generation.Control
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat} {ctx : Ctx n}

set_option maxHeartbeats 800000 in
/-- A matching internal occurrence reaches the specification target sweep.
Neither the canonical comparison nor the saved pruning boundaries can
cause an immediate return from this node. -/
theorem other_internal {inf tcLevel fuel level numcells tc : Nat} {st : SearchSt n}
    {targets : List Nat} {key : Key n}
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells < n)
    (hok : IterOk ctx level (refine ctx level st.lab st.ptn st.active numcells))
    (heq : Equitable ctx level (refine ctx level st.lab st.ptn st.active numcells).lab
      (refine ctx level st.lab st.ptn st.active numcells).ptn)
    (hm : Matches ctx level st (tc :: targets) key)
    (hleaf : HasLeaf ctx tcLevel level (refine ctx level st.lab st.ptn st.active numcells)
      (tc :: targets) key)
    (hlevel : st.eqlevFirst = level - 1) (hclear : st.needshortprune = false) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let pre := otherLeafSt ctx level numcells st
    let mt := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
    let target := { pre with tctotal := pre.tctotal + mt.2.2 }
    let ready := if ¬ cheapautom target.ptn level n then
      { target with noncheaplevel := level + 1 } else target
    let result := otherChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells mt.1
      ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 ready
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      match result.1 with
      | some r => (r, result.2)
      | none => (Int.ofNat level - 1, result.2) := by
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let pre := otherLeafSt ctx level numcells st
  let mt := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
  have hlab : pre.lab = rs.lab := prepF_lab _ _ _
  have hptn : pre.ptn = rs.ptn := prepF_ptn _ _ _
  have htc : pre.firsttc = st.firsttc := prepF_firsttc _ _ _
  have hfirst : pre.eqlevFirst = level := by
    apply (hm.stateEq (out := { st with
      lab := rs.lab, ptn := rs.ptn, active := rs.active, numnodes := st.numnodes + 1 }) rfl rfl rfl).prep hleaf
    exact hlevel
  have hhint : maketargetcell ctx pre.lab pre.ptn level tcLevel pre.firsttc[level]! = mt := by
    rw [hlab, hptn, htc]
    exact hm.target_spec hleaf hok heq
  have hsame : Int.ofNat mt.1 = pre.firsttc[level]! := by
    rw [← hhint, hlab, hptn, htc]
    exact hm.target hleaf hok heq
  have hplain : maketargetcell ctx pre.lab pre.ptn level tcLevel (-1) = mt := by
    rw [hlab, hptn]
    exact maketargetcell_eq_spec heq hok.ok.labOk hok.ok.labSize hok.ok.ptnSize hok.ok.ptnEnd
  let target := { pre with tctotal := pre.tctotal + mt.2.2 }
  change rs.numcells < n at hnum
  have hp : processnode ctx level rs.numcells target = (Int.ofNat level, target) :=
    processnode_internal (by simp only [target, hfirst, ne_eq, not_true_eq_false, false_and, not_false_eq_true])
      (by simp only [beq_iff_eq]; omega)
  have hc : target.needshortprune = false := (otherLeafSt_short ctx level numcells st).trans hclear
  have hstate : otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      finish ctx inf tcLevel fuel level rs.numcells (Int.ofNat mt.1) mt.2.1 target := by
    rw [otherNode]
    dsimp only
    change (if rs.numcells < n ∧ ((pre.eqlevFirst == level) = true ∨ pre.compCanon ≥ (0 : Int)) then
      (if pre.compCanon < (0 : Int) then _ else _) else _) = _
    rw [ite_eq_left ⟨hnum, Or.inl (by simp [hfirst])⟩]
    dsimp only [pre, otherLeafSt, rs] at hhint hplain hsame
    by_cases hneg : pre.compCanon < (0 : Int)
    · rw [ite_eq_left hneg, hhint]
      rw [ite_eq_right (by exact not_not_intro hsame)]
      rfl
    · rw [ite_eq_right hneg, hplain]
      rfl
  rw [hstate]
  change finish ctx inf tcLevel fuel level rs.numcells (Int.ofNat mt.1) mt.2.1 target = _
  let ready := if ¬ cheapautom target.ptn level n then
    { target with noncheaplevel := level + 1 } else target
  let result := otherChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells mt.1
    ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 ready
  change finish ctx inf tcLevel fuel level rs.numcells (Int.ofNat mt.1) mt.2.1 target =
    match result.1 with
    | some r => (r, result.2)
    | none => (Int.ofNat level - 1, result.2)
  dsimp only [result, ready]
  unfold finish
  rw [hp]
  simp only [Int.lt_irrefl, ↓reduceIte, hc, Bool.false_eq_true, Int.ofNat_eq_natCast, Int.toNat_natCast]
  split <;>
    generalize hres : otherChildLoop ctx inf tcLevel fuel (n + 1) level _ _ _ _ _ _ = result <;>
    obtain ⟨r, out⟩ := result <;> cases r <;> rfl

end Hex.GraphIso.Nauty.Generation
