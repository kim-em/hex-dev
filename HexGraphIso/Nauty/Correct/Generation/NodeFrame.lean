/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Loop
public import HexGraphIso.Nauty.Correct.Generation.Internal
public import HexGraphIso.Nauty.Correct.Certify
import all HexGraphIso.Nauty.Invariant.Codes
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty

open Generation

variable {n k : Nat} {G : Colored n k} {ctx : Ctx n}

/-- Refining a valid node preserves the tree's cell-count depth bound. -/
theorem NodeInv.tree {tcLevel level numcells : Nat} {codes bs fs : List Nat}
    {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (h : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hg : ctx.g = rowsOf G) (hn : 0 < n) (hl : 1 ≤ level) :
    TreeOk ctx level (refine ctx level st.lab st.ptn st.active numcells) := by
  obtain ⟨hit, heqt, hcount⟩ := h.refined hg hn hl
  refine ⟨hit, heqt, hcount, ?_⟩
  let rs := refine ctx level st.lab st.ptn st.active numcells
  let out : SearchSt n := { st with lab := rs.lab, ptn := rs.ptn }
  have hout : SearchOk G level rs.numcells out :=
    refine_searchOk hn h.run.searchOk hl rfl rfl (Or.inl rfl)
  have hb := hout.bc
  have hc := hout.count
  change level ≤ rs.numcells
  omega

/-- Sweep preparation preserves the stored first reference and boundary. -/
theorem sweepStart_fields (ctx : Ctx n) (level numcells len : Nat) (st : SearchSt n) :
    FirstFields st (sweepStart ctx level numcells len st) := by
  unfold sweepStart
  dsimp only
  split
  all_goals exact ⟨otherNodePrep_firstcode _ _ _, prepF_firsttc _ _ _,
    prepF_firstlab _ _ _, prepF_allsamelevel _ _ _⟩

/-- A first-reference match at an internal node starts a verified sweep
of the specification's target cell. Its visit evidence comes from the
established totality proof, including the actual pruning decisions. -/
theorem NodeInv.referenceSweep {inf tcLevel specFuel runFuel level numcells : Nat}
    {codes bs fs : List Nat} {st : SearchSt n} {best : Option (Key n)} {trail : FrameTrail}
    (hg : ctx.g = rowsOf G) (hinf : inf = n + 2) (hn0 : 0 < n)
    (hlevel : 2 ≤ level) (hpath : level = codes.length + 1)
    (hspec : level + 1 + specFuel = n + 1)
    (hfuel : n + 2 < level + 1 + runFuel)
    (hcheap : st.noncheaplevel ≤ level)
    (hdesc : CheapDesc ctx level st.noncheaplevel
      (refine ctx level st.lab st.ptn st.active numcells))
    (hnode : NodeInv G ctx tcLevel level codes bs fs numcells st best trail)
    (hlive : Live ctx level st trail)
    (hpathOk : PathOk ctx (initPtn n (n + 2) (initialPartition G).2)
      (initialPartition G).1 level st)
    (horb : OrbSound (OrbConn st.genTrace.toList n) st.orbits n)
    (hcoset : st.cosetindex < n)
    (hdom : ∀ b, best = some b → keyLe (pathLeafKey ctx fs st.firstlab) b)
    (hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells < n)
    (heq : (otherLeafSt ctx level numcells st).eqlevFirst = level) :
    let rs := refine ctx level st.lab st.ptn st.active numcells
    let full := codes ++ [rs.longcode]
    ∃ tc len,
      let tcell := worksetOf n rs.lab tc (tc + len - 1)
      let start := sweepStart ctx level numcells len st
      specMaketargetcell ctx rs.lab rs.ptn level tcLevel = (tc, tcell, len) ∧
      OtherSweep G ctx inf tcLevel specFuel runFuel level rs.numcells tc len
        ((tcell.nextElem none).getD 0) st.noncheaplevel full fs rs.lab rs.ptn start
        (n + 1) none tcell start best trail := by
  intro rs full
  obtain ⟨tc, len, hmk, _, _, hloop⟩ :=
    LoopInv.NodeInv.otherSweep (specFuel := specFuel) hg hn0 (by omega) hpath hnode
      (Nat.ne_of_lt hnum) (Or.inl heq) (by omega)
  have hh := hnode.sweepHyp hg hn0 (by omega) hcheap hdesc hlive hpathOk horb hcoset hdom hloop
  have hlen := hloop.lenTwo
  have hfull : level = full.length := by
    simp only [full, List.length_append, List.length_singleton]
    omega
  obtain ⟨_, _, _, _, _, htrace⟩ :=
    otherLoopTotal (stem := codes) (codes := full) (tv1 := ((worksetOf n rs.lab tc (tc + len - 1)).nextElem none).getD 0)
      (tail := len - 1) hg hinf hn0 (totalAll G ctx inf tcLevel runFuel).1 hfuel hspec hfull
      (by simp only [full, List.take_left']) (by omega) rfl (by omega)
      (n + 1) none _ _ best trail bs hh (by simp only [cursorRank]; omega)
  refine ⟨tc, len, ?_, htrace⟩
  have href := hnode.refined hg hn0 (by omega)
  exact (maketargetcell_eq_spec href.2.1 href.1.ok.labOk href.1.ok.labSize
    href.1.ok.ptnSize href.1.ok.ptnEnd).symm.trans hmk

/-- The matching-node equation uses the same prepared state as the
verified loop invariant. -/
theorem other_internal_sweep {inf tcLevel fuel level numcells tc : Nat} {st : SearchSt n}
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
    let mt := specMaketargetcell ctx rs.lab rs.ptn level tcLevel
    let result := otherChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells mt.1
      ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1
      (sweepStart ctx level numcells mt.2.2 st)
    otherNode ctx inf tcLevel (fuel + 1) level numcells st =
      match result.1 with
      | some r => (r, result.2)
      | none => (Int.ofNat level - 1, result.2) := by
  rw [other_internal hnum hok heq hm hleaf hlevel hclear]
  dsimp only
  unfold sweepStart
  dsimp only
  cases hc : cheapautom (otherLeafSt ctx level numcells st).ptn level n <;>
    simp only [Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ite_true, ite_false]
  all_goals rfl

end Hex.GraphIso.Nauty
