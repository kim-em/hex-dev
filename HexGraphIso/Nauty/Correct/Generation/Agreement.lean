/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Control
import all HexGraphIso.Nauty.Correct.Generation.Control
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Invariant.Codes

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

private theorem recover_agreement {inf level floor : Nat} {st : SearchSt n}
    (hl : floor ≤ level) (hs : floor ≤ st.eqlevFirst) :
    floor ≤ (recover n inf level st).eqlevFirst := by
  rw [recover_eqlevFirst]
  split <;> assumption

private theorem otherLoop_agreement {ctx : Ctx n} {inf tcLevel fuel floor : Nat}
    (hnode : ∀ level numcells (st : SearchSt n), floor < level → floor ≤ st.eqlevFirst →
      floor ≤ (otherNode ctx inf tcLevel fuel level numcells st).2.eqlevFirst) :
    ∀ cfuel level numcells tc tv1 cursor tcell (st : SearchSt n),
      floor ≤ level → floor ≤ st.eqlevFirst →
      floor ≤ (otherChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor tcell st).2.eqlevFirst := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor tcell st hl hs
    simpa only [otherChildLoop] using hs
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor tcell st hl hs
    cases cursor with
    | none => simpa only [otherChildLoop] using hs
    | some tv =>
      let child : SearchSt n := { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      have hc := hnode (level + 1) (numcells + 1) child (by omega) hs
      obtain ⟨r, out, hout⟩ : ∃ r out,
          otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) := ⟨_, _, rfl⟩
      rw [hout] at hc
      by_cases hearly : r < Int.ofNat level
      · rw [otherChildLoop_early ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell st r out hout hearly]
        exact hc
      · rw [otherChildLoop_stay ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell st r out hout hearly]
        dsimp only
        apply ih _ _ _ _ _ _ _ hl
        apply recover_agreement hl
        cases out.needshortprune <;> exact hc

private theorem finish_agreement {ctx : Ctx n} {inf tcLevel fuel floor : Nat}
    (hnode : ∀ level numcells (st : SearchSt n), floor < level → floor ≤ st.eqlevFirst →
      floor ≤ (otherNode ctx inf tcLevel fuel level numcells st).2.eqlevFirst)
    (level numcells : Nat) (tc : Int) (tcell : VSet n) (st : SearchSt n)
    (hl : floor ≤ level) (hs : floor ≤ st.eqlevFirst) :
    floor ≤ (finish ctx inf tcLevel fuel level numcells tc tcell st).2.eqlevFirst := by
  have hp : floor ≤ (processnode ctx level numcells st).2.eqlevFirst := by
    rw [processnode_eqlevFirst]
    exact hs
  unfold finish
  generalize he : processnode ctx level numcells st = res at hp ⊢
  obtain ⟨r, out⟩ := res
  dsimp only
  by_cases hearly : r < Int.ofNat level
  · rw [ite_eq_left hearly]
    exact hp
  · rw [ite_eq_right hearly]
    have htail : ∀ (cell : VSet n) (pre : SearchSt n), floor ≤ pre.eqlevFirst →
        floor ≤ (match (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
              ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).1 with
          | some r => (r, (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells
              tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).2)
          | none => (Int.ofNat level - 1,
              (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
                ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).2)).2.eqlevFirst := by
      intro cell pre hpre
      have hloop := otherLoop_agreement hnode (n + 1) level numcells tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre hl hpre
      generalize hr : otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre = result at hloop ⊢
      obtain ⟨r, out⟩ := result
      cases r <;> exact hloop
    cases out.needshortprune <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> apply htail
    all_goals exact hp

/-- Off-path recursion cannot erase first-reference agreement strictly
above its entry level. This follows the actual updates, without assuming
that the comparison invariant records maximal agreement. -/
theorem other_agreement (ctx : Ctx n) (inf tcLevel floor : Nat) :
    ∀ fuel level numcells (st : SearchSt n), floor < level → floor ≤ st.eqlevFirst →
      floor ≤ (otherNode ctx inf tcLevel fuel level numcells st).2.eqlevFirst := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st hl hs
    simpa only [otherNode] using hs
  | succ fuel ih =>
    intro level numcells st hl hs
    rw [otherNode]
    dsimp only
    generalize hprep : otherNodePrep level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        numnodes := st.numnodes + 1,
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab,
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn,
        active := (refine ctx level st.lab st.ptn st.active numcells).active } = pre
    have hm : floor ≤ pre.eqlevFirst := by
      rw [← hprep, otherNodePrep_eqlevFirst]
      split
      · omega
      · exact hs
    have htail : ∀ tc cell (p : SearchSt n), floor ≤ p.eqlevFirst →
        floor ≤ (finish ctx inf tcLevel fuel level
          (refine ctx level st.lab st.ptn st.active numcells).numcells tc cell p).2.eqlevFirst :=
      fun tc cell p hp => finish_agreement ih _ _ tc cell p (by omega) hp
    by_cases ht : (refine ctx level st.lab st.ptn st.active numcells).numcells < n ∧
        ((pre.eqlevFirst == level) = true ∨ pre.compCanon ≥ (0 : Int))
    · rw [ite_eq_left ht]
      by_cases hcomp : pre.compCanon < (0 : Int)
      · rw [ite_eq_left hcomp]
        by_cases hh : Int.ofNat
            (maketargetcell ctx pre.lab pre.ptn level tcLevel pre.firsttc[level]!).1 ≠ pre.firsttc[level]!
        · rw [ite_eq_left hh]
          apply htail
          dsimp only
          omega
        · rw [ite_eq_right hh]
          apply htail
          exact hm
      · rw [ite_eq_right hcomp]
        apply htail
        exact hm
    · rw [ite_eq_right ht]
      apply htail
      exact hm

end Hex.GraphIso.Nauty.Generation
