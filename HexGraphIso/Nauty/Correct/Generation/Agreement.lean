/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Control
public import HexGraphIso.Nauty.Correct.FirstPath.Loop
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


/-- After the guiding vertex, every child is off-path and preserves the
agreement at the receiving frame, including on early returns. -/
theorem firstTail_agreement (ctx : Ctx n) (inf tcLevel fuel : Nat) :
    ∀ cfuel level numcells tc tv1 cursor tcell index (st : SearchSt n),
      (∀ v, cursor = some v → tv1 < v) → level ≤ st.eqlevFirst →
      level ≤ (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1
        cursor tcell index st).2.2.eqlevFirst := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor tcell index st _ hs
    simpa only [firstChildLoop] using hs
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor tcell index st hafter hs
    cases cursor with
    | none => simpa only [firstChildLoop] using hs
    | some tv =>
      have htv := hafter tv rfl
      have hnext : ∀ cell : VSet n, ∀ v, cell.nextElem (some tv) = some v → tv1 < v := by
        intro cell v hv
        have hv' : tv < v := nextElem_after hv
        omega
      cases hrep : st.orbits[tv]! == tv with
      | false =>
        rw [firstChildLoop_skip ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st hrep]
        exact ih _ _ _ _ _ _ _ _ (hnext _) hs
      | true =>
        have hother : (tv == tv1) = false := by simp only [beq_eq_false_iff_ne]; omega
        let child : SearchSt n := { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
          cosetindex := tv }
        have hc := other_agreement ctx inf tcLevel level fuel (level + 1) (numcells + 1)
          child (by omega) hs
        obtain ⟨r, out, hout⟩ : ∃ r out,
            otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) := ⟨_, _, rfl⟩
        rw [hout] at hc
        by_cases hearly : r < Int.ofNat level
        · rw [firstChildLoop_earlyOther ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st
            r out hrep hother hout hearly]
          exact hc
        · rw [firstChildLoop_stayOther ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st
            r out hrep hother hout hearly]
          dsimp only
          apply ih _ _ _ _ _ _ _ _ (hnext _)
          apply recover_agreement (Nat.le_refl _)
          cases out.needshortprune <;> exact hc

/-- Agreement installed by the guiding child survives the rest of its
parent's sweep. -/
theorem firstGuide_agreement {ctx : Ctx n} {inf tcLevel fuel cfuel level numcells tc tv index : Nat}
    {tcell : VSet n} {st out : SearchSt n} {r : Int}
    (hrep : (st.orbits[tv]! == tv) = true)
    (hcall : firstPathNode ctx inf tcLevel fuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (r, out))
    (hs : level ≤ out.eqlevFirst) :
    level ≤ (firstChildLoop ctx inf tcLevel fuel (cfuel + 1) level numcells tc tv
      (some tv) tcell index st).2.2.eqlevFirst := by
  by_cases hearly : r < Int.ofNat level
  · rw [firstChildLoop_earlyGuide ctx inf tcLevel fuel cfuel level numcells tc tv tv tcell index st
      r out hrep (by simp) hcall hearly]
    exact hs
  · rw [firstChildLoop_stayGuide ctx inf tcLevel fuel cfuel level numcells tc tv tv tcell index st
      r out hrep (by simp) hcall hearly]
    dsimp only
    apply firstTail_agreement ctx inf tcLevel fuel cfuel _ _ _ _ _ _ _ _
      (fun _ hv => nextElem_after hv)
    apply recover_agreement (Nat.le_refl _)
    cases out.needshortprune <;> exact hs

end Hex.GraphIso.Nauty.Generation
