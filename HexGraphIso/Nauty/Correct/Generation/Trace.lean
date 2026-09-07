/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Control
public import HexGraphIso.Nauty.Correct.FirstPath.Hyp
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Correct.Generation.Control

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- Recording an automorphism never discards earlier trace entries. -/
theorem process_retains {ctx : Ctx n} {level numcells : Nat} {st : SearchSt n}
    {γ : Array Nat} (hγ : γ ∈ st.genTrace) :
    γ ∈ (processnode ctx level numcells st).2.genTrace := by
  rcases processnode_genOrb ctx level numcells st with he | ⟨δ, he⟩
  · have h := congrArg Prod.fst he
    change (processnode ctx level numcells st).2.genTrace = st.genTrace at h
    rw [h]
    exact hγ
  · have h := congrArg Prod.fst he
    change (processnode ctx level numcells st).2.genTrace = st.genTrace.push δ at h
    rw [h]
    exact Array.mem_push.mpr (Or.inl hγ)

private theorem otherLoop_retains {ctx : Ctx n} {inf tcLevel fuel : Nat}
    (hnode : ∀ level numcells (st : SearchSt n) {γ : Array Nat}, γ ∈ st.genTrace →
      γ ∈ (otherNode ctx inf tcLevel fuel level numcells st).2.genTrace) :
    ∀ cfuel level numcells tc tv1 cursor tcell (st : SearchSt n) {γ : Array Nat},
      γ ∈ st.genTrace → γ ∈
        (otherChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor tcell st).2.genTrace := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor tcell st γ hγ
    simpa only [otherChildLoop] using hγ
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor tcell st γ hγ
    cases cursor with
    | none => simpa only [otherChildLoop] using hγ
    | some tv =>
      let child : SearchSt n := { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      have hc := hnode (level + 1) (numcells + 1) child hγ
      obtain ⟨r, out, hout⟩ : ∃ r out,
          otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) :=
        ⟨_, _, rfl⟩
      rw [hout] at hc
      by_cases hearly : r < Int.ofNat level
      · rw [otherChildLoop_early ctx inf tcLevel fuel cfuel level numcells tc tv1 tv
          tcell st r out hout hearly]
        exact hc
      · rw [otherChildLoop_stay ctx inf tcLevel fuel cfuel level numcells tc tv1 tv
          tcell st r out hout hearly]
        apply ih
        rw [recover_genTrace]
        cases out.needshortprune <;> exact hc

private theorem finish_retains {ctx : Ctx n} {inf tcLevel fuel : Nat}
    (hnode : ∀ level numcells (st : SearchSt n) {γ : Array Nat}, γ ∈ st.genTrace →
      γ ∈ (otherNode ctx inf tcLevel fuel level numcells st).2.genTrace)
    (level numcells : Nat) (tc : Int) (tcell : VSet n) (st : SearchSt n)
    {γ : Array Nat} (hγ : γ ∈ st.genTrace) :
    γ ∈ (finish ctx inf tcLevel fuel level numcells tc tcell st).2.genTrace := by
  have hp := process_retains (ctx := ctx) (level := level) (numcells := numcells) hγ
  unfold finish
  generalize he : processnode ctx level numcells st = res at hp ⊢
  obtain ⟨r, out⟩ := res
  dsimp only
  by_cases hearly : r < Int.ofNat level
  · rw [ite_eq_left hearly]
    exact hp
  · rw [ite_eq_right hearly]
    have htail : ∀ (cell : VSet n) (pre : SearchSt n), γ ∈ pre.genTrace →
        γ ∈ (match (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
              ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).1 with
          | some r => (r, (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells
              tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).2)
          | none => (Int.ofNat level - 1,
              (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
                ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).2)).2.genTrace := by
      intro cell pre hpre
      have hl := otherLoop_retains hnode (n + 1) level numcells tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre hpre
      generalize hr : otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre = result at hl ⊢
      obtain ⟨r, out⟩ := result
      cases r <;> exact hl
    cases out.needshortprune <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> apply htail <;> exact hp

/-- Off-path recursion keeps all previously recorded generators. -/
theorem other_retains (ctx : Ctx n) (inf tcLevel : Nat) :
    ∀ fuel level numcells (st : SearchSt n) {γ : Array Nat}, γ ∈ st.genTrace →
      γ ∈ (otherNode ctx inf tcLevel fuel level numcells st).2.genTrace := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st γ hγ
    simpa only [otherNode] using hγ
  | succ fuel ih =>
    intro level numcells st γ hγ
    rw [otherNode]
    dsimp only
    generalize hprep : otherNodePrep level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        numnodes := st.numnodes + 1,
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab,
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn,
        active := (refine ctx level st.lab st.ptn st.active numcells).active } = pre
    have hm : γ ∈ pre.genTrace := by
      rw [← hprep, otherNodePrep_genTrace']
      exact hγ
    have htail : ∀ tc cell (p : SearchSt n), γ ∈ p.genTrace →
        γ ∈ (finish ctx inf tcLevel fuel level
            (refine ctx level st.lab st.ptn st.active numcells).numcells tc cell p).2.genTrace :=
      fun tc cell p hp => finish_retains ih _ _ tc cell p hp
    by_cases ht : (refine ctx level st.lab st.ptn st.active numcells).numcells < n ∧
        ((pre.eqlevFirst == level) = true ∨ pre.compCanon ≥ (0 : Int))
    · rw [ite_eq_left ht]
      by_cases hcomp : pre.compCanon < (0 : Int)
      · rw [ite_eq_left hcomp]
        by_cases hh : Int.ofNat
            (maketargetcell ctx pre.lab pre.ptn level tcLevel pre.firsttc[level]!).1 ≠
              pre.firsttc[level]!
        · rw [ite_eq_left hh]
          apply htail; exact hm
        · rw [ite_eq_right hh]
          apply htail; exact hm
      · rw [ite_eq_right hcomp]
        apply htail; exact hm
    · rw [ite_eq_right ht]
      apply htail; exact hm

private theorem firstLoop_retains {ctx : Ctx n} {inf tcLevel fuel : Nat}
    (hnode : ∀ level numcells (st : SearchSt n) {γ : Array Nat}, γ ∈ st.genTrace →
      γ ∈ (firstPathNode ctx inf tcLevel fuel level numcells st).2.genTrace) :
    ∀ cfuel level numcells tc tv1 cursor tcell index (st : SearchSt n) {γ : Array Nat},
      γ ∈ st.genTrace → γ ∈
        (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor tcell index st).2.2.genTrace := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor tcell index st γ hγ
    simpa only [firstChildLoop] using hγ
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor tcell index st γ hγ
    cases cursor with
    | none => simpa only [firstChildLoop] using hγ
    | some tv =>
      cases hrep : st.orbits[tv]! == tv with
      | false =>
        rw [firstChildLoop_skip ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st hrep]
        exact ih _ _ _ _ _ _ _ _ hγ
      | true =>
        let child : SearchSt n := { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
          cosetindex := tv }
        cases hfirst : tv == tv1 with
        | false =>
          have hc := other_retains ctx inf tcLevel fuel (level + 1) (numcells + 1) child hγ
          obtain ⟨r, out, hout⟩ : ∃ r out,
              otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) :=
            ⟨_, _, rfl⟩
          rw [hout] at hc
          by_cases hearly : r < Int.ofNat level
          · rw [firstChildLoop_earlyOther ctx inf tcLevel fuel cfuel level numcells tc tv1 tv
              tcell index st r out hrep hfirst hout hearly]
            exact hc
          · rw [firstChildLoop_stayOther ctx inf tcLevel fuel cfuel level numcells tc tv1 tv
              tcell index st r out hrep hfirst hout hearly]
            apply ih
            rw [recover_genTrace]
            cases out.needshortprune <;> exact hc
        | true =>
          have hc := hnode (level + 1) (numcells + 1) child hγ
          obtain ⟨r, out, hout⟩ : ∃ r out,
              firstPathNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) :=
            ⟨_, _, rfl⟩
          rw [hout] at hc
          by_cases hearly : r < Int.ofNat level
          · rw [firstChildLoop_earlyGuide ctx inf tcLevel fuel cfuel level numcells tc tv1 tv
              tcell index st r out hrep hfirst hout hearly]
            exact hc
          · rw [firstChildLoop_stayGuide ctx inf tcLevel fuel cfuel level numcells tc tv1 tv
              tcell index st r out hrep hfirst hout hearly]
            apply ih
            rw [recover_genTrace]
            cases out.needshortprune <;> exact hc

/-- First-path recursion keeps all previously recorded generators, even
when a bounded pruning-workspace slot is overwritten. -/
theorem first_retains (ctx : Ctx n) (inf tcLevel : Nat) :
    ∀ fuel level numcells (st : SearchSt n) {γ : Array Nat}, γ ∈ st.genTrace →
      γ ∈ (firstPathNode ctx inf tcLevel fuel level numcells st).2.genTrace := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st γ hγ
    simpa only [firstPathNode] using hγ
  | succ fuel ih =>
    intro level numcells st γ hγ
    by_cases hnum : (refine ctx level st.lab st.ptn st.active numcells).numcells = n
    · rw [firstPath_discrete_state ctx inf tcLevel fuel level numcells st hnum]
      rw [(firstterminal_store level _).1]
      exact hγ
    · let rs := refine ctx level st.lab st.ptn st.active numcells
      let mt := maketargetcell ctx rs.lab rs.ptn level tcLevel (-1)
      let pre0 : SearchSt n := { st with
        lab := rs.lab, ptn := rs.ptn, active := rs.active,
        firstcode := st.firstcode.set! level rs.longcode,
        firsttc := st.firsttc.set! level (Int.ofNat mt.1),
        numnodes := st.numnodes + 1, tctotal := st.tctotal + mt.2.2 }
      let pre := if pre0.noncheaplevel ≥ level ∧ ¬ cheapautom pre0.ptn level n then
        { pre0 with noncheaplevel := level + 1 } else pre0
      have hpre : γ ∈ pre.genTrace := by
        dsimp only [pre]
        split <;> exact hγ
      have hl := firstLoop_retains ih (n + 1) level rs.numcells mt.1
        ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre hpre
      rw [firstPath_internal_state ctx inf tcLevel fuel level numcells st hnum]
      change γ ∈ (match (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells
          mt.1 ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre).1 with
        | some r => (r, (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells
            mt.1 ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre).2.2)
        | none => (Int.ofNat level - 1, firstFinish level mt.2.2
            (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells
              mt.1 ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre).2.1
            (firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells
              mt.1 ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre).2.2)).2.genTrace
      generalize he : firstChildLoop ctx inf tcLevel fuel (n + 1) level rs.numcells mt.1
        ((mt.2.1.nextElem none).getD 0) (mt.2.1.nextElem none) mt.2.1 0 pre = result at hl ⊢
      obtain ⟨r, index, out⟩ := result
      cases r
      · simp only [firstFinish]
        split <;> exact hl
      · exact hl


/-- Every generator discovered by the guiding child remains in the
completed sibling sweep, including when that child returns early. -/
theorem firstGuide_retains {ctx : Ctx n} {inf tcLevel fuel cfuel level numcells tc tv index : Nat}
    {tcell : VSet n} {st out : SearchSt n} {r : Int}
    (hrep : (st.orbits[tv]! == tv) = true)
    (hcall : firstPathNode ctx inf tcLevel fuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (r, out))
    {γ : Array Nat} (hγ : γ ∈ out.genTrace) :
    γ ∈ (firstChildLoop ctx inf tcLevel fuel (cfuel + 1) level numcells tc tv
      (some tv) tcell index st).2.2.genTrace := by
  by_cases hearly : r < Int.ofNat level
  · rw [firstChildLoop_earlyGuide ctx inf tcLevel fuel cfuel level numcells tc tv tv tcell index st
      r out hrep (by simp) hcall hearly]
    exact hγ
  · rw [firstChildLoop_stayGuide ctx inf tcLevel fuel cfuel level numcells tc tv tv tcell index st
      r out hrep (by simp) hcall hearly]
    dsimp only
    apply firstLoop_retains (first_retains ctx inf tcLevel fuel)
    rw [recover_genTrace]
    cases out.needshortprune <;> exact hγ

end Hex.GraphIso.Nauty.Generation
