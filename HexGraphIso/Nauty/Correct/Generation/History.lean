/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Matching
import all HexGraphIso.Nauty.Correct.Generation.Control
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Domination
import all HexGraphIso.Nauty.Invariant.Codes

public section

namespace Hex.GraphIso.Nauty.Generation

variable {n : Nat}

/-- Equality of the stored first reference, including its target hints and all-same boundary. -/
structure FirstFields (st out : SearchSt n) : Prop where
  codes : out.firstcode = st.firstcode
  targets : out.firsttc = st.firsttc
  lab : out.firstlab = st.firstlab
  same : out.allsamelevel = st.allsamelevel

namespace FirstFields

variable {a b c : SearchSt n}

theorem refl (st : SearchSt n) : FirstFields st st := ⟨rfl, rfl, rfl, rfl⟩

theorem trans (h : FirstFields a b) (h' : FirstFields b c) : FirstFields a c :=
  ⟨h'.codes.trans h.codes, h'.targets.trans h.targets, h'.lab.trans h.lab, h'.same.trans h.same⟩

theorem matching {ctx : Ctx n} {level : Nat} {targets : List Nat} {key : Key n}
    (h : FirstFields a b) (hm : Matches ctx level a targets key) :
    Matches ctx level b targets key := hm.stateEq h.codes h.targets h.lab

theorem process (ctx : Ctx n) (level numcells : Nat) (st : SearchSt n) :
    FirstFields st (processnode ctx level numcells st).2 :=
  ⟨processnode_firstcode _ _ _ _, processnode_firsttc _ _ _ _, processnode_firstlab _ _ _ _,
    processnode_allsamelevel _ _ _ _⟩

theorem recover (inf level : Nat) (st : SearchSt n) :
    FirstFields st (Nauty.recover n inf level st) :=
  ⟨recover_firstcode _ _ _ _, recF_firsttc _ _ _ _, recF_firstlab _ _ _ _, recF_allsamelevel _ _ _ _⟩

end FirstFields

private theorem otherLoop_fields {ctx : Ctx n} {inf tcLevel fuel : Nat}
    (hnode : ∀ level numcells (st : SearchSt n),
      FirstFields st (otherNode ctx inf tcLevel fuel level numcells st).2) :
    ∀ cfuel level numcells tc tv1 cursor tcell (st : SearchSt n),
      FirstFields st (otherChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor tcell st).2 := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor tcell st
    simpa only [otherChildLoop] using FirstFields.refl st
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor tcell st
    cases cursor with
    | none => simpa only [otherChildLoop] using FirstFields.refl st
    | some tv =>
      let child : SearchSt n := { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      have hc := hnode (level + 1) (numcells + 1) child
      obtain ⟨r, out, hout⟩ : ∃ r out,
          otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) := ⟨_, _, rfl⟩
      rw [hout] at hc
      have hc' : FirstFields st out := ⟨hc.codes, hc.targets, hc.lab, hc.same⟩
      by_cases hearly : r < Int.ofNat level
      · rw [otherChildLoop_early ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell st r out hout hearly]
        exact ⟨hc'.codes, hc'.targets, hc'.lab, hc'.same⟩
      · rw [otherChildLoop_stay ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell st r out hout hearly]
        dsimp only
        apply FirstFields.trans _ (ih _ _ _ _ _ _ _)
        apply hc'.trans
        apply FirstFields.trans _ (FirstFields.recover inf level _)
        cases out.needshortprune <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem finish_fields {ctx : Ctx n} {inf tcLevel fuel : Nat}
    (hnode : ∀ level numcells (st : SearchSt n),
      FirstFields st (otherNode ctx inf tcLevel fuel level numcells st).2)
    (level numcells : Nat) (tc : Int) (tcell : VSet n) (st : SearchSt n) :
    FirstFields st (finish ctx inf tcLevel fuel level numcells tc tcell st).2 := by
  have hp := FirstFields.process ctx level numcells st
  unfold finish
  generalize he : processnode ctx level numcells st = res at hp ⊢
  obtain ⟨r, out⟩ := res
  dsimp only
  by_cases hearly : r < Int.ofNat level
  · rw [ite_eq_left hearly]
    exact hp
  · rw [ite_eq_right hearly]
    have htail : ∀ (cell : VSet n) (pre : SearchSt n), FirstFields st pre →
        FirstFields st (match (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
              ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).1 with
          | some r => (r, (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells
              tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).2)
          | none => (Int.ofNat level - 1,
              (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
                ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).2)).2 := by
      intro cell pre hpre
      have hl := hpre.trans (otherLoop_fields hnode (n + 1) level numcells tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre)
      generalize hr : otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre = result at hl ⊢
      obtain ⟨r, out⟩ := result
      cases r <;> exact hl
    cases out.needshortprune <;> simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> apply htail
    all_goals exact ⟨hp.codes, hp.targets, hp.lab, hp.same⟩

/-- Off-path recursion preserves the first reference's codes, hints,
labelling, and all-same boundary, independently of all pruning and return choices. -/
theorem other_fields (ctx : Ctx n) (inf tcLevel : Nat) :
    ∀ fuel level numcells (st : SearchSt n),
      FirstFields st (otherNode ctx inf tcLevel fuel level numcells st).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st
    simpa only [otherNode] using FirstFields.refl st
  | succ fuel ih =>
    intro level numcells st
    rw [otherNode]
    dsimp only
    generalize hprep : otherNodePrep level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        numnodes := st.numnodes + 1,
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab,
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn,
        active := (refine ctx level st.lab st.ptn st.active numcells).active } = pre
    have hm : FirstFields st pre := by
      rw [← hprep]
      exact ⟨otherNodePrep_firstcode _ _ _, prepF_firsttc _ _ _, prepF_firstlab _ _ _, prepF_allsamelevel _ _ _⟩
    have htail : ∀ tc cell (p : SearchSt n), FirstFields st p →
        FirstFields st (finish ctx inf tcLevel fuel level
          (refine ctx level st.lab st.ptn st.active numcells).numcells tc cell p).2 :=
      fun tc cell p hp => hp.trans (finish_fields ih _ _ tc cell p)
    by_cases ht : (refine ctx level st.lab st.ptn st.active numcells).numcells < n ∧
        ((pre.eqlevFirst == level) = true ∨ pre.compCanon ≥ (0 : Int))
    · rw [ite_eq_left ht]
      by_cases hcomp : pre.compCanon < (0 : Int)
      · rw [ite_eq_left hcomp]
        by_cases hh : Int.ofNat
            (maketargetcell ctx pre.lab pre.ptn level tcLevel pre.firsttc[level]!).1 ≠ pre.firsttc[level]!
        · rw [ite_eq_left hh]
          apply htail; exact ⟨hm.codes, hm.targets, hm.lab, hm.same⟩
        · rw [ite_eq_right hh]
          apply htail; exact ⟨hm.codes, hm.targets, hm.lab, hm.same⟩
      · rw [ite_eq_right hcomp]
        apply htail; exact ⟨hm.codes, hm.targets, hm.lab, hm.same⟩
    · rw [ite_eq_right ht]
      apply htail; exact ⟨hm.codes, hm.targets, hm.lab, hm.same⟩

/-- The saved all-same boundary remains strictly deeper than the
first-path guide throughout an off-path subtree. -/
theorem other_boundary {ctx : Ctx n} {inf tcLevel fuel level numcells : Nat} {st : SearchSt n}
    (hclear : st.needshortprune = false) (hboundary : st.gcaFirst < st.allsamelevel) :
    (otherNode ctx inf tcLevel fuel level numcells st).2.gcaFirst <
      (otherNode ctx inf tcLevel fuel level numcells st).2.allsamelevel := by
  rw [(node_control ctx inf tcLevel fuel level numcells st hclear).1,
    (other_fields ctx inf tcLevel fuel level numcells st).same]
  exact hboundary

/-- Once the guiding vertex has been visited, a first-path sibling sweep
preserves the complete stored first reference. All later recursive calls
are off-path, including after target-set filters. -/
theorem firstTail_fields (ctx : Ctx n) (inf tcLevel fuel : Nat) :
    ∀ cfuel level numcells tc tv1 cursor tcell index (st : SearchSt n),
      (∀ v, cursor = some v → tv1 < v) →
      FirstFields st (firstChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1
        cursor tcell index st).2.2 := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor tcell index st _
    simpa only [firstChildLoop] using FirstFields.refl st
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor tcell index st hafter
    cases cursor with
    | none => simpa only [firstChildLoop] using FirstFields.refl st
    | some tv =>
      have htv := hafter tv rfl
      have hnext : ∀ cell : VSet n, ∀ v, cell.nextElem (some tv) = some v → tv1 < v := by
        intro cell v hv
        have hv' : tv < v := nextElem_after hv
        omega
      cases hrep : st.orbits[tv]! == tv with
      | false =>
        rw [firstChildLoop_skip ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st hrep]
        exact ih _ _ _ _ _ _ _ _ (hnext _)
      | true =>
        have hother : (tv == tv1) = false := by simp only [beq_eq_false_iff_ne]; omega
        let child : SearchSt n := { st with
          lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
          ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
          active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
          fixedpts := st.fixedpts.insert tv
          cosetindex := tv }
        have hc := other_fields ctx inf tcLevel fuel (level + 1) (numcells + 1) child
        obtain ⟨r, out, hout⟩ : ∃ r out,
            otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) := ⟨_, _, rfl⟩
        rw [hout] at hc
        have hc' : FirstFields st out := ⟨hc.codes, hc.targets, hc.lab, hc.same⟩
        by_cases hearly : r < Int.ofNat level
        · rw [firstChildLoop_earlyOther ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st
            r out hrep hother hout hearly]
          exact ⟨hc'.codes, hc'.targets, hc'.lab, hc'.same⟩
        · rw [firstChildLoop_stayOther ctx inf tcLevel fuel cfuel level numcells tc tv1 tv tcell index st
            r out hrep hother hout hearly]
          dsimp only
          apply FirstFields.trans _ (ih _ _ _ _ _ _ _ _ (hnext _))
          apply hc'.trans
          apply FirstFields.trans _ (FirstFields.recover inf level _)
          cases out.needshortprune <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- After the guiding recursive call, every remaining first-path sibling
retains the exact reference that call installed. This includes early
unwinds and the short-prune/recovery path. -/
theorem firstGuide_fields {ctx : Ctx n} {inf tcLevel fuel cfuel level numcells tc tv index : Nat}
    {tcell : VSet n} {st out : SearchSt n} {r : Int}
    (hrep : (st.orbits[tv]! == tv) = true)
    (hcall : firstPathNode ctx inf tcLevel fuel (level + 1) (numcells + 1)
      { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv
        cosetindex := tv } = (r, out)) :
    FirstFields out (firstChildLoop ctx inf tcLevel fuel (cfuel + 1) level numcells tc tv
      (some tv) tcell index st).2.2 := by
  by_cases hearly : r < Int.ofNat level
  · rw [firstChildLoop_earlyGuide ctx inf tcLevel fuel cfuel level numcells tc tv tv tcell index st
      r out hrep (by simp) hcall hearly]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [firstChildLoop_stayGuide ctx inf tcLevel fuel cfuel level numcells tc tv tv tcell index st
      r out hrep (by simp) hcall hearly]
    dsimp only
    apply FirstFields.trans _ (firstTail_fields ctx inf tcLevel fuel cfuel _ _ _ _ _ _ _ _ ?_)
    · apply FirstFields.trans _ (FirstFields.recover inf level _)
      cases out.needshortprune <;> exact ⟨rfl, rfl, rfl, rfl⟩
    · intro v hv
      exact nextElem_after hv

end Hex.GraphIso.Nauty.Generation
