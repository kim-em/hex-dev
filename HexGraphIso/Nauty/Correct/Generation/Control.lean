/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Correct.Generation.Short
import all HexGraphIso.Nauty.Search.Search
import all HexGraphIso.Nauty.Invariant.Domination

public section

namespace Hex.GraphIso.Nauty

namespace Generation

variable {n : Nat}

/-- An off-path node preserves its first-path guide and directs every
outstanding short-prune request to a different frame. -/
def NodeControl (guide : Nat) (result : Int × SearchSt n) : Prop :=
  result.2.gcaFirst = guide ∧
    (result.2.needshortprune = true → result.1 ≠ Int.ofNat guide)

/-- A loop with a live short-prune request has returned early to a frame
different from its first-path guide. -/
def LoopControl (guide : Nat) (result : Option Int × SearchSt n) : Prop :=
  result.2.gcaFirst = guide ∧
    (result.2.needshortprune = true →
      ∃ r, result.1 = some r ∧ r ≠ Int.ofNat guide)

theorem loop_control {ctx : Ctx n} {inf tcLevel fuel : Nat}
    (hnode : ∀ level numcells (st : SearchSt n), st.needshortprune = false →
      NodeControl st.gcaFirst (otherNode ctx inf tcLevel fuel level numcells st)) :
    ∀ cfuel level numcells tc tv1 cursor tcell (st : SearchSt n),
      st.needshortprune = false →
      LoopControl st.gcaFirst
        (otherChildLoop ctx inf tcLevel fuel cfuel level numcells tc tv1 cursor tcell st) := by
  intro cfuel
  induction cfuel with
  | zero =>
    intro level numcells tc tv1 cursor tcell st hc
    simp [otherChildLoop, LoopControl, hc]
  | succ cfuel ih =>
    intro level numcells tc tv1 cursor tcell st hc
    cases cursor with
    | none => simp [otherChildLoop, LoopControl, hc]
    | some tv =>
      let child : SearchSt n := { st with
        lab := (breakout n st.lab st.ptn (level + 1) tc tv).1
        ptn := (breakout n st.lab st.ptn (level + 1) tc tv).2.1
        active := (breakout n st.lab st.ptn (level + 1) tc tv).2.2
        fixedpts := st.fixedpts.insert tv }
      have hchild := hnode (level + 1) (numcells + 1) child hc
      obtain ⟨r, out, hout⟩ : ∃ r out,
          otherNode ctx inf tcLevel fuel (level + 1) (numcells + 1) child = (r, out) :=
        ⟨_, _, rfl⟩
      rw [hout] at hchild
      change out.gcaFirst = st.gcaFirst ∧
        (out.needshortprune = true → r ≠ Int.ofNat st.gcaFirst) at hchild
      by_cases hearly : r < Int.ofNat level
      · rw [otherChildLoop_early ctx inf tcLevel fuel cfuel level numcells tc tv1 tv
          tcell st r out hout hearly]
        exact ⟨hchild.1, fun hs => ⟨r, rfl, hchild.2 hs⟩⟩
      · rw [otherChildLoop_stay ctx inf tcLevel fuel cfuel level numcells tc tv1 tv
          tcell st r out hout hearly]
        dsimp only
        let cleaned := { out with fixedpts := out.fixedpts.erase tv }
        have hclear : (recover n inf level
            (clearShortIf cleaned.needshortprune cleaned)).needshortprune = false := by
          rw [recover_needshortprune]
          cases hs : cleaned.needshortprune <;> simp [clearShortIf, hs]
        have hguide : (recover n inf level
            (clearShortIf cleaned.needshortprune cleaned)).gcaFirst = st.gcaFirst := by
          rw [recF_gcaFirst]
          cases hs : cleaned.needshortprune <;> simpa [clearShortIf] using hchild.1
        rw [← hguide]
        exact ih _ _ _ _ _ _ _ hclear

private def finish (ctx : Ctx n) (inf tcLevel fuel level numcells : Nat)
    (tc : Int) (tcell : VSet n) (st : SearchSt n) : Int × SearchSt n := Id.run do
  let (rtnlevel, st') := processnode ctx level numcells st
  let mut st := st'
  let mut tcell := tcell
  if rtnlevel < Int.ofNat level then
    return (rtnlevel, st)
  if st.needshortprune then
    st := { st with needshortprune := false }
    tcell := shortprune tcell st
  if ¬ cheapautom st.ptn level n then
    st := { st with noncheaplevel := level + 1 }
  let tv1 := (tcell.nextElem none).getD 0
  let (r, out) := otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells
    tc.toNat tv1 (tcell.nextElem none) tcell st
  match r with
  | some rtn => return (rtn, out)
  | none => return (Int.ofNat level - 1, out)

private theorem finish_control {ctx : Ctx n} {inf tcLevel fuel : Nat}
    (hnode : ∀ level numcells (st : SearchSt n), st.needshortprune = false →
      NodeControl st.gcaFirst (otherNode ctx inf tcLevel fuel level numcells st))
    (level numcells : Nat) (tc : Int) (tcell : VSet n) (st : SearchSt n)
    (hclear : st.needshortprune = false) :
    NodeControl st.gcaFirst (finish ctx inf tcLevel fuel level numcells tc tcell st) := by
  have hp : NodeControl st.gcaFirst (processnode ctx level numcells st) :=
    ⟨processnode_gcaFirst ctx level numcells st, process_short hclear⟩
  unfold finish
  generalize he : processnode ctx level numcells st = res at hp ⊢
  obtain ⟨r, out⟩ := res
  dsimp only
  by_cases hearly : r < Int.ofNat level
  · rw [ite_eq_left hearly]
    exact hp
  · rw [ite_eq_right hearly]
    have htail : ∀ (cell : VSet n) (pre : SearchSt n),
        pre.gcaFirst = st.gcaFirst → pre.needshortprune = false →
        NodeControl st.gcaFirst
          (match (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
              ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).1 with
          | some r => (r, (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells
              tc.toNat ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).2)
          | none => (Int.ofNat level - 1,
              (otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
                ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre).2)) := by
      intro cell pre hg hc
      have hl := loop_control hnode (n + 1) level numcells tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre hc
      rw [hg] at hl
      generalize hr : otherChildLoop ctx inf tcLevel fuel (n + 1) level numcells tc.toNat
        ((cell.nextElem none).getD 0) (cell.nextElem none) cell pre = result at hl ⊢
      obtain ⟨r, out⟩ := result
      cases r with
      | none =>
        exact ⟨hl.1, fun hs => by obtain ⟨_, h, _⟩ := hl.2 hs; cases h⟩
      | some r =>
        exact ⟨hl.1, fun hs => by
          obtain ⟨r', heq, hne⟩ := hl.2 hs
          cases Option.some.inj heq
          exact hne⟩
    cases hs : out.needshortprune <;>
      simp only [Bool.false_eq_true, ↓reduceIte]
    all_goals split <;> apply htail
    all_goals first
      | exact hp.1
      | exact hs
      | rfl

private theorem prep_short (level code : Nat) (st : SearchSt n) :
    (otherNodePrep level code st).needshortprune = st.needshortprune := by
  rw [otherNodePrep]
  simp only [Id.run_pure, apply_ite Id.run,
    apply_ite SearchSt.needshortprune, ite_self]

/-- Throughout off-path recursion the first guide is unchanged, and an
outstanding short-prune request returns to a different guide. -/
theorem node_control (ctx : Ctx n) (inf tcLevel : Nat) :
    ∀ fuel level numcells (st : SearchSt n), st.needshortprune = false →
      NodeControl st.gcaFirst (otherNode ctx inf tcLevel fuel level numcells st) := by
  intro fuel
  induction fuel with
  | zero =>
    intro level numcells st hc
    simp [otherNode, NodeControl, hc]
  | succ fuel ih =>
    intro level numcells st hc
    rw [otherNode]
    dsimp only
    generalize hprep : otherNodePrep level
      (refine ctx level st.lab st.ptn st.active numcells).longcode
      { st with
        numnodes := st.numnodes + 1,
        lab := (refine ctx level st.lab st.ptn st.active numcells).lab,
        ptn := (refine ctx level st.lab st.ptn st.active numcells).ptn,
        active := (refine ctx level st.lab st.ptn st.active numcells).active } = pre
    have hg : pre.gcaFirst = st.gcaFirst := by
      rw [← hprep, prepF_gcaFirst]
    have hclear : pre.needshortprune = false := by
      rw [← hprep, prep_short]
      exact hc
    have htail : ∀ tc cell (p : SearchSt n), p.gcaFirst = st.gcaFirst →
        p.needshortprune = false → NodeControl st.gcaFirst
          (finish ctx inf tcLevel fuel level
            (refine ctx level st.lab st.ptn st.active numcells).numcells tc cell p) := by
      intro tc cell p hpg hpc
      rw [← hpg]
      exact finish_control ih _ _ _ _ _ hpc
    by_cases ht : (refine ctx level st.lab st.ptn st.active numcells).numcells < n ∧
        ((pre.eqlevFirst == level) = true ∨ pre.compCanon ≥ (0 : Int))
    · rw [ite_eq_left ht]
      by_cases hcomp : pre.compCanon < (0 : Int)
      · rw [ite_eq_left hcomp]
        by_cases hh : Int.ofNat
            (maketargetcell ctx pre.lab pre.ptn level tcLevel pre.firsttc[level]!).1 ≠
              pre.firsttc[level]!
        · rw [ite_eq_left hh]
          apply htail <;> assumption
        · rw [ite_eq_right hh]
          apply htail <;> assumption
      · rw [ite_eq_right hcomp]
        apply htail <;> assumption
    · rw [ite_eq_right ht]
      apply htail <;> assumption

/-- A sibling subtree entered with a clear request flag returns to its
first-path guide with the flag still clear. -/
theorem clear_at_guide {ctx : Ctx n} {inf tcLevel fuel level numcells : Nat}
    {st : SearchSt n} (hc : st.needshortprune = false)
    (hr : (otherNode ctx inf tcLevel fuel level numcells st).1 = Int.ofNat st.gcaFirst) :
    (otherNode ctx inf tcLevel fuel level numcells st).2.needshortprune = false := by
  have h := (node_control ctx inf tcLevel fuel level numcells st hc).2
  cases hs : (otherNode ctx inf tcLevel fuel level numcells st).2.needshortprune
  · rfl
  · exact (h hs hr).elim

end Generation

end Hex.GraphIso.Nauty
