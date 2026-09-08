/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.Depth
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Policy.Descent
import all HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- A mathematical descent agrees with the executable partition and cell count. -/
def DescentAt (ctx : Ctx n) (store : Array Int) (base : Nat) (root : RefineSt n)
    (level numcells : Nat) (st : Search n) : Prop :=
  ∃ current, FollowsPerm ctx store base root level current ∧
    current.lab = st.lab ∧ current.ptn = st.ptn ∧ current.numcells = numcells

/-- Bookkeeping that preserves the partition preserves its descent history. -/
theorem DescentAt.congr {ctx : Ctx n} {store : Array Int} {base level numcells : Nat}
    {root : RefineSt n} {st out : Search n}
    (h : DescentAt ctx store base root level numcells st)
    (hlab : out.lab = st.lab) (hptn : out.ptn = st.ptn) :
    DescentAt ctx store base root level numcells out := by
  obtain ⟨current, hh, hl, hp, hc⟩ := h
  exact ⟨current, hh, hl.trans hlab.symm, hp.trans hptn.symm, hc⟩

/-- Reopening after a child restores exactly the parent's partition array. -/
theorem recover_ptn_eq {G : Colored n k} {level numcells : Nat} {st out : Search n}
    (hok : SearchOk G level numcells st.view)
    (hout : SearchOut G level level st.view out.view) :
    (recoverLevels level (recoverPtn (n + 2) level out)).ptn = st.ptn := by
  have hview := view_recover (n + 2) level out
  have hs : (recoverLevels level (recoverPtn (n + 2) level out)).ptn.size = st.ptn.size := by
    change (recoverLevels level (recoverPtn (n + 2) level out)).view.ptn.size = _
    rw [hview, recover_ptn_size]
    exact hout.ptnSize
  apply Array.ext hs
  intro i hi₁ hi₂
  rw [← getElem!_pos (recoverLevels level (recoverPtn (n + 2) level out)).ptn i hi₁,
    ← getElem!_pos st.ptn i hi₂]
  change (recoverLevels level (recoverPtn (n + 2) level out)).view.ptn[i]! = _
  rw [hview, recover_ptn]
  change (if i < n ∧ out.ptn[i]! > level then n + 2 else out.ptn[i]!) = st.ptn[i]!
  have hi : i < n := by rw [← hok.ptnSize]; exact hi₂
  by_cases hclosed : st.ptn[i]! ≤ level
  · have he := hout.low i (Or.inl hclosed)
    change out.ptn[i]! = st.ptn[i]! at he
    simp only [he, show ¬ st.ptn[i]! > level by omega, and_false, ite_false]
  · have hopen : level < out.ptn[i]! := by
      by_cases houtclosed : out.ptn[i]! ≤ level
      · have he := hout.low i (Or.inr houtclosed)
        change out.ptn[i]! = st.ptn[i]! at he
        omega
      · omega
    have hmarker : st.ptn[i]! = n + 2 := (hok.vals i hi).resolve_left hclosed
    simp only [hi, hopen, and_self, ite_true, hmarker]

/-- Recovering a completed child retains the parent's history up to label
order within its cells, even though the child's labelling is kept. -/
theorem DescentAt.recover {G : Colored n k} {ctx : Ctx n} {store : Array Int}
    {base level numcells : Nat} {root : RefineSt n} {st out : Search n}
    (h : DescentAt ctx store base root level numcells st)
    (hok : SearchOk G level numcells st.view)
    (hout : SearchOut G level level st.view out.view) :
    DescentAt ctx store base root level numcells
      (recoverLevels level (recoverPtn (n + 2) level out)) := by
  obtain ⟨current, hh, hl, hp, hc⟩ := h
  have hsize : out.lab.size = current.lab.size := by rw [hl]; exact hout.labSize
  have hperm : cellsPerm current.ptn level current.lab out.lab := by
    rw [hl, hp]
    exact hout.perm
  refine ⟨{ current with lab := out.lab }, hh.setLab hsize hperm, ?_, ?_, hc⟩
  · have he := congrArg SearchSt.lab (view_recover (n + 2) level out)
    change (recoverLevels level (recoverPtn (n + 2) level out)).lab = _ at he
    rw [Nauty.recover_lab] at he
    exact he.symm
  · exact hp.trans (recover_ptn_eq hok hout).symm

/-- Individualizing a vertex in the recorded target and refining it
extends the executable descent history. -/
theorem DescentAt.child {ctx : Ctx n} {store : Array Int}
    {base level numcells tc e o : Nat} {root : RefineSt n} {st : Search n}
    (h : DescentAt ctx store base root level numcells st)
    (hsize : ctx.g.size = n) (hroot : IterOk ctx base root)
    (hlevel : level < n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc) (htc : store[level]! = Int.ofNat tc) :
    FollowsPerm ctx store base root (level + 1)
      ((child false level tc st.lab[tc + o]! st).refined ctx (level + 1) (numcells + 1)) := by
  obtain ⟨current, hh, hl, hp, hc⟩ := h
  have hcell' : (tc, e) ∈ cells current.ptn level n := by rwa [hp]
  have hnext := hh.child hsize hroot hlevel hcell' hne ho htc
  change FollowsPerm ctx store base root (level + 1)
    (refine ctx (level + 1) (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
      (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1))
  simpa only [childSt, hl, hp, hc] using hnext

/-- At a cheap ancestor, retaining code agreement forces the executable
target choice to extend the saved descent history. -/
theorem DescentAt.target {ctx : Ctx n} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : Search n}
    (h : DescentAt ctx st.firsttc base root level numcells st)
    (href : FirstRef ctx tcLevel base root st) (hdepth : Depth href.last st)
    (heq : st.eqlevFirst = level)
    (hkeep : (chooseTarget false ctx tcLevel level numcells st).2.2.2.eqlevFirst = level)
    (hnc : numcells < n) (hlevel : 0 < level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hsmall : SubtreeOk ctx base root) :
    (chooseTarget false ctx tcLevel level numcells st).1 = st.firsttc[level]! := by
  obtain ⟨current, hh, hl, hp, hc⟩ := h
  have hs := hh.subtree hsmall hsymm
  have hopen : ∃ i, i < n ∧ level < current.ptn[i]! := by
    apply exists_open_of_bcount_lt
    rw [hs.acc, hc]
    exact hnc
  have hbound : level ≤ href.last := by rw [← heq]; exact hdepth.1
  have htarget := href.target hbound hgsz hsymm hloop hsmall hh hopen
  rw [hl, hp] at htarget
  apply chooseTarget_match hnc hlevel heq hkeep htarget
  · simpa only [hl, hp] using hs.eqt
  · simpa only [hl] using hs.it.ok.labOk
  · simpa only [hl] using hs.it.ok.labSize
  · simpa only [hp] using hs.it.ok.ptnSize
  · simpa only [hp] using hs.it.ok.ptnEnd

end Hex.GraphIso.Nauty.Engine
