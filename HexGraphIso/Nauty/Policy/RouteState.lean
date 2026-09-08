/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Equitable
public import HexGraphIso.Nauty.Policy.Alignment
import all HexGraphIso.Nauty.Policy.Equitable
import all HexGraphIso.Nauty.Policy.Route
import all HexGraphIso.Nauty.Policy.Recovery
import all HexGraphIso.Nauty.Policy.FirstHistory
import all HexGraphIso.Nauty.Policy.State
import all HexGraphIso.Nauty.Search.Search

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n k : Nat}

/-- A guided history ending at the executable partition and cell count. -/
def GuidedAt (ctx : Ctx n) (tcLevel : Nat) (store : Array Int) (base : Nat)
    (root : RefineSt n) (level numcells : Nat) (st : Search n) : Prop :=
  ∃ current, GuidedPerm ctx tcLevel store base root level current ∧
    current.lab = st.lab ∧ current.ptn = st.ptn ∧ current.numcells = numcells

/-- Changes to other fields leave the guided endpoint unchanged. -/
theorem GuidedAt.congr {ctx : Ctx n} {store : Array Int} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st out : Search n}
    (h : GuidedAt ctx tcLevel store base root level numcells st)
    (hl : out.lab = st.lab) (hp : out.ptn = st.ptn) :
    GuidedAt ctx tcLevel store base root level numcells out := by
  obtain ⟨current, hg, hcl, hcp, hc⟩ := h
  exact ⟨current, hg, hcl.trans hl.symm, hcp.trans hp.symm, hc⟩

/-- Restoring a parent after a child preserves the parent's guided history. -/
theorem GuidedAt.recover {G : Colored n k} {ctx : Ctx n} {store : Array Int}
    {tcLevel base level numcells : Nat} {root : RefineSt n} {st out : Search n}
    (h : GuidedAt ctx tcLevel store base root level numcells st)
    (hok : SearchOk G level numcells st.view)
    (hout : SearchOut G level level st.view out.view) :
    GuidedAt ctx tcLevel store base root level numcells
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

/-- A canonical or saved target extends the executable guided descent. -/
theorem GuidedAt.child {ctx : Ctx n} {store : Array Int}
    {tcLevel base level numcells tc e o : Nat} {root : RefineSt n} {st : Search n}
    (h : GuidedAt ctx tcLevel store base root level numcells st)
    (hsize : ctx.g.size = n) (hroot : IterOk ctx base root)
    (hlevel : level < n) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc)
    (htc : specTargetcell ctx st.lab st.ptn level tcLevel = tc ∨ store[level]! = Int.ofNat tc) :
    GuidedPerm ctx tcLevel store base root (level + 1)
      ((child false level tc st.lab[tc + o]! st).refined ctx (level + 1) (numcells + 1)) := by
  obtain ⟨current, hh, hl, hp, hc⟩ := h
  have hcell' : (tc, e) ∈ cells current.ptn level n := by rwa [hp]
  have hnext := hh.child hsize hroot hlevel hcell' hne ho (by simpa only [hl, hp] using htc)
  change GuidedPerm ctx tcLevel store base root (level + 1)
    (refine ctx (level + 1) (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
      (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc) (numcells + 1))
  simpa only [childSt, hl, hp, hc] using hnext

/-- Equitability of the guided history gives equitability of the current partition. -/
theorem GuidedAt.equitable {ctx : Ctx n} {store : Array Int} {tcLevel base level numcells : Nat}
    {root : RefineSt n} {st : Search n}
    (h : GuidedAt ctx tcLevel store base root level numcells st)
    (hok : IterOk ctx base root) (heq : Equitable ctx base root.lab root.ptn)
    (hacc : bcount root.ptn base n = root.numcells)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    Equitable ctx level st.lab st.ptn := by
  obtain ⟨current, hg, hl, hp, _⟩ := h
  simpa only [hl, hp] using hg.equitable hok heq hacc hsymm

end Hex.GraphIso.Nauty.Engine
