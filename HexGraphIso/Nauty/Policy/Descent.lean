/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.History
import all HexGraphIso.Nauty.Policy.History

public section

/-!
Descent histories modulo reordering labels within cells. A recovered
parent keeps the descendant's labelling, so its exact refinement state
need not occur on a path from the frozen ancestor. Cell equivalence
relates it to a state that does, and is preserved by individualizing
the same vertex on both sides.
-/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

theorem StPerm.symm {level : Nat} {U V : RefineSt n}
    (h : StPerm level U V) : StPerm level V U := by
  refine ⟨h.ptn.symm, h.active.symm, h.numcells.symm, h.hint.symm,
    h.maxpos.symm, h.longcode.symm, h.labSize.symm, ?_⟩
  intro tc len hc
  rw [h.ptn] at hc
  exact (h.cells tc len hc).symm

theorem StPerm.trans {level : Nat} {U V W : RefineSt n}
    (hUV : StPerm level U V) (hVW : StPerm level V W) :
    StPerm level U W := by
  refine ⟨hVW.ptn.trans hUV.ptn, hVW.active.trans hUV.active,
    hVW.numcells.trans hUV.numcells, hVW.hint.trans hUV.hint,
    hVW.maxpos.trans hUV.maxpos, hVW.longcode.trans hUV.longcode,
    hVW.labSize.trans hUV.labSize, ?_⟩
  intro tc len hc
  exact (hUV.cells tc len hc).trans (hVW.cells tc len (by rwa [hUV.ptn]))

/-- Cell-equivalent states have the same equitability property. -/
theorem StPerm.equitable {ctx : Ctx n} {level : Nat} {current leaf : RefineSt n}
    (h : StPerm level current leaf) (heq : Equitable ctx level leaf.lab leaf.ptn)
    (hsize : leaf.ptn.size = n) (hend : leaf.ptn[leaf.ptn.size - 1]! ≤ level) :
    Equitable ctx level current.lab current.ptn := by
  rw [← h.ptn]
  have hp := h.symm.cells
  intro cd hcd de hde
  have hcdCell := cells_isCell (Nat.le_of_eq hsize.symm) hend cd hcd
  have hdeCell := cells_isCell (Nat.le_of_eq hsize.symm) hend de hde
  have hcdPerm := hp cd.1 (cd.2 + 1 - cd.1) hcdCell
  have hdePerm := hp de.1 (de.2 + 1 - de.1) hdeCell
  have hwork : worksetOf n leaf.lab de.1 de.2 = worksetOf n current.lab de.1 de.2 :=
    worksetOf_perm hdePerm
  rw [splitDone_iff_constOn, ← hwork]
  exact (splitDone_iff_constOn.mp (heq cd hcd de hde)).perm hcdPerm.symm

/-- The small-cell invariant holds along any mathematical descent. -/
theorem Descends.subtree {ctx : Ctx n} {base level : Nat} {root leaf : RefineSt n}
    (h : Descends ctx base root level leaf) (hroot : SubtreeOk ctx base root)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    SubtreeOk ctx level leaf := by
  induction h with
  | refl => exact hroot
  | step tc e o hlvl hcell hne ho htail ih =>
    exact ih (subtreeOk_child hroot hlvl hsymm hcell hne ho)

/-- The identity vertex renaming. -/
def idRenaming : Renaming n :=
  ⟨id, fun _ _ h => h, fun _ => Iff.rfl⟩

/-- Mapping by the identity leaves a refinement state unchanged. -/
theorem mapSt_id (st : RefineSt n) : mapSt idRenaming st = st := by
  simp only [mapSt, idRenaming, Array.map_id]

/-- The identity renaming preserves a correctly sized row array. -/
theorem rowsMap_id {ctx : Ctx n} (hsize : ctx.g.size = n) :
    RowsMap idRenaming ctx.g ctx.g := by
  refine ⟨hsize, hsize, ?_⟩
  intro v _
  exact (image_id _).symm

namespace Engine

/-- A stored-target descent whose endpoint agrees with the current
state up to label order inside cells. -/
def FollowsPerm (ctx : Ctx n) (store : Array Int) (base : Nat)
    (root : RefineSt n) (level : Nat) (current : RefineSt n) : Prop :=
  ∃ leaf, Follows ctx store base root level leaf ∧ StPerm level current leaf

theorem Follows.perm {ctx : Ctx n} {store : Array Int} {base level : Nat}
    {root leaf : RefineSt n} (h : Follows ctx store base root level leaf) :
    FollowsPerm ctx store base root level leaf :=
  ⟨leaf, h, .refl _ _⟩

/-- A descent modulo cell order retains the mathematical node invariant. -/
theorem FollowsPerm.iter {ctx : Ctx n} {store : Array Int} {base level : Nat}
    {root current : RefineSt n} (h : FollowsPerm ctx store base root level current)
    (hroot : IterOk ctx base root) : IterOk ctx level current := by
  obtain ⟨leaf, ⟨path, hd, _⟩, hp⟩ := h
  apply iterOk_of_stPerm (σ := idRenaming) (descends_iterOk hd.descends hroot)
  rw [mapSt_id]
  exact hp

/-- A descent modulo cell order retains the entire small-cell invariant. -/
theorem FollowsPerm.subtree {ctx : Ctx n} {store : Array Int} {base level : Nat}
    {root current : RefineSt n} (h : FollowsPerm ctx store base root level current)
    (hroot : SubtreeOk ctx base root)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    SubtreeOk ctx level current := by
  have hit := h.iter hroot.it
  obtain ⟨leaf, ⟨path, hd, _⟩, hp⟩ := h
  have hs := hd.descends.subtree hroot hsymm
  exact ⟨hit, hp.equitable hs.eqt hs.it.ok.ptnSize hs.it.ok.ptnEnd,
    by rw [← hp.ptn, ← hp.numcells]; exact hs.acc,
    by rw [← hp.ptn]; exact hs.shape⟩

/-- A cell-preserving relabelling of a recovered parent keeps its history. -/
theorem FollowsPerm.setLab {ctx : Ctx n} {store : Array Int} {base level : Nat}
    {root current : RefineSt n} {lab : Array Nat}
    (h : FollowsPerm ctx store base root level current)
    (hsize : lab.size = current.lab.size)
    (hcells : cellsPerm current.ptn level current.lab lab) :
    FollowsPerm ctx store base root level { current with lab := lab } := by
  obtain ⟨leaf, hpath, hperm⟩ := h
  refine ⟨leaf, hpath, ?_⟩
  have hnew : StPerm level current { current with lab := lab } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsize, hcells⟩
  exact hnew.symm.trans hperm

theorem FollowsPerm.set_after {ctx : Ctx n} {store : Array Int}
    {base level slot : Nat} {root current : RefineSt n}
    (h : FollowsPerm ctx store base root level current)
    (hafter : level ≤ slot) (value : Int) :
    FollowsPerm ctx (store.set! slot value) base root level current := by
  obtain ⟨leaf, hpath, hperm⟩ := h
  exact ⟨leaf, hpath.set_after hafter value, hperm⟩

/-- Individualizing a vertex in the stored target extends the history
even when earlier sibling searches reordered the parent's labels. -/
theorem FollowsPerm.child {ctx : Ctx n} {store : Array Int}
    {base level tc e o : Nat} {root current : RefineSt n}
    (hsize : ctx.g.size = n) (hroot : IterOk ctx base root)
    (h : FollowsPerm ctx store base root level current)
    (hlevel : level < n) (hcell : (tc, e) ∈ cells current.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc)
    (htc : store[level]! = Int.ofNat tc) :
    FollowsPerm ctx store base root (level + 1)
      (childSt ctx level current tc current.lab[tc + o]!) := by
  obtain ⟨leaf, hpath, hperm⟩ := h
  obtain ⟨path, hdesc, htargets⟩ := hpath
  have hleaf := descends_iterOk hdesc.descends hroot
  have hcurrent : IterOk ctx level current :=
    iterOk_of_stPerm (σ := idRenaming) hleaf (by rwa [mapSt_id])
  have hstep : DescPath ctx level current [(tc, o)] (level + 1)
      (childSt ctx level current tc current.lab[tc + o]!) :=
    .step tc e o hlevel hcell hne ho (.refl _ _)
  obtain ⟨leaf', q, hq, htargets', hperm'⟩ :=
    descPath_transport (rowsMap_id hsize) hstep hcurrent
      (show StPerm level leaf (mapSt idRenaming current) by
        rw [mapSt_id]; exact hperm.symm)
  refine ⟨leaf', ⟨path ++ q, hdesc.append hq, ?_⟩, ?_⟩
  · rw [List.map_append, htargets']
    apply htargets.append
    simpa only [List.length_map, ← hdesc.length] using htc
  · rw [mapSt_id] at hperm'
    exact hperm'.symm

/-- At a discrete endpoint the ghost labelling is the actual labelling. -/
theorem FollowsPerm.leaf {ctx : Ctx n} {store : Array Int}
    {base level : Nat} {root current : RefineSt n}
    (hroot : IterOk ctx base root)
    (h : FollowsPerm ctx store base root level current)
    (hdisc : ∀ i, i < n → current.ptn[i]! ≤ level) :
    ∃ leaf, Follows ctx store base root level leaf ∧
      leaf.lab = current.lab ∧ leaf.ptn = current.ptn := by
  obtain ⟨leaf, hpath, hperm⟩ := h
  obtain ⟨path, hdesc, htargets⟩ := hpath
  have hleaf := descends_iterOk hdesc.descends hroot
  have hlsz : current.lab.size = n := hperm.labSize.symm.trans hleaf.ok.labSize
  have hpsz : current.ptn.size = n := by rw [← hperm.ptn, hleaf.ok.ptnSize]
  exact ⟨leaf, ⟨path, hdesc, htargets⟩,
    stPerm_lab_eq hperm (by simpa only [hpsz] using hdisc) (hlsz.trans hpsz.symm),
    hperm.ptn⟩

/-- Cheap admission remains valid when sibling recovery has reordered
labels inside ancestor cells. -/
theorem scatter_of_permHistory {ctx : Ctx n} {st : Search n} {level : Nat}
    {cs fs : List Nat}
    (hcodes : FirstCodeInv n cs fs st.firstcode st.eqlevFirst)
    (heq : st.eqlevFirst = level)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u v, u < n → v < n →
      (ctx.g[u]!).mem v = (ctx.g[v]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {ancestor U V : RefineSt n}
    (hsmall : SubtreeOk ctx st.gcaFirst ancestor)
    (hU : FollowsPerm ctx st.firsttc st.gcaFirst ancestor fs.length U)
    (hV : FollowsPerm ctx st.firsttc st.gcaFirst ancestor level V)
    (hUd : ∀ i, i < n → U.ptn[i]! ≤ fs.length)
    (hVd : ∀ i, i < n → V.ptn[i]! ≤ level)
    (hfirst : st.firstlab = U.lab) (hcurrent : st.lab = V.lab)
    (hwork : st.workperm.size = n) :
    checkAutom ctx.g (scatter st.firstlab st).workperm = true := by
  obtain ⟨U', hU', hUlab, hUptn⟩ := hU.leaf hsmall.it hUd
  obtain ⟨V', hV', hVlab, hVptn⟩ := hV.leaf hsmall.it hVd
  apply scatter_of_history hcodes heq hgsz hsymm hloop hsmall hU' hV'
  · simpa only [hUptn] using hUd
  · simpa only [hVptn] using hVd
  · exact hfirst.trans hUlab.symm
  · exact hcurrent.trans hVlab.symm
  · exact hwork

end Engine

end Hex.GraphIso.Nauty
