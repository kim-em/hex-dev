/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.PathFrame
import all HexGraphIso.Nauty.Policy.Guided
import all HexGraphIso.Nauty.Policy.Descent
import all HexGraphIso.Nauty.Policy.History

public section

namespace Hex.GraphIso.Nauty.Engine

variable {n : Nat}

/-- Appending a canonical or saved target extends a guided descent. -/
theorem Guided.append {ctx : Ctx n} {store : Array Int} {tcLevel base level tc o : Nat}
    {root leaf : RefineSt n} {path : List (Nat × Nat)}
    (h : DescPath ctx base root path level leaf)
    (hg : Guided ctx tcLevel store base root path)
    (htc : specTargetcell ctx leaf.lab leaf.ptn level tcLevel = tc ∨ store[level]! = Int.ofNat tc) :
    Guided ctx tcLevel store base root (path ++ [(tc, o)]) := by
  induction h with
  | refl => exact ⟨htc, trivial⟩
  | step _ _ _ _ _ _ _ _ ih => exact ⟨hg.1, ih hg.2 htc⟩

/-- A guided descent whose endpoint agrees with the current partition
up to label order within cells. -/
def GuidedPerm (ctx : Ctx n) (tcLevel : Nat) (store : Array Int) (base : Nat)
    (root : RefineSt n) (level : Nat) (current : RefineSt n) : Prop :=
  ∃ leaf path, DescPath ctx base root path level leaf ∧
    Guided ctx tcLevel store base root path ∧ StPerm level current leaf

/-- A frozen frame starts its own guided history. -/
theorem GuidedPerm.refl (ctx : Ctx n) (tcLevel : Nat) (store : Array Int)
    (level : Nat) (st : RefineSt n) : GuidedPerm ctx tcLevel store level st level st :=
  ⟨st, [], .refl _ _, trivial, .refl _ _⟩

/-- A guided descent retains the mathematical node invariant. -/
theorem GuidedPerm.iter {ctx : Ctx n} {store : Array Int} {tcLevel base level : Nat}
    {root current : RefineSt n} (h : GuidedPerm ctx tcLevel store base root level current)
    (hroot : IterOk ctx base root) : IterOk ctx level current := by
  obtain ⟨leaf, path, hd, _, hp⟩ := h
  apply iterOk_of_stPerm (σ := idRenaming) (descends_iterOk hd.descends hroot)
  rw [mapSt_id]
  exact hp

/-- Sibling recovery may reorder labels within cells while retaining the
same guided history. -/
theorem GuidedPerm.setLab {ctx : Ctx n} {store : Array Int} {tcLevel base level : Nat}
    {root current : RefineSt n} {lab : Array Nat}
    (h : GuidedPerm ctx tcLevel store base root level current)
    (hsize : lab.size = current.lab.size) (hcells : cellsPerm current.ptn level current.lab lab) :
    GuidedPerm ctx tcLevel store base root level { current with lab := lab } := by
  obtain ⟨leaf, path, hd, hg, hp⟩ := h
  have hnew : StPerm level current { current with lab := lab } :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, hsize, hcells⟩
  exact ⟨leaf, path, hd, hg, hnew.symm.trans hp⟩

/-- A guided discrete endpoint has the actual current labelling. -/
theorem GuidedPerm.leaf {ctx : Ctx n} {store : Array Int} {tcLevel base level : Nat}
    {root current : RefineSt n} (h : GuidedPerm ctx tcLevel store base root level current)
    (hroot : IterOk ctx base root) (hdisc : ∀ i, i < n → current.ptn[i]! ≤ level) :
    ∃ leaf path, DescPath ctx base root path level leaf ∧ Guided ctx tcLevel store base root path ∧
      leaf.lab = current.lab ∧ leaf.ptn = current.ptn := by
  have hcurrent := h.iter hroot
  obtain ⟨leaf, path, hd, hg, hp⟩ := h
  exact ⟨leaf, path, hd, hg,
    stPerm_lab_eq hp (by simpa only [hcurrent.ok.ptnSize] using hdisc)
      (hcurrent.ok.labSize.trans hcurrent.ok.ptnSize.symm), hp.ptn⟩

/-- A canonical or saved target extends the guided history through
individualization and refinement, including after sibling reordering. -/
theorem GuidedPerm.child {ctx : Ctx n} {store : Array Int} {tcLevel base level tc e o : Nat}
    {root current : RefineSt n} (hsize : ctx.g.size = n) (hroot : IterOk ctx base root)
    (h : GuidedPerm ctx tcLevel store base root level current)
    (hlevel : level < n) (hcell : (tc, e) ∈ cells current.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc)
    (htc : specTargetcell ctx current.lab current.ptn level tcLevel = tc ∨
      store[level]! = Int.ofNat tc) :
    GuidedPerm ctx tcLevel store base root (level + 1)
      (childSt ctx level current tc current.lab[tc + o]!) := by
  have hcurrent := h.iter hroot
  obtain ⟨leaf, path, hd, hg, hp⟩ := h
  have hleaf := descends_iterOk hd.descends hroot
  have hchoice : specTargetcell ctx leaf.lab leaf.ptn level tcLevel = tc ∨
      store[level]! = Int.ofNat tc := by
    rcases htc with hs | hs
    · left
      have hm := stPerm_target (tcLevel := tcLevel) (rowsMap_id hsize) hleaf
        (show StPerm level current (mapSt idRenaming leaf) by rw [mapSt_id]; exact hp)
      exact hm.symm.trans hs
    · exact Or.inr hs
  have hstep : DescPath ctx level current [(tc, o)] (level + 1)
      (childSt ctx level current tc current.lab[tc + o]!) :=
    .step tc e o hlevel hcell hne ho (.refl _ _)
  obtain ⟨leaf', q, hq, ht, hp'⟩ := descPath_transport (rowsMap_id hsize) hstep hcurrent
    (show StPerm level leaf (mapSt idRenaming current) by rw [mapSt_id]; exact hp.symm)
  obtain ⟨o', rfl⟩ : ∃ o', q = [(tc, o')] := by
    cases q with
    | nil => simp at ht
    | cons pick tail =>
      obtain ⟨pos, off⟩ := pick
      simp only [List.map_cons, List.map_nil, List.cons.injEq] at ht
      have hp : pos = tc := ht.1
      have htail : tail = [] := List.map_eq_nil_iff.mp ht.2
      subst pos
      subst tail
      exact ⟨off, rfl⟩
  rw [mapSt_id] at hp'
  exact ⟨leaf', path ++ [(tc, o')], hd.append hq, hg.append hd hchoice, hp'.symm⟩

end Hex.GraphIso.Nauty.Engine
