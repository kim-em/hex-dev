/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Transport
public import HexGraphIso.Nauty.Invariant.Stabilize
import all HexGraphIso.Nauty.Spec.Descent
import all HexGraphIso.Nauty.Invariant.Stabilize
import all HexGraphIso.Nauty.Equitable.Basic

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat} {ctx : Ctx n}

/-- A subtree step preserves its parent's cell contents and every
boundary already closed at the parent. -/
theorem childSt_frame {st : RefineSt n} {level tc e o : Nat}
    (h : IterOk ctx level st) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc) :
    let child := childSt ctx level st tc st.lab[tc + o]!
    cellsPerm st.ptn level st.lab child.lab ∧
      ∀ q : Nat, st.ptn[q]! ≤ level → child.ptn[q]! = st.ptn[q]! := by
  have he := target_end_lt h.ok.ptnSize h.ok.ptnEnd hcell
  have hc := cells_isCell (Nat.le_of_eq h.ok.ptnSize.symm) h.ok.ptnEnd _ hcell
  have hopen := target_open h.ok.ptnSize h.ok.ptnEnd hcell tc (Nat.le_refl _) hne
  have hend := setTc_end (tc := tc) h.ok.ptnEnd (by rw [h.ok.ptnSize]; omega)
  have hbsz : (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1.size =
      (st.ptn.set! tc (level + 1)).size := by
    rw [breakout_lab_size, Array.size_set!, h.ok.labSize, h.ok.ptnSize]
  have hpsz : n = (st.ptn.set! tc (level + 1)).size := by
    rw [Array.size_set!, h.ok.ptnSize]
  have hraw : ∀ q : Nat, st.ptn[q]! ≤ level →
      (st.ptn.set! tc (level + 1))[q]! = st.ptn[q]! := by
    intro q hq
    exact Array.getElem!_set!_ne _ _ _ _ (by intro heq; subst q; omega)
  have hbreak := breakout_cellsPerm (n := n) hc (by rw [h.ok.ptnSize]; omega)
    (by rw [h.ok.labSize, h.ok.ptnSize]) (by omega : o < e + 1 - tc)
  refine ⟨?_, ?_⟩
  · exact refine_reachAt hbreak (Nat.le_of_eq hpsz)
      (Array.size_set! _ _ _).symm hbsz hend h.ok.ptnEnd
      (fun q hq => by rw [hraw q hq]; omega)
  · intro q hq
    change (refine ctx (level + 1) _ _ _ _).ptn[q]! = _
    rw [refine_frozen hpsz hbsz hend (by rw [hraw q hq]; omega), hraw q hq]

/-- Every descent preserves the ordered cell contents of its frozen
entry partition and its already closed boundaries. -/
theorem DescPath.frame {base last : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} (h : DescPath ctx base root path last leaf)
    (hok : IterOk ctx base root) :
    cellsPerm root.ptn base root.lab leaf.lab ∧
      ∀ q : Nat, root.ptn[q]! ≤ base → leaf.ptn[q]! = root.ptn[q]! := by
  induction h with
  | refl => exact ⟨fun _ _ _ => .refl _, fun _ _ => rfl⟩
  | @step base last root leaf path tc e o hlvl hcell hne ho htail ih =>
    have hchild := iterOk_child hok hlvl hcell hne ho
    have hleaf := descends_iterOk htail.descends hchild
    obtain ⟨hstep, hclosed⟩ := childSt_frame hok hcell hne ho
    obtain ⟨htailPerm, htailClosed⟩ := ih hchild
    refine ⟨?_, ?_⟩
    · exact cellsPerm_trans hstep (cellsPerm_coarsen
        (hok.ok.ptnSize.trans hchild.ok.ptnSize.symm)
        (hchild.ok.labSize.trans hchild.ok.ptnSize.symm)
        (hleaf.ok.labSize.trans hchild.ok.ptnSize.symm) htailPerm hchild.ok.ptnEnd hok.ok.ptnEnd
        (fun q hq => by rw [hclosed q hq]; omega))
    · intro q hq
      rw [htailClosed q (by rw [hclosed q hq]; omega), hclosed q hq]

/-- A checked scatter between the leaves stabilizes their common
ancestor, and hence forces equal depth for guided descents. -/
theorem Guided.leaf_checked {tcLevel base last₁ last₂ : Nat}
    {store : Array Int} {perm : Array Nat} {root first current : RefineSt n}
    {p₁ p₂ : List (Nat × Nat)}
    (hfirst : DescPath ctx base root p₁ last₁ first)
    (hok : IterOk ctx base root) (hselect : Selects ctx tcLevel base root p₁)
    (htarget : Targets store base (p₁.map Prod.fst))
    (hcurrent : DescPath ctx base root p₂ last₂ current)
    (hguided : Guided ctx tcLevel store base root p₂)
    (hdisc₁ : ∀ q, q < n → first.ptn[q]! ≤ last₁)
    (hdisc₂ : ∀ q, q < n → current.ptn[q]! ≤ last₂)
    (hgsz : ctx.g.size = n) (hcheck : checkAutom ctx.g perm = true)
    (hmap : ∀ i, i < n → perm[first.lab[i]!]! = current.lab[i]!) : last₂ = last₁ ∧ leafRows ctx current.lab = leafRows ctx first.lab := by
  have hfirstOk := descends_iterOk hfirst.descends hok
  have hcurrentOk := descends_iterOk hcurrent.descends hok
  obtain ⟨σ, hσ, hg⟩ := checkAutom_sound hgsz hcheck
  have hlabels : first.lab.map σ.toFun = current.lab := by
    apply Array.ext (by rw [Array.size_map, hfirstOk.ok.labSize, hcurrentOk.ok.labSize])
    intro i hi hj
    have hiN : i < n := by rwa [hcurrentOk.ok.labSize] at hj
    have hs := hσ first.lab[i]! (hfirstOk.ok.labOk i (by rw [hfirstOk.ok.labSize]; exact hiN))
    have hm := hmap i hiN
    simpa only [Array.getElem_map, getElem!_pos first.lab i (by rw [hfirstOk.ok.labSize]; exact hiN),
      getElem!_pos current.lab i hj] using hs.trans hm
  have hstab := cellStab_of_scatter hok.ok.ptnSize hok.ok.labSize hfirstOk.ok.labSize
    hok.ok.ptnEnd (hfirst.frame hok).1 (hcurrent.frame hok).1 hmap
  have hrootMap : root.lab.map σ.toFun = root.lab.map (fun w => perm[w]!) :=
    map_congr_of_labOk hok.ok.labOk (fun w hw => hσ w hw)
  have hsp : StPerm base root (mapSt σ root) := by
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · simp only [Array.size_map]
    · change cellsPerm root.ptn base root.lab (root.lab.map σ.toFun)
      rw [hrootMap]
      exact hstab
  refine ⟨Guided.depth_map hg hfirst hok hselect htarget hcurrent hguided hsp hdisc₁ hdisc₂ hlabels, ?_⟩
  rw [← hlabels]
  exact leafRows_map σ hg hfirstOk.ok.labOk hfirstOk.ok.labSize

/-- Checked guided leaves have equal descent depth. -/
theorem Guided.depth_checked {tcLevel base last₁ last₂ : Nat}
    {store : Array Int} {perm : Array Nat} {root first current : RefineSt n}
    {p₁ p₂ : List (Nat × Nat)}
    (hfirst : DescPath ctx base root p₁ last₁ first)
    (hok : IterOk ctx base root) (hselect : Selects ctx tcLevel base root p₁)
    (htarget : Targets store base (p₁.map Prod.fst))
    (hcurrent : DescPath ctx base root p₂ last₂ current)
    (hguided : Guided ctx tcLevel store base root p₂)
    (hdisc₁ : ∀ q, q < n → first.ptn[q]! ≤ last₁)
    (hdisc₂ : ∀ q, q < n → current.ptn[q]! ≤ last₂)
    (hgsz : ctx.g.size = n) (hcheck : checkAutom ctx.g perm = true)
    (hmap : ∀ i, i < n → perm[first.lab[i]!]! = current.lab[i]!) : last₂ = last₁ := by
  exact (Guided.leaf_checked hfirst hok hselect htarget hcurrent hguided hdisc₁ hdisc₂
    hgsz hcheck hmap).1

end Hex.GraphIso.Nauty
