/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Route
import all HexGraphIso.Nauty.Policy.Route
import all HexGraphIso.Nauty.SmallCell.Descent

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat} {ctx : Ctx n}

/-- Individualization followed by refinement preserves an accurate cell count. -/
theorem childSt_count {st : RefineSt n} {level tc e o : Nat}
    (h : IterOk ctx level st) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (hacc : bcount st.ptn level n = st.numcells) :
    bcount (childSt ctx level st tc st.lab[tc + o]!).ptn (level + 1) n =
      (childSt ctx level st tc st.lab[tc + o]!).numcells := by
  have he := target_end_lt h.ok.ptnSize h.ok.ptnEnd hcell
  have hopen := target_open h.ok.ptnSize h.ok.ptnEnd hcell tc (Nat.le_refl _) hne
  have hsplit := bcount_breakout_eq (ptn := st.ptn) (level := level) (tc := tc)
    h.valsWeak hopen (by rw [h.ok.ptnSize]; omega) n (Nat.le_refl _)
  rw [ite_eq_left (by omega : tc < n)] at hsplit
  have hpsz : n = (st.ptn.set! tc (level + 1)).size := by rw [Array.size_set!, h.ok.ptnSize]
  have hbsz : (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1.size =
      (st.ptn.set! tc (level + 1)).size := by
    rw [breakout_lab_size, Array.size_set!, h.ok.labSize, h.ok.ptnSize]
  have hend := setTc_end (tc := tc) h.ok.ptnEnd (by rw [h.ok.ptnSize]; omega)
  have hr := refine_bcount (ctx := ctx) (level := level + 1)
    (lab := (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1)
    (ptn := st.ptn.set! tc (level + 1)) (active := VSet.empty.insert tc)
    (numcells := st.numcells + 1) hpsz hbsz hend
  change bcount (refine ctx (level + 1) _ _ _ _).ptn (level + 1) n =
    (refine ctx (level + 1) _ _ _ _).numcells
  omega

/-- An equitable ancestor with an accurate cell count has equitable
descendants with accurate counts, without any small-cell hypothesis. -/
theorem DescPath.equitable {base last : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} (h : DescPath ctx base root path last leaf)
    (hok : IterOk ctx base root) (heq : Equitable ctx base root.lab root.ptn)
    (hacc : bcount root.ptn base n = root.numcells)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    Equitable ctx last leaf.lab leaf.ptn ∧ bcount leaf.ptn last n = leaf.numcells := by
  induction h with
  | refl => exact ⟨heq, hacc⟩
  | step tc e o hlvl hcell hne ho htail ih =>
    exact ih (iterOk_child hok hlvl hcell hne ho)
      (equitable_breakout hok.ok.labSize hok.ok.ptnSize hok.ok.ptnEnd hok.valsWeak
        hok.ok.labOk hok.inj hsymm heq hcell hne ho hacc)
      (childSt_count hok hcell hne hacc)

namespace Engine

/-- Reordering within cells preserves the equitability of a guided endpoint. -/
theorem GuidedPerm.equitable {store : Array Int} {tcLevel base level : Nat}
    {root current : RefineSt n} (h : GuidedPerm ctx tcLevel store base root level current)
    (hok : IterOk ctx base root) (heq : Equitable ctx base root.lab root.ptn)
    (hacc : bcount root.ptn base n = root.numcells)
    (hsymm : ∀ u v, u < n → v < n → (ctx.g[u]!).mem v = (ctx.g[v]!).mem u) :
    Equitable ctx level current.lab current.ptn := by
  obtain ⟨leaf, path, hd, _, hp⟩ := h
  have hleaf := descends_iterOk hd.descends hok
  exact hp.equitable (hd.equitable hok heq hacc hsymm).1 hleaf.ok.ptnSize hleaf.ok.ptnEnd

end Engine

end Hex.GraphIso.Nauty
