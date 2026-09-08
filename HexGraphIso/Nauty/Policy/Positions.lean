/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Policy.Selection
public import HexGraphIso.Nauty.Invariant.Singleton
import all HexGraphIso.Nauty.Spec.Descent

public section

namespace Hex.GraphIso.Nauty

variable {n : Nat} {ctx : Ctx n}

/-- A subtree step retains every existing singleton and its vertex. -/
theorem childSt_singleton {st : RefineSt n} {level tc e o a : Nat}
    (h : IterOk ctx level st) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc) (ha : IsCell st.ptn level a 1) :
    let child := childSt ctx level st tc st.lab[tc + o]!
    IsCell child.ptn (level + 1) a 1 ∧ child.lab[a]! = st.lab[a]! := by
  have he := target_end_lt h.ok.ptnSize h.ok.ptnEnd hcell
  have hc := cells_isCell (Nat.le_of_eq h.ok.ptnSize.symm) h.ok.ptnEnd _ hcell
  have hat : a ≠ tc := by
    intro heq
    subst a
    rcases isCell_disjoint_or_eq ha hc with hleft | hright | hsame <;> omega
  have hs := isCell_set_miss ha hc (by omega)
  have hend := setTc_end (tc := tc) h.ok.ptnEnd (by rw [h.ok.ptnSize]; omega)
  have hbsz : (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1.size =
      (st.ptn.set! tc (level + 1)).size := by
    rw [breakout_lab_size, Array.size_set!, h.ok.labSize, h.ok.ptnSize]
  have hpsz : n = (st.ptn.set! tc (level + 1)).size := by
    rw [Array.size_set!, h.ok.ptnSize]
  refine ⟨isCell_refine_one hpsz hbsz hend hs, ?_⟩
  change (refine ctx (level + 1) _ _ _ _).lab[a]! = _
  rw [refine_fixes_singleton (Nat.le_of_eq hpsz) hbsz hend hs]
  exact breakout_misses_singleton (by rw [h.ok.labSize]; exact h.inj)
    (by rw [h.ok.labSize]; omega) (singleton_outside_cell ha hc hat (by omega))

/-- A subtree step creates a singleton containing its selected vertex. -/
theorem childSt_picked {st : RefineSt n} {level tc e o : Nat}
    (h : IterOk ctx level st) (hcell : (tc, e) ∈ cells st.ptn level n)
    (hne : tc < e) (ho : o ≤ e - tc) :
    let child := childSt ctx level st tc st.lab[tc + o]!
    IsCell child.ptn (level + 1) tc 1 ∧ child.lab[tc]! = st.lab[tc + o]! := by
  have he := target_end_lt h.ok.ptnSize h.ok.ptnEnd hcell
  have hc := cells_isCell (Nat.le_of_eq h.ok.ptnSize.symm) h.ok.ptnEnd _ hcell
  have hs : IsCell (st.ptn.set! tc (level + 1)) (level + 1) tc 1 :=
    isCell_breakout_target (n := n) (lab := st.lab) (tv := st.lab[tc + o]!)
      (by rw [h.ok.ptnSize]; omega) hc.2.1
  have hend := setTc_end (tc := tc) h.ok.ptnEnd (by rw [h.ok.ptnSize]; omega)
  have hbsz : (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1.size =
      (st.ptn.set! tc (level + 1)).size := by
    rw [breakout_lab_size, Array.size_set!, h.ok.labSize, h.ok.ptnSize]
  have hpsz : n = (st.ptn.set! tc (level + 1)).size := by
    rw [Array.size_set!, h.ok.ptnSize]
  refine ⟨isCell_refine_one hpsz hbsz hend hs, ?_⟩
  change (refine ctx (level + 1) _ _ _ _).lab[tc]! = _
  rw [refine_fixes_singleton (Nat.le_of_eq hpsz) hbsz hend hs]
  exact breakout_at_target (by rw [h.ok.labSize]; exact h.inj)
    (by rw [h.ok.labSize]; omega)

/-- Every descent retains its entry singletons and their vertices. -/
theorem DescPath.singleton {level last a : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} (h : DescPath ctx level root path last leaf)
    (hok : IterOk ctx level root) (ha : IsCell root.ptn level a 1) :
    IsCell leaf.ptn last a 1 ∧ leaf.lab[a]! = root.lab[a]! := by
  induction h with
  | refl => exact ⟨ha, rfl⟩
  | step tc e o hlvl hcell hne ho htail ih =>
    obtain ⟨hc, hv⟩ := childSt_singleton hok hcell hne ho ha
    obtain ⟨hc', hv'⟩ := ih (iterOk_child hok hlvl hcell hne ho) hc
    exact ⟨hc', hv'.trans hv⟩

/-- The final labelling records the first individualized vertex at the
first target position. -/
theorem DescPath.picked {level last tc o : Nat} {root leaf : RefineSt n}
    {path : List (Nat × Nat)} (h : DescPath ctx level root ((tc, o) :: path) last leaf)
    (hok : IterOk ctx level root) : leaf.lab[tc]! = root.lab[tc + o]! := by
  cases h with
  | step _ e _ hlvl hcell hne ho htail =>
    obtain ⟨hc, hv⟩ := childSt_picked hok hcell hne ho
    exact (htail.singleton (iterOk_child hok hlvl hcell hne ho) hc).2.trans hv

end Hex.GraphIso.Nauty
