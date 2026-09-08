/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Invariant.Refine
public import HexGraphIso.Nauty.Equitable.Individualize
public import HexGraphIso.Nauty.Equitable.Fix
import all HexGraphIso.Nauty.Search.State

public section

/-! Singleton cells retain their vertices through refinement and
individualization of another cell. -/

namespace Hex.GraphIso.Nauty

variable {n : Nat}

/-- Individualizing offset `o` puts that offset's vertex at the target
position. -/
theorem breakout_at_target {lab ptn : Array Nat} {level tc o : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size) :
    (breakout n lab ptn (level + 1) tc lab[tc + o]!).1[tc]! =
      lab[tc + o]! := by
  rw [breakout_lab_at hinj hto tc, ite_eq_right (Nat.lt_irrefl tc),
    ite_eq_left rfl]

/-- Individualizing closes the target position, so it becomes a
singleton cell one level down. This is what makes the transport below
apply from the child onwards. -/
theorem isCell_breakout_target {lab ptn : Array Nat}
    {level tc tv : Nat} (hlt : tc < ptn.size)
    (hstart : tc = 0 ∨ ptn[tc - 1]! ≤ level) :
    IsCell (breakout n lab ptn (level + 1) tc tv).2.1 (level + 1) tc 1 := by
  refine ⟨Nat.one_pos, ?_, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos tc with rfl | hpos
    · exact Or.inl rfl
    · refine Or.inr ?_
      show (ptn.set! tc (level + 1))[tc - 1]! ≤ level + 1
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      rcases hstart with rfl | hs
      · omega
      · exact Nat.le_succ_of_le hs
  · intro i h1 h2; omega
  · show (ptn.set! tc (level + 1))[tc]! ≤ level + 1
    rw [Array.getElem!_set!_self _ _ _ hlt]
    exact Nat.le_refl _

/-- `refine` leaves a singleton cell's position exactly where it was:
it permutes cell contents, and a singleton cell has only one. -/
theorem refine_fixes_singleton {ctx : Ctx n} {level : Nat}
    {lab ptn : Array Nat} {active : VSet n} {numcells a : Nat}
    (hnn : n ≤ ptn.size) (hs : lab.size = ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) (hc : IsCell ptn level a 1) :
    (refine ctx level lab ptn active numcells).lab[a]! = lab[a]! :=
  (cellsPerm_singleton (refine_refInv hnn hs hend).perm hc).symm

/-- A singleton cell lies outside any other cell, so outside the window
a `breakout` at that other cell rotates. -/
theorem singleton_outside_cell {ptn : Array Nat}
    {level a tc len o : Nat} (hca : IsCell ptn level a 1)
    (hct : IsCell ptn level tc len) (hne : a ≠ tc) (ho : o < len) :
    a < tc ∨ tc + o < a := by
  rcases isCell_disj_or_eq hca hct with ⟨h1, _⟩ | h | h
  · exact absurd h1 hne
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)

/-- A `breakout` at a different cell leaves a singleton cell's position
alone. Together with `refine_fixes_singleton` this is the whole content
of the descent's position bookkeeping, one operation at a time. -/
theorem breakout_misses_singleton {lab ptn : Array Nat}
    {level a tc o : Nat} (hinj : LabInj lab lab.size)
    (hto : tc + o < lab.size) (hout : a < tc ∨ tc + o < a) :
    (breakout n lab ptn (level + 1) tc lab[tc + o]!).1[a]! = lab[a]! := by
  rw [breakout_lab_at hinj hto a]
  rcases hout with h | h
  · rw [ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

/-- Refinement preserves an existing singleton cell. -/
theorem isCell_refine_one {ctx : Ctx n} {level : Nat} {active : VSet n} {numcells a : Nat}
    {lab ptn : Array Nat} (hnn : n = ptn.size)
    (hls : lab.size = ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    (hc : IsCell ptn level a 1) :
    IsCell (Nauty.refine ctx level lab ptn active numcells).ptn
      level a 1 := by
  obtain ⟨hpos, hstart, _, hclose⟩ := hc
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rcases hstart with rfl | hstart
    · exact Or.inl rfl
    · right
      rw [refine_frozen hnn hls hend hstart]
      exact hstart
  · intro i hi hlt
    omega
  · have hclose' : ptn[a]! ≤ level := by simpa using hclose
    change (Nauty.refine ctx level lab ptn active numcells).ptn[a]! ≤ level
    rw [refine_frozen hnn hls hend hclose']
    exact hclose'

/-- Splitting a different non-singleton cell preserves a singleton. -/
theorem isCell_set_miss {ptn : Array Nat} {level a tc len : Nat}
    (ha : IsCell ptn level a 1) (ht : IsCell ptn level tc len)
    (hlen : 2 ≤ len) :
    IsCell (ptn.set! tc (level + 1)) (level + 1) a 1 := by
  have hne : tc ≠ a ∧ tc ≠ a - 1 := by
    rcases isCell_disjoint_or_eq ha ht with hleft | hright | heq
    · constructor <;> omega
    · constructor <;> omega
    · omega
  obtain ⟨hpos, hstart, _, hclose⟩ := ha
  refine ⟨hpos, ?_, ?_, ?_⟩
  · rcases hstart with rfl | hstart
    · exact Or.inl rfl
    · right
      rw [Array.getElem!_set!_ne _ _ _ _ hne.2]
      omega
  · intro i hi hlt
    omega
  · have hclose' : ptn[a]! ≤ level := by simpa using hclose
    simpa using (show (ptn.set! tc (level + 1))[a]! ≤ level + 1 by
      rw [Array.getElem!_set!_ne _ _ _ _ hne.1]
      omega)

end Hex.GraphIso.Nauty
