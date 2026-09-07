/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable.Fix
import all HexGraphIso.Nauty.Equitable.Basic

public section

/-!
Membership, bounds, and maximal runs of partition cells.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- A position with a closed partition entry is its own cell end. -/
theorem cellEnd_of_closed {ptn : Array Nat} {level i : Nat}
    (hi : i < ptn.size) (hc : ¬ ptn[i]! > level) :
    cellEnd ptn level i = i := by
  rw [cellEnd]
  have hf : ptn.size - i = (ptn.size - i - 1) + 1 := by omega
  rw [hf, cellEnd.go, ite_eq_right hc]

/-- A position with an open partition entry shares its cell end with
its successor. -/
theorem cellEnd_succ_of_open {ptn : Array Nat} {level i : Nat}
    (hi : i < ptn.size) (ho : ptn[i]! > level) :
    cellEnd ptn level i = cellEnd ptn level (i + 1) := by
  rw [cellEnd, cellEnd]
  have hf : ptn.size - i = (ptn.size - (i + 1)) + 1 := by omega
  rw [hf, cellEnd.go, ite_eq_left ho]

/-- Interior positions of a cell run are open. -/
theorem cellEnd_interior {ptn : Array Nat} {level i j : Nat}
    (hj : i ≤ j) (hlt : j < cellEnd ptn level i) : ptn[j]! > level := by
  rw [cellEnd] at hlt
  exact cellEnd_go_interior _ i j hj hlt

/-- Membership in the cell list: a start below the bound paired with
its cell end. -/
theorem mem_cells_iff {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {c e : Nat} :
    (c, e) ∈ cells ptn level nn ↔
      c < nn ∧ (c = 0 ∨ ptn[c - 1]! ≤ level) ∧
        e = cellEnd ptn level c := by
  constructor
  · intro hmem
    rw [cells] at hmem
    have hfwd : ∀ (fuel c1 : Nat), (c1 = 0 ∨ ptn[c1 - 1]! ≤ level) →
        ∀ p ∈ cells.go ptn level nn fuel c1,
          p.1 < nn ∧ (p.1 = 0 ∨ ptn[p.1 - 1]! ≤ level) ∧
            p.2 = cellEnd ptn level p.1 := by
      intro fuel
      induction fuel with
      | zero => intro c1 _ p hp; exact absurd hp (by simp [cells.go])
      | succ fuel ih =>
        intro c1 hstart p hp
        rw [cells.go] at hp
        rcases Decidable.em (c1 < nn) with hlt | hge
        · rw [ite_eq_left hlt] at hp
          simp only [List.mem_cons] at hp
          rcases hp with rfl | hmem2
          · exact ⟨hlt, hstart, rfl⟩
          · refine ih (cellEnd ptn level c1 + 1) (Or.inr ?_) p hmem2
            rw [show cellEnd ptn level c1 + 1 - 1 =
              cellEnd ptn level c1 by omega, cellEnd]
            exact cellEnd_go_end hend _ _ (by omega) (by omega)
        · rw [ite_eq_right hge] at hp
          cases hp
    exact hfwd nn 0 (Or.inl rfl) (c, e) hmem
  · rintro ⟨hc, hstart, rfl⟩
    rw [cells]
    have hbwd : ∀ (fuel c1 : Nat), nn ≤ fuel + c1 →
        (c1 = 0 ∨ ptn[c1 - 1]! ≤ level) → c1 ≤ c →
        (c, cellEnd ptn level c) ∈ cells.go ptn level nn fuel c1 := by
      intro fuel
      induction fuel with
      | zero => intro c1 hf _ hle; omega
      | succ fuel ih =>
        intro c1 hf hstart1 hle
        rw [cells.go, ite_eq_left (by omega)]
        rcases Decidable.em (c1 = c) with rfl | hne
        · exact List.mem_cons_self
        · have hgt : cellEnd ptn level c1 < c := by
            rcases Decidable.em (cellEnd ptn level c1 < c) with h | hcon
            · exact h
            · exfalso
              have hlt2 : c - 1 < cellEnd ptn level c1 := by omega
              have hopen := cellEnd_interior
                (i := c1) (j := c - 1) (by omega) hlt2
              rcases hstart with h0 | hcl
              · omega
              · omega
          have hge1 : c1 ≤ cellEnd ptn level c1 := cellEnd_ge
          refine List.mem_cons_of_mem _ (ih (cellEnd ptn level c1 + 1)
            (by omega) (Or.inr ?_) (by omega))
          rw [show cellEnd ptn level c1 + 1 - 1 =
            cellEnd ptn level c1 by omega, cellEnd]
          exact cellEnd_go_end hend _ _ (by omega) (by omega)
    exact hbwd nn 0 (by omega) (Or.inl rfl) (by omega)

/-- Cell ends agree between adjacent levels when no entry sits at the
intermediate value. -/
theorem cellEnd_succ_congr {ptn : Array Nat} {level : Nat}
    (hvals : ∀ q, q < ptn.size → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!) :
    ∀ i, cellEnd ptn (level + 1) i = cellEnd ptn level i := by
  intro i
  rw [cellEnd, cellEnd]
  have hgo : ∀ (fuel j : Nat), fuel + j ≤ ptn.size →
      cellEnd.go ptn (level + 1) fuel j = cellEnd.go ptn level fuel j := by
    intro fuel
    induction fuel with
    | zero => intro j _; rfl
    | succ fuel ih =>
      intro j hj
      rw [cellEnd.go, cellEnd.go]
      rcases hvals j (by omega) with hlo | hhi
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
      · rw [ite_eq_left (by omega), ite_eq_left (by omega),
          ih (j + 1) (by omega)]
  rcases Decidable.em (i ≤ ptn.size) with hi | hi
  · exact hgo _ _ (by omega)
  · have h0 : ptn.size - i = 0 := by omega
    rw [h0]
    rfl

/-- Cell membership agrees between adjacent levels when no entry sits
at the intermediate value. -/
theorem mem_cells_succ_congr {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q, q < ptn.size → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    {c e : Nat} :
    (c, e) ∈ cells ptn (level + 1) nn ↔ (c, e) ∈ cells ptn level nn := by
  rw [mem_cells_iff hnn (by omega),
    mem_cells_iff hnn hend, cellEnd_succ_congr hvals]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    rcases h2 with h0 | hcl
    · exact Or.inl h0
    · rcases Decidable.em (c = 0) with rfl | hne
      · exact Or.inl rfl
      · rcases hvals (c - 1) (by omega) with hlo | hhi
        · exact Or.inr hlo
        · omega
  · rintro ⟨h1, h2, h3⟩
    refine ⟨h1, ?_, h3⟩
    rcases h2 with h0 | hcl
    · exact Or.inl h0
    · exact Or.inr (by omega)

/-- Two cells of the partition list sharing a position coincide. -/
theorem cells_eq_of_shared {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {p q : Nat × Nat} (hp : p ∈ cells ptn level nn)
    (hq : q ∈ cells ptn level nn)
    {j : Nat} (hjp1 : p.1 ≤ j) (hjp2 : j ≤ p.2)
    (hjq1 : q.1 ≤ j) (hjq2 : j ≤ q.2) : p = q := by
  have hIp := cells_isCell hnn hend _ hp
  have hIq := cells_isCell hnn hend _ hq
  have hple := cells_le _ hp
  have hqle := cells_le _ hq
  rcases isCell_disj_or_eq hIp hIq with ⟨h1, h2⟩ | hd | hd
  · obtain ⟨pa, pb⟩ := p
    obtain ⟨qa, qb⟩ := q
    simp only at h1 h2 hple hqle
    have : pb = qb := by omega
    rw [h1, this]
  · omega
  · omega

end Hex.GraphIso.Nauty
