/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell
import all HexGraphIso.Nauty.Equitable

public section

/-!
The cheapautom descent and branch step (SPEC § Verified search
refinement, the code-1 arm of the store-validity obligation).

`HexGraphIso.Nauty.SmallCell` proves the guard characterization and
the flip theorem; this file carries them down the search subtree: the
descent seed (individualize-and-refine preserves equitability), the
guard's cell-size consequences, and the branch step -- the two
children of a pair target cell refine to states related by the flip,
collapsing at a discrete child to equal leaf rows.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-! # The descent seed

Individualizing a vertex of an equitable partition and refining with
the singleton active produces an equitable partition again: the
certificate invariant's entry seed is the parent's equitability, with
the split-off singleton as the one active certificate cell. These are
the entry facts `refine_equitable` consumes at every node of a search
subtree. -/

section Descent

/-- The positional effect of individualization's rotation: the target
vertex moves to the front of its cell and the displaced prefix shifts
one place right. -/
theorem breakout_go_shift {tv : Nat} :
    ∀ (fuel : Nat) (lab : Array Nat) (i prev k : Nat),
      (∀ m, m < k → lab[i + m]! ≠ tv) → lab[i + k]! = tv →
      k < fuel → i + k < lab.size →
      ∀ q, (breakout.go tv fuel lab i prev)[q]! =
        if q < i then lab[q]!
        else if q = i then prev
        else if q ≤ i + k then lab[q - 1]!
        else lab[q]!
  | fuel + 1, lab, i, prev, k, hfirst, hk, hkf, hks, q => by
    rw [breakout.go]
    rcases Decidable.em (k = 0) with rfl | hkpos
    · rw [Nat.add_zero] at hk hks
      rw [ite_eq_left (by simp [hk])]
      rcases Decidable.em (q < i) with h1 | h1
      · rw [ite_eq_left h1, Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rcases Decidable.em (q = i) with rfl | h2
        · rw [ite_eq_right (by omega), ite_eq_left rfl,
            Array.getElem!_set!_self _ _ _ hks]
        · rw [ite_eq_right h1, ite_eq_right h2,
            ite_eq_right (by omega),
            Array.getElem!_set!_ne _ _ _ _ (by omega)]
    · have h0 : lab[i]! ≠ tv := by
        have := hfirst 0 (by omega)
        rwa [Nat.add_zero] at this
      rw [ite_eq_right (by simp [h0])]
      have hres := breakout_go_shift fuel (lab.set! i prev) (i + 1)
        lab[i]! (k - 1)
        (fun m hm => by
          rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
            show i + 1 + m = i + (m + 1) by omega]
          exact hfirst (m + 1) (by omega))
        (by
          rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
            show i + 1 + (k - 1) = i + k by omega]
          exact hk)
        (by omega)
        (by rw [Array.size_set!]; omega) q
      rw [hres]
      rcases Decidable.em (q < i) with h1 | h1
      · rw [ite_eq_left (by omega), ite_eq_left h1,
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rcases Decidable.em (q = i) with rfl | h2
        · rw [ite_eq_left (by omega), ite_eq_right (by omega),
            ite_eq_left rfl, Array.getElem!_set!_self _ _ _ (by omega)]
        · rcases Decidable.em (q = i + 1) with rfl | h3
          · rw [ite_eq_right (by omega), ite_eq_left rfl,
              ite_eq_right (by omega), ite_eq_right (by omega),
              ite_eq_left (by omega : i + 1 ≤ i + k),
              show i + 1 - 1 = i by omega]
          · rw [ite_eq_right (by omega), ite_eq_right h3,
              ite_eq_right h1, ite_eq_right h2]
            rcases Decidable.em (q ≤ i + k) with h4 | h4
            · rw [ite_eq_left (by omega), ite_eq_left h4,
                Array.getElem!_set!_ne _ _ _ _ (by omega)]
            · rw [ite_eq_right (by omega), ite_eq_right h4,
                Array.getElem!_set!_ne _ _ _ _ (by omega)]

/-- Membership in a bit singleton. -/
theorem elem_single {tc v : Nat} :
    elem (insert 0 tc) v = decide (v = tc) := by
  rw [insert, elem, Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
  rcases Decidable.em (v = tc) with rfl | hne
  · rw [Nat.testBit_two_pow_self]
    simp
  · rw [Nat.testBit_two_pow_of_ne (fun h => hne h.symm)]
    simp
    omega

variable {lab ptn : Array Nat} {level tc e k : Nat}

/-- Cell-end computations agree between two partitions that agree in
openness along the walked run. -/
theorem cellEnd_congr_within {ptn' : Array Nat} {level' : Nat}
    (hsz : ptn'.size = ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel j : Nat), ptn.size ≤ fuel + j → j < ptn.size →
      (∀ q, j ≤ q → q ≤ cellEnd ptn level j →
        ((ptn'[q]! > level') ↔ (ptn[q]! > level))) →
      cellEnd ptn' level' j = cellEnd ptn level j
  | 0, j, hf, hj, _ => by omega
  | fuel + 1, j, hf, hj, hagree => by
    rcases Decidable.em (ptn[j]! > level) with ho | hc
    · have ho' : ptn'[j]! > level' :=
        (hagree j (Nat.le_refl _) cellEnd_ge).mpr ho
      have hlt : cellEnd ptn level j < ptn.size := cellEnd_lt hj hend
      have hstep : cellEnd ptn level j = cellEnd ptn level (j + 1) :=
        cellEnd_succ_of_open hj ho
      have hj1 : j + 1 < ptn.size := by
        have := cellEnd_ge (ptn := ptn) (level := level) (i := j + 1)
        omega
      rw [cellEnd_succ_of_open (by omega) ho',
        cellEnd_succ_of_open hj ho]
      exact cellEnd_congr_within hsz hend fuel (j + 1) (by omega) hj1
        (fun q hq1 hq2 => hagree q (by omega) (by rw [hstep]; omega))
    · have hc' : ¬ ptn'[j]! > level' := fun h =>
        hc ((hagree j (Nat.le_refl _) cellEnd_ge).mp h)
      rw [cellEnd_of_closed (by omega) hc', cellEnd_of_closed hj hc]

/-- The end of a cell walk is closed. -/
theorem cellEnd_closed (hend : ptn[ptn.size - 1]! ≤ level)
    {i : Nat} (hi : i < ptn.size) :
    ptn[cellEnd ptn level i]! ≤ level := by
  rw [cellEnd]
  exact cellEnd_go_end hend _ _ hi (by omega)

/-- A start left of another start closes its cell before it. -/
theorem cellEnd_lt_start
    {c : Nat} (hc : c < tc) (htcs : ptn[tc - 1]! ≤ level) :
    cellEnd ptn level c < tc := by
  rcases Decidable.em (cellEnd ptn level c < tc) with h | h
  · exact h
  · exfalso
    rcases Decidable.em (tc - 1 < cellEnd ptn level c) with h2 | h2
    · have := cellEnd_interior (i := c) (j := tc - 1) (by omega) h2
      omega
    · have : cellEnd ptn level c = tc - 1 := by omega
      omega

section Split

variable (hpsz : ptn.size = ctx.n) (hn : 0 < ctx.n)
  (hend : ptn[ptn.size - 1]! ≤ level)
  (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
  (hcell : (tc, e) ∈ cells ptn level ctx.n) (hne : tc < e)

include hpsz hend hcell

/-- The target cell's interior is open. -/
theorem target_open : ∀ q, tc ≤ q → q < e → ptn[q]! > level := by
  intro q hq1 hq2
  obtain ⟨-, -, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  exact cellEnd_interior hq1 (by omega)

/-- The target cell's end is closed. -/
theorem target_end_closed : ptn[e]! ≤ level := by
  obtain ⟨h1, -, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  rw [he]
  exact cellEnd_closed hend (by omega)

/-- The target cell's end is in range. -/
theorem target_end_lt : e < ctx.n := by
  obtain ⟨h1, -, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  rw [he, ← hpsz]
  exact cellEnd_lt (by omega) hend

/-- The split-off singleton is a cell of the child partition. -/
theorem child_cells_singleton :
    (tc, tc) ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n := by
  obtain ⟨h1, h2, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  have hsz : (ptn.set! tc (level + 1)).size = ptn.size := Array.size_set! _ _ _
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  rw [mem_cells_iff (by omega) hend']
  refine ⟨h1, ?_, ?_⟩
  · rcases Decidable.em (tc = 0) with rfl | h0
    · exact Or.inl rfl
    · rcases h2 with h00 | hcl
      · exact Or.inl h00
      · refine Or.inr ?_
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
  · rw [cellEnd_of_closed (by rw [hsz]; omega) (by
      rw [Array.getElem!_set!_self _ _ _ (by rw [hpsz]; omega)]
      omega)]

include hvals hne

/-- The remainder is a cell of the child partition. -/
theorem child_cells_rest :
    (tc + 1, e) ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n := by
  obtain ⟨h1, h2, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  have hen := target_end_lt hpsz hend hcell
  have hsz : (ptn.set! tc (level + 1)).size = ptn.size := Array.size_set! _ _ _
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  rw [mem_cells_iff (by omega) hend']
  refine ⟨by omega, Or.inr ?_, ?_⟩
  · rw [show tc + 1 - 1 = tc by omega,
      Array.getElem!_set!_self _ _ _ (by rw [hpsz]; omega)]
    omega
  · have hopen : ptn[tc]! > level := target_open hpsz hend hcell tc
      (Nat.le_refl _) hne
    have he1 : cellEnd ptn level (tc + 1) = e := by
      rw [he]
      exact (cellEnd_succ_of_open (by omega) hopen).symm
    rw [← he1]
    refine (cellEnd_congr_within hsz hend ptn.size (tc + 1) (by omega)
      (by omega) ?_).symm
    intro q hq1 hq2
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    rw [he1] at hq2
    rcases hvals q (by omega) with hlo | hhi
    · constructor <;> omega
    · constructor <;> omega

/-- A parent cell away from the target survives into the child
partition. -/
theorem child_cells_old {c ce : Nat}
    (hmem : (c, ce) ∈ cells ptn level ctx.n) (hcne : c ≠ tc) :
    (c, ce) ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n := by
  obtain ⟨h1, h2, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  obtain ⟨hc1, hc2, hce⟩ := (mem_cells_iff (by omega) hend).mp hmem
  have hen := target_end_lt hpsz hend hcell
  have hsz : (ptn.set! tc (level + 1)).size = ptn.size := Array.size_set! _ _ _
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  have hgt : c > tc → c > e := by
    intro hgt
    rcases Decidable.em (c ≤ e) with hle | hgt2
    · exfalso
      have hop := target_open hpsz hend hcell (c - 1) (by omega)
        (by omega)
      rcases hc2 with h0 | hcl
      · omega
      · omega
    · omega
  rw [mem_cells_iff (by omega) hend']
  refine ⟨hc1, ?_, ?_⟩
  · rcases hc2 with h0 | hcl
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases Decidable.em (c < tc) with hlt | hge
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
      · have := hgt (by omega)
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
  · rcases Decidable.em (c < tc) with hlt | hge
    · have htcs : ptn[tc - 1]! ≤ level := by
        rcases h2 with h0 | hcl
        · omega
        · exact hcl
      have hlt2 : cellEnd ptn level c < tc :=
        cellEnd_lt_start hlt htcs
      rw [hce]
      refine (cellEnd_congr_within hsz hend ptn.size c (by omega)
        (by omega) ?_).symm
      intro q hq1 hq2
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      rcases hvals q (by omega) with hlo | hhi
      · constructor <;> omega
      · constructor <;> omega
    · have hgtc := hgt (by omega)
      have hlt3 : cellEnd ptn level c < ptn.size :=
        cellEnd_lt (by omega) hend
      rw [hce]
      refine (cellEnd_congr_within hsz hend ptn.size c (by omega)
        (by omega) ?_).symm
      intro q hq1 hq2
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      rcases hvals q (by omega) with hlo | hhi
      · constructor <;> omega
      · constructor <;> omega

/-- Every cell of the child partition is the singleton, the remainder,
or a parent cell away from the target. -/
theorem child_cells_cases {p : Nat × Nat}
    (hp : p ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n) :
    p = (tc, tc) ∨ p = (tc + 1, e) ∨
      (p ∈ cells ptn level ctx.n ∧ p.1 ≠ tc) := by
  obtain ⟨h1, h2, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  have hen := target_end_lt hpsz hend hcell
  have hsz : (ptn.set! tc (level + 1)).size = ptn.size := Array.size_set! _ _ _
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  obtain ⟨hp1, hp2, hpe⟩ := (mem_cells_iff (by omega) hend').mp hp
  rcases Decidable.em (p.1 = tc) with heq | hne1
  · refine Or.inl ?_
    have hpe2 : p.2 = tc := by
      rw [hpe, heq]
      exact cellEnd_of_closed (by rw [hsz, hpsz]; omega) (by
        rw [Array.getElem!_set!_self _ _ _ (by rw [hpsz]; omega)]
        omega)
    obtain ⟨a, b⟩ := p
    simp_all
  · rcases Decidable.em (p.1 = tc + 1) with heq1 | hne2
    · refine Or.inr (Or.inl ?_)
      have hmem := child_cells_rest hpsz hend hvals hcell hne
      obtain ⟨-, -, he2⟩ := (mem_cells_iff (by omega) hend').mp hmem
      have hpe2 : p.2 = e := by
        rw [hpe, heq1, ← he2]
      obtain ⟨a, b⟩ := p
      simp_all
    · refine Or.inr (Or.inr ⟨?_, hne1⟩)
      have hstart : p.1 = 0 ∨ ptn[p.1 - 1]! ≤ level := by
        rcases hp2 with h0 | hcl
        · exact Or.inl h0
        · refine Or.inr ?_
          rcases Decidable.em (p.1 - 1 = tc) with heq2 | hne3
          · omega
          · rw [Array.getElem!_set!_ne _ _ _ _
              (fun h => hne3 h.symm)] at hcl
            rcases hvals (p.1 - 1) (by omega) with hlo | hhi
            · exact hlo
            · omega
      rw [mem_cells_iff (by omega) hend]
      refine ⟨hp1, hstart, ?_⟩
      have hgt : tc < p.1 → e < p.1 := by
        intro hgt
        rcases Decidable.em (p.1 ≤ e) with hle | hgt2
        · exfalso
          have hop := target_open hpsz hend hcell (p.1 - 1) (by omega)
            (by omega)
          rcases hstart with h0 | hcl
          · omega
          · omega
        · omega
      rcases Decidable.em (p.1 < tc) with hlt | hge
      · have htcs : ptn[tc - 1]! ≤ level := by
          rcases h2 with h0 | hcl
          · omega
          · exact hcl
        have hlt2 : cellEnd ptn level p.1 < tc :=
          cellEnd_lt_start hlt htcs
        rw [hpe]
        exact cellEnd_congr_within hsz hend ptn.size p.1 (by omega)
          (by omega) (by
            intro q hq1 hq2
            rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
            rcases hvals q (by omega) with hlo | hhi
            · constructor <;> omega
            · constructor <;> omega)
      · have hgtc := hgt (by omega)
        have hlt3 : cellEnd ptn level p.1 < ptn.size :=
          cellEnd_lt (by omega) hend
        rw [hpe]
        exact cellEnd_congr_within hsz hend ptn.size p.1 (by omega)
          (by omega) (by
            intro q hq1 hq2
            rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
            rcases hvals q (by omega) with hlo | hhi
            · constructor <;> omega
            · constructor <;> omega)

end Split

section Labelling

variable {lab ptn : Array Nat} {level tc e o : Nat}

/-- The rotated labelling positionally, at an injectively unique
target vertex. -/
theorem breakout_lab_at
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size) :
    ∀ q, (breakout lab ptn (level + 1) tc lab[tc + o]!).1[q]! =
      if q < tc then lab[q]!
      else if q = tc then lab[tc + o]!
      else if q ≤ tc + o then lab[q - 1]!
      else lab[q]! := by
  intro q
  show (breakout.go lab[tc + o]! (lab.size + 1) lab tc
    lab[tc + o]!)[q]! = _
  exact breakout_go_shift (lab.size + 1) lab tc lab[tc + o]! o
    (fun m hm heq => by
      have := hinj (tc + m) (tc + o) (by omega) (by omega) heq
      omega)
    rfl (by omega) hto q

/-- The rotated labelling stays injective. -/
theorem labInj_breakout
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size) :
    LabInj (breakout lab ptn (level + 1) tc lab[tc + o]!).1 lab.size := by
  intro i j hi hj hv
  rw [breakout_lab_at hinj hto i, breakout_lab_at hinj hto j] at hv
  rcases Decidable.em (i < tc) with hi1 | hi1 <;>
    rcases Decidable.em (j < tc) with hj1 | hj1
  · rw [ite_eq_left hi1, ite_eq_left hj1] at hv
    exact hinj i j hi hj hv
  · rw [ite_eq_left hi1] at hv
    rcases Decidable.em (j = tc) with heqj | hj2
    · rw [ite_eq_right hj1, ite_eq_left heqj] at hv
      have := hinj i (tc + o) hi (by omega) hv
      omega
    · rcases Decidable.em (j ≤ tc + o) with hj3 | hj3
      · rw [ite_eq_right hj1, ite_eq_right hj2, ite_eq_left hj3] at hv
        have := hinj i (j - 1) hi (by omega) hv
        omega
      · rw [ite_eq_right hj1, ite_eq_right hj2, ite_eq_right hj3] at hv
        have := hinj i j hi hj hv
        omega
  · rw [ite_eq_left hj1] at hv
    rcases Decidable.em (i = tc) with heqi | hi2
    · rw [ite_eq_right hi1, ite_eq_left heqi] at hv
      have := hinj (tc + o) j (by omega) hj hv
      omega
    · rcases Decidable.em (i ≤ tc + o) with hi3 | hi3
      · rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_left hi3] at hv
        have := hinj (i - 1) j (by omega) hj hv
        omega
      · rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_right hi3] at hv
        have := hinj i j hi hj hv
        omega
  · rcases Decidable.em (i = tc) with heqi | hi2 <;>
      rcases Decidable.em (j = tc) with heqj | hj2
    · omega
    · rw [ite_eq_right hi1, ite_eq_left heqi, ite_eq_right hj1,
        ite_eq_right hj2] at hv
      rcases Decidable.em (j ≤ tc + o) with hj3 | hj3
      · rw [ite_eq_left hj3] at hv
        have := hinj (tc + o) (j - 1) (by omega) (by omega) hv
        omega
      · rw [ite_eq_right hj3] at hv
        have := hinj (tc + o) j (by omega) hj hv
        omega
    · rw [ite_eq_right hj1, ite_eq_left heqj, ite_eq_right hi1,
        ite_eq_right hi2] at hv
      rcases Decidable.em (i ≤ tc + o) with hi3 | hi3
      · rw [ite_eq_left hi3] at hv
        have := hinj (i - 1) (tc + o) (by omega) (by omega) hv
        omega
      · rw [ite_eq_right hi3] at hv
        have := hinj i (tc + o) hi (by omega) hv
        omega
    · rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_right hj1,
        ite_eq_right hj2] at hv
      rcases Decidable.em (i ≤ tc + o) with hi3 | hi3 <;>
        rcases Decidable.em (j ≤ tc + o) with hj3 | hj3
      · rw [ite_eq_left hi3, ite_eq_left hj3] at hv
        have := hinj (i - 1) (j - 1) (by omega) (by omega) hv
        omega
      · rw [ite_eq_left hi3, ite_eq_right hj3] at hv
        have := hinj (i - 1) j (by omega) hj hv
        omega
      · rw [ite_eq_right hi3, ite_eq_left hj3] at hv
        have := hinj i (j - 1) hi (by omega) hv
        omega
      · rw [ite_eq_right hi3, ite_eq_right hj3] at hv
        exact hinj i j hi hj hv

/-- Any-membership transfers along a membership equivalence. -/
private theorem any_beq_congr {l1 l2 : List Nat}
    (h : ∀ v, v ∈ l1 ↔ v ∈ l2) (v : Nat) :
    l1.any (· == v) = l2.any (· == v) := by
  rcases hb : l2.any (· == v) with _ | _
  · refine List.any_eq_false.mpr fun x hx hxv => ?_
    exact List.any_eq_false.mp hb x ((h x).mp hx) hxv
  · obtain ⟨x, hx, hxv⟩ := List.any_eq_true.mp hb
    exact List.any_eq_true.mpr ⟨x, (h x).mpr hx, hxv⟩

/-- The rotated target window has the same members. -/
private theorem mem_segN_breakout_target {lab ptn : Array Nat}
    {level tc e o : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size)
    (hoe : o ≤ e - tc) (hte : tc ≤ e) :
    ∀ v, v ∈ segN (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1 tc (e + 1 - tc) ↔
      v ∈ segN lab tc (e + 1 - tc) := by
  intro v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv
    rw [breakout_lab_at hinj hto (tc + w)] at hwv
    refine mem_segN_iff.mpr ?_
    rcases Decidable.em (w = 0) with rfl | hw0
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)] at hwv
      exact ⟨o, by omega, hwv⟩
    · rcases Decidable.em (w ≤ o) with hwo | hwo
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left (by omega)] at hwv
        exact ⟨w - 1, by omega, by
          rw [show tc + (w - 1) = tc + w - 1 by omega]
          exact hwv⟩
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)] at hwv
        exact ⟨w, by omega, hwv⟩
  · intro hv
    obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv
    refine mem_segN_iff.mpr ?_
    rcases Decidable.em (w = o) with heqw | hwo
    · refine ⟨0, by omega, ?_⟩
      rw [breakout_lab_at hinj hto (tc + 0),
        ite_eq_right (by omega), ite_eq_left (by omega), ← heqw]
      exact hwv
    · rcases Decidable.em (w < o) with hlt | hgt
      · refine ⟨w + 1, by omega, ?_⟩
        rw [breakout_lab_at hinj hto (tc + (w + 1)),
          ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left (by omega),
          show tc + (w + 1) - 1 = tc + w by omega]
        exact hwv
      · refine ⟨w, by omega, ?_⟩
        rw [breakout_lab_at hinj hto (tc + w),
          ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        exact hwv

/-- The full target window's vertex set survives the rotation. -/
theorem worksetOf_breakout_full {lab ptn : Array Nat}
    {level tc e o : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size)
    (hoe : o ≤ e - tc) (hte : tc ≤ e) :
    worksetOf (breakout lab ptn (level + 1) tc lab[tc + o]!).1 tc e =
      worksetOf lab tc e := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  rw [testBit_worksetOf, testBit_worksetOf]
  exact any_beq_congr (mem_segN_breakout_target hinj hto hoe hte) v

/-- Vertex sets of windows away from the rotation are untouched. -/
theorem worksetOf_breakout_outside {a b : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size)
    (hout : b < tc ∨ tc + o < a) :
    worksetOf (breakout lab ptn (level + 1) tc lab[tc + o]!).1 a b =
      worksetOf lab a b := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  rw [testBit_worksetOf, testBit_worksetOf]
  have hpt : ∀ w, w < b + 1 - a →
      (breakout lab ptn (level + 1) tc lab[tc + o]!).1[a + w]! =
        lab[a + w]! := by
    intro w hw
    rw [breakout_lab_at hinj hto (a + w)]
    rcases hout with h | h
    · rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
  rcases hb : (segN lab a (b + 1 - a)).any (· == v) with _ | _
  · refine List.any_eq_false.mpr fun x hx hxv => ?_
    obtain ⟨w, hw, hwx⟩ := mem_segN_iff.mp hx
    rw [hpt w hw] at hwx
    exact List.any_eq_false.mp hb x
      (mem_segN_iff.mpr ⟨w, hw, hwx⟩) hxv
  · obtain ⟨x, hx, hxv⟩ := List.any_eq_true.mp hb
    obtain ⟨w, hw, hwx⟩ := mem_segN_iff.mp hx
    refine List.any_eq_true.mpr ⟨x, mem_segN_iff.mpr ⟨w, hw, ?_⟩, hxv⟩
    rw [hpt w hw, hwx]

end Labelling

section Seed

private theorem or_self_right (a w : Nat) : a ||| w ||| w = a ||| w := by
  rw [Nat.or_assoc, Nat.or_self]

private theorem foldl_union_none {act : Nat} {lab : Array Nat} :
    ∀ (l : List (Nat × Nat)) (A : Nat),
      (∀ p ∈ l, elem act p.1 = false) →
      l.foldl (fun A p => if elem act p.1 then
        A ||| worksetOf lab p.1 p.2 else A) A = A
  | [], A, _ => rfl
  | q :: l, A, h => by
    rw [List.foldl_cons, ite_eq_right (by
      rw [h q List.mem_cons_self]
      simp)]
    exact foldl_union_none l A fun p hp => h p (List.mem_cons_of_mem _ hp)

private theorem foldl_union_from {act W : Nat} {lab : Array Nat} :
    ∀ (l : List (Nat × Nat)) (A : Nat),
      (∀ p ∈ l, elem act p.1 = true → worksetOf lab p.1 p.2 = W) →
      l.foldl (fun A p => if elem act p.1 then
        A ||| worksetOf lab p.1 p.2 else A) (A ||| W) = A ||| W
  | [], A, _ => rfl
  | q :: l, A, h => by
    rw [List.foldl_cons]
    rcases hq : elem act q.1 with _ | _
    · rw [ite_eq_right (by simp [hq])]
      exact foldl_union_from l A
        fun p hp => h p (List.mem_cons_of_mem _ hp)
    · rw [ite_eq_left (by simp [hq]), h q List.mem_cons_self hq,
        or_self_right]
      exact foldl_union_from l A
        fun p hp => h p (List.mem_cons_of_mem _ hp)

private theorem foldl_union_single {act W : Nat} {lab : Array Nat} :
    ∀ (l : List (Nat × Nat)) (A : Nat),
      (∀ p ∈ l, elem act p.1 = true → worksetOf lab p.1 p.2 = W) →
      (∃ p ∈ l, elem act p.1 = true) →
      l.foldl (fun A p => if elem act p.1 then
        A ||| worksetOf lab p.1 p.2 else A) A = A ||| W
  | [], _, _, ⟨p, hp, _⟩ => absurd hp (by simp)
  | q :: l, A, h, ⟨p, hp, hpa⟩ => by
    rw [List.foldl_cons]
    rcases hq : elem act q.1 with _ | _
    · rw [ite_eq_right (by simp [hq])]
      have hpl : p ∈ l := by
        rcases List.mem_cons.mp hp with rfl | hmem
        · rw [hq] at hpa
          cases hpa
        · exact hmem
      exact foldl_union_single l A
        (fun p hp2 => h p (List.mem_cons_of_mem _ hp2)) ⟨p, hpl, hpa⟩
    · rw [ite_eq_left (by simp [hq]), h q List.mem_cons_self hq]
      exact foldl_union_from l A
        fun p hp2 => h p (List.mem_cons_of_mem _ hp2)

variable {lab ptn : Array Nat} {level tc e o numcells : Nat}

variable (hlsz : lab.size = ctx.n) (hpsz : ptn.size = ctx.n)
  (hend : ptn[ptn.size - 1]! ≤ level)
  (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
  (hinj : LabInj lab ctx.n)
  (hcell : (tc, e) ∈ cells ptn level ctx.n) (hne : tc < e)
  (ho : o ≤ e - tc)

include hlsz hpsz hend hvals hinj hcell hne ho

/-- The active union of the child entry state is the split-off
singleton's vertex. -/
theorem activeUnion_breakout :
    activeUnion ctx (level + 1)
      { lab := (breakout lab ptn (level + 1) tc lab[tc + o]!).1,
        ptn := ptn.set! tc (level + 1), active := insert 0 tc,
        numcells := numcells + 1, hint := 0, maxpos := 0,
        longcode := numcells + 1 } =
      worksetOf (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        tc tc := by
  have hen := target_end_lt hpsz hend hcell
  unfold activeUnion
  refine foldl_union_single _ 0 ?_ ?_ |>.trans (Nat.zero_or _)
  · intro p hp hpa
    rw [elem_single] at hpa
    have hptc : p.1 = tc := by
      have := of_decide_eq_true hpa
      exact this
    rcases child_cells_cases hpsz hend hvals hcell hne hp with
      rfl | rfl | ⟨-, hne2⟩
    · rfl
    · exact absurd hptc (by omega)
    · exact absurd hptc hne2
  · exact ⟨(tc, tc),
      child_cells_singleton hpsz hend hcell, by
        rw [elem_single]
        simp⟩

/-- The singleton's vertex saturates every child cell: it is the whole
splitter set of the singleton and misses every other cell. -/
theorem saturated_breakout :
    Saturated ctx (level + 1)
      { lab := (breakout lab ptn (level + 1) tc lab[tc + o]!).1,
        ptn := ptn.set! tc (level + 1), active := insert 0 tc,
        numcells := numcells + 1, hint := 0, maxpos := 0,
        longcode := numcells + 1 }
      (worksetOf (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        tc tc) := by
  have hen := target_end_lt hpsz hend hcell
  have hinj' := labInj_breakout (lab := lab) (ptn := ptn)
    (level := level) (tc := tc) (o := o)
    (by rw [hlsz]; exact hinj) (by omega)
  intro q hq
  rcases child_cells_cases hpsz hend hvals hcell hne hq with
    rfl | rfl | ⟨hqm, hne2⟩
  · exact Or.inr (Nat.and_self _)
  · refine Or.inl (worksetOf_disjoint fun v hv1 hv2 => ?_)
    obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv1
    obtain ⟨w', hw', hwv'⟩ := mem_segN_iff.mp hv2
    have hw0 : w' = 0 := by omega
    subst hw0
    have hwv2 : (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1[tc + 1 + w]! = v := hwv
    have hwv3 : (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1[tc + 0]! = v := hwv'
    have := hinj' (tc + 0) (tc + 1 + w) (by rw [hlsz]; omega)
      (by rw [hlsz]; omega) (hwv3.trans hwv2.symm)
    omega
  · obtain ⟨hq1, hq2, hqe⟩ := (mem_cells_iff (by omega) hend).mp hqm
    have hout : q.2 < tc ∨ e < q.1 := by
      rcases Decidable.em (q.1 < tc) with hlt | hge
      · obtain ⟨-, h2t, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
        have htcs : ptn[tc - 1]! ≤ level := by
          rcases h2t with h0 | hcl
          · omega
          · exact hcl
        refine Or.inl ?_
        rw [hqe]
        exact cellEnd_lt_start hlt htcs
      · refine Or.inr ?_
        rcases Decidable.em (q.1 ≤ e) with hle | hgt
        · exfalso
          have hop := target_open hpsz hend hcell (q.1 - 1) (by omega)
            (by omega)
          rcases hq2 with h0 | hcl
          · omega
          · omega
        · omega
    have hq2lt : q.2 < ctx.n := by
      rw [hqe, ← hpsz]
      exact cellEnd_lt (by omega) hend
    have hq12 : q.1 ≤ q.2 := by
      rw [hqe]
      exact cellEnd_ge
    refine Or.inl (worksetOf_disjoint fun v hv1 hv2 => ?_)
    obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv1
    obtain ⟨w', hw', hwv'⟩ := mem_segN_iff.mp hv2
    have hw0 : w' = 0 := by omega
    subst hw0
    have hwv2 : (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1[q.1 + w]! = v := hwv
    have hwv3 : (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1[tc + 0]! = v := hwv'
    have := hinj' (tc + 0) (q.1 + w) (by rw [hlsz]; omega)
      (by rw [hlsz]; omega) (hwv3.trans hwv2.symm)
    rcases hout with h | h <;> omega

/-- Unchanged windows keep their member lists. -/
private theorem segN_breakout_congr {a len : Nat}
    (hout : a + len ≤ tc ∨ tc + o < a) :
    segN (breakout lab ptn (level + 1) tc lab[tc + o]!).1 a len =
      segN lab a len := by
  rw [segN, segN]
  refine List.map_congr_left fun w hw => ?_
  have hwr := List.mem_range.mp hw
  rw [breakout_lab_at (by rw [hlsz]; exact hinj)
    (by have := target_end_lt hpsz hend hcell; rw [hlsz]; omega)]
  rcases hout with h | h
  · rw [ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]

/-- Members of the rotated target window sit inside the parent target
window. -/
private theorem segN_breakout_target_sub {a len : Nat}
    (hin : tc ≤ a) (hlen : a + len ≤ e + 1) :
    ∀ v ∈ segN (breakout lab ptn (level + 1) tc lab[tc + o]!).1 a len,
      v ∈ segN lab tc (e + 1 - tc) := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv
  rw [breakout_lab_at (by rw [hlsz]; exact hinj)
    (by have := target_end_lt hpsz hend hcell; rw [hlsz]; omega)] at hwv
  refine mem_segN_iff.mpr ?_
  rcases Decidable.em (a + w < tc) with h1 | h1
  · omega
  · rcases Decidable.em (a + w = tc) with h2 | h2
    · rw [ite_eq_right h1, ite_eq_left h2] at hwv
      exact ⟨o, by omega, hwv⟩
    · rcases Decidable.em (a + w ≤ tc + o) with h3 | h3
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] at hwv
        exact ⟨a + w - 1 - tc, by omega, by
          rw [show tc + (a + w - 1 - tc) = a + w - 1 by omega]
          exact hwv⟩
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at hwv
        exact ⟨a + w - tc, by omega, by
          rw [show tc + (a + w - tc) = a + w by omega]
          exact hwv⟩

variable (hE : Equitable ctx level lab ptn)

include hE

/-- A child cell's members are covered by a parent cell's constancy
into any parent-cell splitter set. -/
private theorem constOn_child {W : Nat} {c : Nat × Nat}
    (hc : c ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n)
    (hW : ∀ pc ∈ cells ptn level ctx.n,
      ConstOn ctx W (segN lab pc.1 (pc.2 + 1 - pc.1))) :
    ConstOn ctx W
      (segN (breakout lab ptn (level + 1) tc lab[tc + o]!).1 c.1
        (c.2 + 1 - c.1)) := by
  rcases child_cells_cases hpsz hend hvals hcell hne hc with
    rfl | rfl | ⟨hcm, hne2⟩
  · exact (hW _ hcell).mono
      (segN_breakout_target_sub hlsz hpsz hend hvals hinj hcell hne ho
        (Nat.le_refl _) (by omega))
  · exact (hW _ hcell).mono
      (segN_breakout_target_sub hlsz hpsz hend hvals hinj hcell hne ho
        (by omega) (by omega))
  · obtain ⟨hq1, hq2, hqe⟩ := (mem_cells_iff (by omega) hend).mp hcm
    have hout : c.2 < tc ∨ e < c.1 := by
      rcases Decidable.em (c.1 < tc) with hlt | hge
      · obtain ⟨-, h2t, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
        have htcs : ptn[tc - 1]! ≤ level := by
          rcases h2t with h0 | hcl
          · omega
          · exact hcl
        refine Or.inl ?_
        rw [hqe]
        exact cellEnd_lt_start hlt htcs
      · refine Or.inr ?_
        rcases Decidable.em (c.1 ≤ e) with hle | hgt
        · exfalso
          have hop := target_open hpsz hend hcell (c.1 - 1) (by omega)
            (by omega)
          rcases hq2 with h0 | hcl
          · omega
          · omega
        · omega
    have hc12 : c.1 ≤ c.2 := by
      rw [hqe]
      exact cellEnd_ge
    rw [segN_breakout_congr hlsz hpsz hend hvals hinj hcell hne ho (by
      rcases hout with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))]
    exact hW _ hcm

/-- The certificate invariant of the child entry state: the parent's
equitability seeds every certificate, with the split-off singleton as
the one active cell. -/
theorem certInv_breakout :
    CertInv ctx (level + 1)
      { lab := (breakout lab ptn (level + 1) tc lab[tc + o]!).1,
        ptn := ptn.set! tc (level + 1), active := insert 0 tc,
        numcells := numcells + 1, hint := 0, maxpos := 0,
        longcode := numcells + 1 } := by
  intro p hp hpin c hc
  have hen := target_end_lt hpsz hend hcell
  rcases child_cells_cases hpsz hend hvals hcell hne hp with
    rfl | rfl | ⟨hpm, hne2⟩
  · rw [elem_single] at hpin
    simp at hpin
  · refine ⟨worksetOf (breakout lab ptn (level + 1) tc
      lab[tc + o]!).1 tc tc, ?_, ?_, ?_⟩
    · rw [activeUnion_breakout hlsz hpsz hend hvals hinj hcell hne ho]
      exact Nat.and_self _
    · exact saturated_breakout hlsz hpsz hend hvals hinj hcell hne ho
    · have hsplit : worksetOf (breakout lab ptn (level + 1) tc
          lab[tc + o]!).1 tc e =
          worksetOf (breakout lab ptn (level + 1) tc
            lab[tc + o]!).1 tc tc |||
          worksetOf (breakout lab ptn (level + 1) tc
            lab[tc + o]!).1 (tc + 1) e :=
        worksetOf_split (Nat.le_refl _) hne
      have hfull : worksetOf (breakout lab ptn (level + 1) tc
          lab[tc + o]!).1 tc e = worksetOf lab tc e :=
        worksetOf_breakout_full (by rw [hlsz]; exact hinj)
          (by rw [hlsz]; omega) ho (by omega)
      have hkey : worksetOf (breakout lab ptn (level + 1) tc
          lab[tc + o]!).1 (tc + 1) e |||
          worksetOf (breakout lab ptn (level + 1) tc
            lab[tc + o]!).1 tc tc = worksetOf lab tc e := by
        rw [Nat.or_comm, ← hsplit, hfull]
      rw [hkey]
      refine constOn_child hlsz hpsz hend hvals hinj hcell hne ho hE
        hc ?_
      intro pc hpc
      rw [← splitDone_iff_constOn]
      exact hE _ hpc _ hcell
  · refine ⟨0, Nat.zero_and _, fun q hq => Or.inl (Nat.and_zero _),
      ?_⟩
    rw [Nat.or_zero]
    obtain ⟨hq1, hq2, hqe⟩ := (mem_cells_iff (by omega) hend).mp hpm
    have hout : p.2 < tc ∨ e < p.1 := by
      rcases Decidable.em (p.1 < tc) with hlt | hge
      · obtain ⟨-, h2t, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
        have htcs : ptn[tc - 1]! ≤ level := by
          rcases h2t with h0 | hcl
          · omega
          · exact hcl
        refine Or.inl ?_
        rw [hqe]
        exact cellEnd_lt_start hlt htcs
      · refine Or.inr ?_
        rcases Decidable.em (p.1 ≤ e) with hle | hgt
        · exfalso
          have hop := target_open hpsz hend hcell (p.1 - 1) (by omega)
            (by omega)
          rcases hq2 with h0 | hcl
          · omega
          · omega
        · omega
    have hWp : worksetOf (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1 p.1 p.2 = worksetOf lab p.1 p.2 :=
      worksetOf_breakout_outside (by rw [hlsz]; exact hinj)
        (by rw [hlsz]; omega)
        (by rcases hout with h | h
            · exact Or.inl h
            · exact Or.inr (by omega))
    rw [hWp]
    refine constOn_child hlsz hpsz hend hvals hinj hcell hne ho hE
      hc ?_
    intro pc hpc
    rw [← splitDone_iff_constOn]
    exact hE _ hpc _ hpm

end Seed

section Package

variable {lab ptn : Array Nat} {level tc e o numcells : Nat}

/-- Splitting one open position advances the boundary count by exactly
one at the next level. -/
theorem bcount_breakout_eq {nn : Nat}
    (hvals : ∀ q, q < nn → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (htc : ptn[tc]! > level) (htcs : tc < ptn.size) :
    ∀ m, m ≤ nn →
      bcount (ptn.set! tc (level + 1)) (level + 1) m =
        bcount ptn level m + (if tc < m then 1 else 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [ite_eq_right (by omega)]
    rw [bcount, bcount]
    simp
  | succ m ih =>
    intro hm
    rw [bcount_succ, bcount_succ, ih (by omega)]
    rcases Decidable.em (tc = m) with heq | hne
    · have hset : (ptn.set! tc (level + 1))[m]! = level + 1 := by
        rw [← heq]
        exact Array.getElem!_set!_self _ _ _ htcs
      have hm2 : ¬ ptn[m]! ≤ level := by
        rw [← heq]
        omega
      rw [hset,
        ite_eq_left (by omega : level + 1 ≤ level + 1),
        ite_eq_right (by omega : ¬ tc < m),
        ite_eq_right hm2,
        ite_eq_left (by omega : tc < m + 1)]
    · have hset : (ptn.set! tc (level + 1))[m]! = ptn[m]! :=
        Array.getElem!_set!_ne _ _ _ _ hne
      rw [hset]
      rcases hvals m (by omega) with hlo | hhi
      · rw [ite_eq_left (show ptn[m]! ≤ level + 1 by omega),
          ite_eq_left hlo]
        rcases Decidable.em (tc < m) with h | h
        · rw [ite_eq_left h, ite_eq_left (show tc < m + 1 by omega)]
        · rw [ite_eq_right h,
            ite_eq_right (show ¬ tc < m + 1 by omega)]
      · rw [ite_eq_right (show ¬ ptn[m]! ≤ level + 1 by omega),
          ite_eq_right (show ¬ ptn[m]! ≤ level by omega)]
        rcases Decidable.em (tc < m) with h | h
        · rw [ite_eq_left h, ite_eq_left (show tc < m + 1 by omega)]
        · rw [ite_eq_right h,
            ite_eq_right (show ¬ tc < m + 1 by omega)]

/-- The descent theorem: individualizing any vertex of a nontrivial
cell of an equitable partition and refining with the singleton active
yields an equitable partition at the next level. -/
theorem equitable_breakout
    (hlsz : lab.size = ctx.n) (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (hlab : LabOk lab ctx.n) (hinj : LabInj lab ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hE : Equitable ctx level lab ptn)
    (hcell : (tc, e) ∈ cells ptn level ctx.n) (hne : tc < e)
    (ho : o ≤ e - tc)
    (hacc : bcount ptn level ctx.n = numcells) :
    Equitable ctx (level + 1)
      (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        (ptn.set! tc (level + 1)) (insert 0 tc) (numcells + 1)).lab
      (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        (ptn.set! tc (level + 1)) (insert 0 tc) (numcells + 1)).ptn := by
  have hen := target_end_lt hpsz hend hcell
  have htcn : tc < ctx.n := by omega
  have hto : tc + o < lab.size := by rw [hlsz]; omega
  obtain ⟨-, hstart, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
  have hopen : ptn[tc]! > level :=
    target_open hpsz hend hcell tc (Nat.le_refl _) hne
  refine refine_equitable ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsymm ?_ ?_
  · rw [breakout_lab_size, hlsz]
  · intro i hi
    rw [breakout_lab_size] at hi
    rw [breakout_lab_at (by rw [hlsz]; exact hinj) hto i]
    rcases Decidable.em (i < tc) with h1 | h1
    · rw [ite_eq_left h1]
      exact hlab i hi
    · rcases Decidable.em (i = tc) with heq2 | h2
      · rw [ite_eq_right h1, ite_eq_left heq2]
        exact hlab _ (by omega)
      · rcases Decidable.em (i ≤ tc + o) with h3 | h3
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
          exact hlab _ (by omega)
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
          exact hlab i hi
  · rw [Array.size_set! _ _ _, hpsz]
  · rw [insert, Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) htcn
  · rw [Array.size_set! _ _ _]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  · have h := labInj_breakout (lab := lab) (ptn := ptn)
      (level := level) (tc := tc) (o := o)
      (by rw [hlsz]; exact hinj) hto
    rw [hlsz] at h
    exact h
  · intro v hv
    rw [elem_single] at hv
    have hvtc : v = tc := of_decide_eq_true hv
    rw [hvtc]
    rcases Decidable.em (tc = 0) with h00 | h00
    · exact Or.inl h00
    · rcases hstart with h0 | hcl
      · exact Or.inl h0
      · refine Or.inr ?_
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
  · rw [bcount_breakout_eq hvals hopen (by omega) ctx.n
      (Nat.le_refl _), ite_eq_left htcn, hacc]
  · exact certInv_breakout hlsz hpsz hend hvals hinj hcell hne ho hE

end Package

/-! # The guard's cell-size consequences

In the first branch of `cheapautom`'s guard the defect is at most the
nontrivial cell count plus one, which forces every nontrivial cell to
a pair except at most one triple; in particular every non-pair cell
has odd size, the `hOdd` hypothesis of the flip theorem. -/

section Sizes

variable {ptn : Array Nat} {level nn : Nat}

private theorem sum_excess_ge_countP :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) →
      ((l.map fun p => p.2 - p.1).sum ≥
        l.countP fun p => decide (p.1 < p.2))
  | [], _ => by simp
  | a :: l, hwf => by
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    have ih := sum_excess_ge_countP l
      fun p hp => hwf p (List.mem_cons_of_mem _ hp)
    rcases Decidable.em (a.1 < a.2) with h | h
    · rw [ite_eq_left (decide_eq_true h)]
      omega
    · rw [ite_eq_right (by simpa using h)]
      omega

private theorem sum_excess_ge_countP_add {q : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) → q ∈ l →
      ((l.map fun p => p.2 - p.1).sum ≥
        (l.countP fun p => decide (p.1 < p.2)) + (q.2 - q.1) - 1)
  | [], _, hq => absurd hq (by simp)
  | a :: l, hwf, hq => by
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    rcases List.mem_cons.mp hq with rfl | hmem
    · have ih := sum_excess_ge_countP l
        fun p hp => hwf p (List.mem_cons_of_mem _ hp)
      rcases Decidable.em (q.1 < q.2) with h | h
      · rw [ite_eq_left (decide_eq_true h)]
        omega
      · rw [ite_eq_right (by simpa using h)]
        omega
    · have ih := sum_excess_ge_countP_add l
        (fun p hp => hwf p (List.mem_cons_of_mem _ hp)) hmem
      have ha := hwf a List.mem_cons_self
      rcases Decidable.em (a.1 < a.2) with h | h
      · rw [ite_eq_left (decide_eq_true h)]
        omega
      · rw [ite_eq_right (by simpa using h)]
        omega

private theorem sum_sizes_split :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) →
      (l.map fun p => p.2 + 1 - p.1).sum =
        (l.map fun p => p.2 - p.1).sum + l.length
  | [], _ => rfl
  | a :: l, hwf => by
    rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons,
      List.length_cons,
      sum_sizes_split l fun p hp => hwf p (List.mem_cons_of_mem _ hp)]
    have := hwf a List.mem_cons_self
    omega

/-- The first guard branch forces non-pair cells to odd size: every
nontrivial cell is a pair except at most one triple. -/
theorem hOdd_of_defect_le
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1 := by
  intro q hq hnp
  have hwf : ∀ p ∈ cells ptn level nn, p.1 ≤ p.2 :=
    fun p hp => cells_le p hp
  have hsum : ((cells ptn level nn).map fun p =>
      p.2 + 1 - p.1).sum = nn := by
    rw [cells]
    have h := cells_go_sizes_sum hps hend nn 0 (by omega)
    rw [show nn - 0 = nn by omega] at h
    exact h
  have hsplit := sum_sizes_split (cells ptn level nn) hwf
  have hmem := sum_excess_ge_countP_add (cells ptn level nn) hwf hq
  have hq12 := hwf q hq
  rcases Decidable.em (q.2 = q.1) with heq | hne2
  · rw [heq]
    omega
  · have hge3 : q.1 + 2 ≤ q.2 := by omega
    have hle3 : q.2 ≤ q.1 + 2 := by omega
    rw [show q.2 + 1 - q.1 = 3 by omega]

end Sizes

end Descent

/-! # The flip as a renaming

The branch step transports one child's refinement to the other's
through `refine_map`, which consumes a `Renaming` and a `RowsMap`.
A bounded involution extends by the identity beyond the vertex range
to a renaming, and `flip_rows`'s conclusion is exactly the rows-map
fact for it. -/

/-- A bounded involution, extended by the identity beyond the vertex
range, as a renaming. -/
@[expose] def renamingOfFlip (f : Nat → Nat) (n : Nat)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v) : Renaming n where
  toFun v := if v < n then f v else v
  inj a b hab := by
    rcases Decidable.em (a < n) with ha | ha <;>
      rcases Decidable.em (b < n) with hb | hb
    · rw [ite_eq_left ha, ite_eq_left hb] at hab
      have h2 := congrArg f hab
      rw [hinvol a ha, hinvol b hb] at h2
      exact h2
    · rw [ite_eq_left ha, ite_eq_right hb] at hab
      exact absurd (hfb a ha) (by omega)
    · rw [ite_eq_right ha, ite_eq_left hb] at hab
      exact absurd (hfb b hb) (by omega)
    · rw [ite_eq_right ha, ite_eq_right hb] at hab
      exact hab
  maps v := by
    rcases Decidable.em (v < n) with h | h
    · rw [ite_eq_left h]
      exact ⟨fun _ => hfb v h, fun _ => h⟩
    · rw [ite_eq_right h]

/-- The extended flip agrees with the flip on vertices. -/
theorem renamingOfFlip_at {f : Nat → Nat} {n : Nat}
    (hfb : ∀ v, v < n → f v < n) (hinvol : ∀ v, v < n → f (f v) = v)
    {v : Nat} (hv : v < n) :
    renamingOfFlip f n hfb hinvol v = f v := by
  show (if v < n then f v else v) = f v
  rw [ite_eq_left hv]

/-- The involution of the flip extends to the renaming. -/
theorem renamingOfFlip_invol {f : Nat → Nat} {n : Nat}
    (hfb : ∀ v, v < n → f v < n) (hinvol : ∀ v, v < n → f (f v) = v)
    {v : Nat} (hv : v < n) :
    renamingOfFlip f n hfb hinvol (renamingOfFlip f n hfb hinvol v) =
      v := by
  rw [renamingOfFlip_at hfb hinvol hv,
    renamingOfFlip_at hfb hinvol (hfb v hv)]
  exact hinvol v hv

/-- A row-preserving flip names a rows map of the graph onto
itself: the packaging of `flip_rows`'s conclusion that `refine_map`
consumes. -/
theorem rowsMap_of_flip_rows {f : Nat → Nat}
    (hgsz : ctx.g.size = ctx.n)
    (hfb : ∀ v, v < ctx.n → f v < ctx.n)
    (hinvol : ∀ v, v < ctx.n → f (f v) = v)
    (hrows : ∀ v, v < ctx.n → ctx.g[f v]! = image f ctx.n ctx.g[v]!) :
    RowsMap (renamingOfFlip f ctx.n hfb hinvol) ctx.g ctx.g := by
  refine ⟨hgsz, hgsz, fun v hv => ?_⟩
  rw [renamingOfFlip_at hfb hinvol hv, hrows v hv]
  exact image_congr _ fun w hw =>
    (renamingOfFlip_at hfb hinvol hw).symm

/-! # Maximal runs and the cell list

`cellsPerm` quantifies over `IsCell` runs; the branch-step
classification works on the `cells` list. The conversion: an in-range
maximal run is a member of the list, a run beyond the array bound is a
phantom singleton, and no run crosses the bound. -/

/-- Reads beyond the array bound default. -/
private theorem getElem!_oob {arr : Array Nat} {q : Nat}
    (h : arr.size ≤ q) : arr[q]! = 0 := by
  rw [Array.getElem!_eq_getD, Array.getD]
  split
  · omega
  · rfl

/-- A maximal run's end from its start is what `cellEnd` computes. -/
theorem cellEnd_of_isCell_start {ptn : Array Nat} {level a len : Nat}
    (h : IsCell ptn level a len) (hin : a + len - 1 < ptn.size) :
    cellEnd ptn level a = a + len - 1 := by
  obtain ⟨hpos, -, hint, hcend⟩ := h
  rw [cellEnd]
  exact cellEnd_go_unique _ a (a + len - 1) (by omega)
    (fun i h1 h2 => hint i h1 (by omega)) hcend (by omega)

/-- An in-range maximal run is a cell of the partition list. -/
theorem mem_cells_of_isCell {ptn : Array Nat} {level nn a len : Nat}
    (hnn : nn ≤ ptn.size) (hpe : ptn[ptn.size - 1]! ≤ level)
    (h : IsCell ptn level a len) (ha : a < nn)
    (hlen : a + len ≤ ptn.size) :
    (a, a + len - 1) ∈ cells ptn level nn := by
  rw [mem_cells_iff hnn hpe]
  have hpos := h.1
  exact ⟨ha, h.2.1, (cellEnd_of_isCell_start h (by omega)).symm⟩

/-- A maximal run beyond the array bound is a singleton. -/
theorem isCell_oob {ptn : Array Nat} {level a len : Nat}
    (h : IsCell ptn level a len) (ha : ptn.size ≤ a) : len = 1 := by
  obtain ⟨hpos, -, hint, -⟩ := h
  rcases Decidable.em (len = 1) with h1 | h1
  · exact h1
  · exfalso
    have hop := hint a (Nat.le_refl _) (by omega)
    rw [getElem!_oob ha] at hop
    omega

/-- No maximal run crosses the array bound. -/
theorem isCell_no_cross {ptn : Array Nat} {level a len : Nat}
    (hpe : ptn[ptn.size - 1]! ≤ level)
    (h : IsCell ptn level a len) (ha : a < ptn.size) :
    a + len ≤ ptn.size := by
  obtain ⟨hpos, -, hint, -⟩ := h
  rcases Decidable.em (a + len ≤ ptn.size) with hle | hgt
  · exact hle
  · exfalso
    have hop := hint (ptn.size - 1) (by omega) (by omega)
    omega

/-! # The branch step: the two children of a pair target

Individualizing either member of a pair target cell produces, before
refinement, labellings that agree as cell contents of the split
partition after composing the first child with the flip of the pair's
matching component. -/

section Branch

variable {lab ptn : Array Nat} {level tc : Nat} {S : Nat → Prop}
  {f : Nat → Nat}

/-- The rotated labelling keeps every entry a vertex. -/
theorem labOk_breakout {o n' : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size)
    (hlab : LabOk lab n') :
    LabOk (breakout lab ptn (level + 1) tc lab[tc + o]!).1 n' := by
  intro i hi
  rw [breakout_lab_size] at hi
  rw [breakout_lab_at hinj hto i]
  rcases Decidable.em (i < tc) with h1 | h1
  · rw [ite_eq_left h1]
    exact hlab i hi
  · rcases Decidable.em (i = tc) with heq2 | h2
    · rw [ite_eq_right h1, ite_eq_left heq2]
      exact hlab _ hto
    · rcases Decidable.em (i ≤ tc + o) with h3 | h3
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
        exact hlab _ (by omega)
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
        exact hlab i hi

/-- Segments of a mapped array are mapped segments. -/
private theorem segN_map {arr : Array Nat} {g : Nat → Nat}
    {lo len : Nat} (h : lo + len ≤ arr.size) :
    segN (arr.map g) lo len = (segN arr lo len).map g := by
  rw [segN, segN, List.map_map]
  exact List.map_congr_left fun o ho => by
    have hor := List.mem_range.mp ho
    show (arr.map g)[lo + o]! = g arr[lo + o]!
    exact getElem!_map_of_lt g arr (by omega)

/-- The second child's labelling is the first child's composed with a
target-swapping flip, as cell contents of the split partition. -/
theorem branch_cellsPerm
    (hpsz : ptn.size = ctx.n) (hlsz : lab.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (hlab : LabOk lab ctx.n) (hinj : LabInj lab ctx.n)
    (hfb : ∀ v, v < ctx.n → f v < ctx.n)
    (hinvol : ∀ v, v < ctx.n → f (f v) = v)
    (hcell : (tc, tc + 1) ∈ cells ptn level ctx.n)
    (hStc : S tc)
    (hSpair : ∀ p ∈ cells ptn level ctx.n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells ptn level ctx.n, S p.1 →
      f lab[p.1]! = lab[p.1 + 1]! ∧ f lab[p.1 + 1]! = lab[p.1]!)
    (hSfix : ∀ p ∈ cells ptn level ctx.n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 → f lab[p.1 + o]! = lab[p.1 + o]!) :
    cellsPerm (ptn.set! tc (level + 1)) (level + 1)
      (breakout lab ptn (level + 1) tc lab[tc + 1]!).1
      (((breakout lab ptn (level + 1) tc lab[tc + 0]!).1).map
        (renamingOfFlip f ctx.n hfb hinvol).toFun) := by
  intro a len hIs
  have hn0 : 0 < ctx.n := by
    obtain ⟨h1, -, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
    omega
  have htc1 : tc + 1 < ctx.n := target_end_lt hpsz hend hcell
  have hinj' : LabInj lab lab.size := by rw [hlsz]; exact hinj
  have hto1 : tc + 1 < lab.size := by omega
  have hto0 : tc + 0 < lab.size := by omega
  have hVat := breakout_lab_at (o := 1) (ptn := ptn) (level := level)
    hinj' hto1
  have hUat := breakout_lab_at (o := 0) (ptn := ptn) (level := level)
    hinj' hto0
  have hVsz : (breakout lab ptn (level + 1) tc
      lab[tc + 1]!).1.size = ctx.n := by
    rw [breakout_lab_size, hlsz]
  have hUsz : (breakout lab ptn (level + 1) tc
      lab[tc + 0]!).1.size = ctx.n := by
    rw [breakout_lab_size, hlsz]
  have hsz' : (ptn.set! tc (level + 1)).size = ctx.n := by
    rw [Array.size_set!, hpsz]
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz', ← hpsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  have hσat : ∀ w, w < ctx.n →
      (renamingOfFlip f ctx.n hfb hinvol).toFun w = f w :=
    fun w hw => renamingOfFlip_at hfb hinvol hw
  rcases Decidable.em (a < ctx.n) with han | han
  · -- in range: classify against the split partition's cell list
    have hcross : a + len ≤ ctx.n := by
      have := isCell_no_cross hend' hIs (by omega)
      omega
    have hmem : (a, a + len - 1) ∈
        cells (ptn.set! tc (level + 1)) (level + 1) ctx.n :=
      mem_cells_of_isCell (by omega) hend' hIs han (by omega)
    have hpos := hIs.1
    have hcases := child_cells_cases hpsz hend hvals hcell
      (by omega) hmem
    have hswapT : f lab[tc]! = lab[tc + 1]! ∧
        f lab[tc + 1]! = lab[tc]! := hSswap (tc, tc + 1) hcell hStc
    rcases hcases with heq | heq | ⟨hmemP, hane⟩
    · -- the split-off singleton
      have h1 : a = tc := congrArg Prod.fst heq
      have h2 : a + len - 1 = tc := congrArg Prod.snd heq
      have hlen1 : len = 1 := by omega
      subst h1
      rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero]
      rw [hVat a, ite_eq_right (by omega), ite_eq_left rfl]
      rw [getElem!_map_of_lt _ _ (by rw [hUsz]; omega), hUat a,
        ite_eq_right (by omega), ite_eq_left rfl,
        hσat _ (hlab _ (by rw [hlsz]; omega))]
      simp only [Nat.add_zero]
      rw [hswapT.1]
    · -- the remainder singleton
      have h1 : a = tc + 1 := congrArg Prod.fst heq
      have h2 : a + len - 1 = tc + 1 := congrArg Prod.snd heq
      have hlen1 : len = 1 := by omega
      subst h1
      rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero]
      rw [hVat (tc + 1), ite_eq_right (by omega),
        ite_eq_right (by omega), ite_eq_left (by omega),
        show tc + 1 - 1 = tc by omega]
      rw [getElem!_map_of_lt _ _ (by rw [hUsz]; omega), hUat (tc + 1),
        ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega),
        hσat _ (hlab _ (by rw [hlsz]; omega))]
      rw [hswapT.2]
    · -- an untouched parent cell
      have hIsA : IsCell ptn level a len := by
        have h := cells_isCell (by omega) hend _ hmemP
        rw [show a + len - 1 + 1 - a = len by omega] at h
        exact h
      have hIsT : IsCell ptn level tc 2 := by
        have h := cells_isCell (by omega) hend _ hcell
        rw [show tc + 1 + 1 - tc = 2 by omega] at h
        exact h
      have hdisj : a + len ≤ tc ∨ tc + 2 ≤ a := by
        rcases isCell_disj_or_eq hIsA hIsT with ⟨h1, -⟩ | h | h
        · exact absurd h1 hane
        · exact Or.inl h
        · exact Or.inr h
      have hVeq : ∀ o, o < len →
          (breakout lab ptn (level + 1) tc
            lab[tc + 1]!).1[a + o]! = lab[a + o]! := by
        intro o ho
        rw [hVat (a + o)]
        rcases hdisj with hd | hd
        · rw [ite_eq_left (by omega)]
        · rw [ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega)]
      have hUeq : ∀ o, o < len →
          (breakout lab ptn (level + 1) tc
            lab[tc + 0]!).1[a + o]! = lab[a + o]! := by
        intro o ho
        rw [hUat (a + o)]
        rcases hdisj with hd | hd
        · rw [ite_eq_left (by omega)]
        · rw [ite_eq_right (by omega), ite_eq_right (by omega),
            ite_eq_right (by omega)]
      have hMeq : ∀ o, o < len →
          ((breakout lab ptn (level + 1) tc
            lab[tc + 0]!).1.map
              (renamingOfFlip f ctx.n hfb hinvol).toFun)[a + o]! =
            f lab[a + o]! := by
        intro o ho
        rw [getElem!_map_of_lt _ _ (by rw [hUsz]; omega), hUeq o ho,
          hσat _ (hlab _ (by rw [hlsz]; omega))]
      rcases Classical.em (S a) with hSa | hSa
      · -- a flipped pair: the segment swaps
        have hpair := hSpair (a, a + len - 1) hmemP hSa
        have hlen2 : len = 2 := by
          have : a + len - 1 = a + 1 := hpair
          omega
        have hswapA : f lab[a]! = lab[a + 1]! ∧
            f lab[a + 1]! = lab[a]! := hSswap (a, a + 1) (by
          rw [show ((a : Nat), a + 1) = (a, a + len - 1) by
            rw [Prod.mk.injEq]
            omega]
          exact hmemP) hSa
        subst hlen2
        have hV0 : (breakout lab ptn (level + 1) tc
            lab[tc + 1]!).1[a]! = lab[a]! := hVeq 0 (by omega)
        have hM0 : ((breakout lab ptn (level + 1) tc
            lab[tc + 0]!).1.map
              (renamingOfFlip f ctx.n hfb hinvol).toFun)[a]! =
            f lab[a]! := hMeq 0 (by omega)
        rw [segN_cons, segN_cons, segN_zero, segN_cons, segN_cons,
          segN_zero]
        rw [hV0, hVeq 1 (by omega), hM0, hMeq 1 (by omega),
          hswapA.1, hswapA.2]
        exact List.Perm.swap _ _ _
      · -- a fixed cell: the segments agree
        have hfix := hSfix (a, a + len - 1) hmemP hSa
        rw [show a + len - 1 + 1 - a = len by omega] at hfix
        have hfix' : ∀ o, o < len → f lab[a + o]! = lab[a + o]! :=
          hfix
        have hVs : segN (breakout lab ptn (level + 1) tc
            lab[tc + 1]!).1 a len = segN lab a len :=
          segN_congr fun o ho => hVeq o ho
        have hMs : segN ((breakout lab ptn (level + 1) tc
            lab[tc + 0]!).1.map
              (renamingOfFlip f ctx.n hfb hinvol).toFun) a len =
            segN lab a len :=
          segN_congr fun o ho => (hMeq o ho).trans (hfix' o ho)
        rw [hVs, hMs]
  · -- beyond the bound: phantom singletons default on both sides
    have hlen1 : len = 1 := isCell_oob hIs (by omega)
    rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero]
    rw [getElem!_oob (by omega : (breakout lab ptn (level + 1) tc
        lab[tc + 1]!).1.size ≤ a)]
    rw [getElem!_oob (by
      rw [Array.size_map]
      omega : ((breakout lab ptn (level + 1) tc
        lab[tc + 0]!).1.map
          (renamingOfFlip f ctx.n hfb hinvol).toFun).size ≤ a)]

/-- The branch step: the two children of a pair target cell refine to
states with identical position-level fields whose labellings agree as
cell contents after composing the first child with the flip. -/
theorem branch_step {numcells : Nat}
    (hgsz : ctx.g.size = ctx.n)
    (hpsz : ptn.size = ctx.n) (hlsz : lab.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (hlab : LabOk lab ctx.n) (hinj : LabInj lab ctx.n)
    (hfb : ∀ v, v < ctx.n → f v < ctx.n)
    (hinvol : ∀ v, v < ctx.n → f (f v) = v)
    (hrows : ∀ v, v < ctx.n → ctx.g[f v]! = image f ctx.n ctx.g[v]!)
    (hcell : (tc, tc + 1) ∈ cells ptn level ctx.n)
    (hStc : S tc)
    (hSpair : ∀ p ∈ cells ptn level ctx.n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells ptn level ctx.n, S p.1 →
      f lab[p.1]! = lab[p.1 + 1]! ∧ f lab[p.1 + 1]! = lab[p.1]!)
    (hSfix : ∀ p ∈ cells ptn level ctx.n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 → f lab[p.1 + o]! = lab[p.1 + o]!) :
    StPerm (level + 1)
      (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + 1]!).1
        (ptn.set! tc (level + 1)) (insert 0 tc) (numcells + 1))
      (mapSt (renamingOfFlip f ctx.n hfb hinvol)
        (refine ctx (level + 1)
          (breakout lab ptn (level + 1) tc lab[tc + 0]!).1
          (ptn.set! tc (level + 1)) (insert 0 tc)
          (numcells + 1))) := by
  have htc1 : tc + 1 < ctx.n := target_end_lt hpsz hend hcell
  have hinj' : LabInj lab lab.size := by rw [hlsz]; exact hinj
  have hto1 : tc + 1 < lab.size := by omega
  have hto0 : tc + 0 < lab.size := by omega
  have hVsz : (breakout lab ptn (level + 1) tc
      lab[tc + 1]!).1.size = ctx.n := by
    rw [breakout_lab_size, hlsz]
  have hUsz : (breakout lab ptn (level + 1) tc
      lab[tc + 0]!).1.size = ctx.n := by
    rw [breakout_lab_size, hlsz]
  have hVok : LabOk (breakout lab ptn (level + 1) tc
      lab[tc + 1]!).1 ctx.n := labOk_breakout hinj' hto1 hlab
  have hUok : LabOk (breakout lab ptn (level + 1) tc
      lab[tc + 0]!).1 ctx.n := labOk_breakout hinj' hto0 hlab
  have hsz' : (ptn.set! tc (level + 1)).size = ctx.n := by
    rw [Array.size_set!, hpsz]
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz', ← hpsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  have hact : insert 0 tc < 2 ^ ctx.n := by
    rw [insert, Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hstarts : ∀ v : Nat, elem (insert 0 tc) v = true →
      v = 0 ∨ (ptn.set! tc (level + 1))[v - 1]! ≤ level + 1 := by
    intro v hv
    rw [elem_single] at hv
    have hvtc : v = tc := of_decide_eq_true hv
    subst hvtc
    obtain ⟨-, hstart, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
    rcases Decidable.em (v = 0) with h00 | h00
    · exact Or.inl h00
    · rcases hstart with h0 | hcl
      · exact Or.inl h0
      · refine Or.inr ?_
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
  have hcp := branch_cellsPerm hpsz hlsz hend hvals hlab hinj hfb
    hinvol hcell hStc hSpair hSswap hSfix
  have h1 := refine_perm (hn := rfl) hcp
    (by rw [Array.size_map, hUsz, hVsz])
    hVsz hVok hsz' hact hend' hstarts
    (numcells := numcells + 1)
  have h2 := refine_map (renamingOfFlip f ctx.n hfb hinvol) rfl rfl
    (rowsMap_of_flip_rows hgsz hfb hinvol hrows) (level + 1)
    (breakout lab ptn (level + 1) tc lab[tc + 0]!).1
    (ptn.set! tc (level + 1)) (insert 0 tc) (numcells + 1)
    hUsz hUok hsz' hact hend'
  rw [h2] at h1
  exact h1

/-- Arrays with equal sizes and equal defaulted reads are equal. -/
private theorem array_eq_of_getElem! {a b : Array Nat}
    (hsz : a.size = b.size)
    (h : ∀ q, q < a.size → a[q]! = b[q]!) : a = b := by
  refine Array.ext hsz fun i hi hib => ?_
  have hq := h i hi
  rwa [getElem!_pos a i hi, getElem!_pos b i hib] at hq

/-- At a discrete partition, cell-content agreement is pointwise
agreement: the labellings of a `StPerm` pair coincide. -/
theorem stPerm_lab_eq {level : Nat} {st st' : RefineSt}
    (h : StPerm level st st')
    (hdisc : ∀ q, q < st.ptn.size → st.ptn[q]! ≤ level)
    (hsz : st.lab.size = st.ptn.size) : st'.lab = st.lab := by
  refine array_eq_of_getElem! (by rw [h.labSize]) fun q hq => ?_
  rw [h.labSize] at hq
  have hc : IsCell st.ptn level q 1 := by
    refine ⟨by omega, ?_, by omega, ?_⟩
    · rcases Decidable.em (q = 0) with h0 | h0
      · exact Or.inl h0
      · exact Or.inr (hdisc (q - 1) (by omega))
    · rw [show q + 1 - 1 = q by omega]
      exact hdisc q (by omega)
  exact (cellsPerm_singleton h.cells hc).symm

/-- The leaf collapse: when the second child's refinement is discrete,
the two children's leaf rows coincide -- the flip is absorbed by
`leafRows_map`. -/
theorem branch_leafRows {numcells : Nat}
    (hgsz : ctx.g.size = ctx.n)
    (hpsz : ptn.size = ctx.n) (hlsz : lab.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (hlab : LabOk lab ctx.n) (hinj : LabInj lab ctx.n)
    (hfb : ∀ v, v < ctx.n → f v < ctx.n)
    (hinvol : ∀ v, v < ctx.n → f (f v) = v)
    (hrows : ∀ v, v < ctx.n → ctx.g[f v]! = image f ctx.n ctx.g[v]!)
    (hcell : (tc, tc + 1) ∈ cells ptn level ctx.n)
    (hStc : S tc)
    (hSpair : ∀ p ∈ cells ptn level ctx.n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells ptn level ctx.n, S p.1 →
      f lab[p.1]! = lab[p.1 + 1]! ∧ f lab[p.1 + 1]! = lab[p.1]!)
    (hSfix : ∀ p ∈ cells ptn level ctx.n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 → f lab[p.1 + o]! = lab[p.1 + o]!)
    (hdisc : ∀ q, q < ctx.n →
      (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + 1]!).1
        (ptn.set! tc (level + 1)) (insert 0 tc)
        (numcells + 1)).ptn[q]! ≤ level + 1) :
    leafRows ctx (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + 1]!).1
        (ptn.set! tc (level + 1)) (insert 0 tc)
        (numcells + 1)).lab =
      leafRows ctx (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + 0]!).1
        (ptn.set! tc (level + 1)) (insert 0 tc)
        (numcells + 1)).lab := by
  have htc1 : tc + 1 < ctx.n := target_end_lt hpsz hend hcell
  have hinj' : LabInj lab lab.size := by rw [hlsz]; exact hinj
  have hVsz : (breakout lab ptn (level + 1) tc
      lab[tc + 1]!).1.size = ctx.n := by
    rw [breakout_lab_size, hlsz]
  have hUsz : (breakout lab ptn (level + 1) tc
      lab[tc + 0]!).1.size = ctx.n := by
    rw [breakout_lab_size, hlsz]
  have hVok : LabOk (breakout lab ptn (level + 1) tc
      lab[tc + 1]!).1 ctx.n := labOk_breakout hinj' (by omega) hlab
  have hUok : LabOk (breakout lab ptn (level + 1) tc
      lab[tc + 0]!).1 ctx.n := labOk_breakout hinj' (by omega) hlab
  have hsz' : (ptn.set! tc (level + 1)).size = ctx.n := by
    rw [Array.size_set!, hpsz]
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz', ← hpsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  have hact : insert 0 tc < 2 ^ ctx.n := by
    rw [insert, Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) (by omega)
  have hVstOk := refine_stOk (hn := rfl) hVsz hVok hsz' hact hend'
    (numcells := numcells + 1)
  have hUstOk := refine_stOk (hn := rfl) hUsz hUok hsz' hact hend'
    (numcells := numcells + 1)
  have hstep := branch_step (S := S) hgsz hpsz hlsz hend hvals hlab
    hinj hfb hinvol hrows hcell hStc hSpair hSswap hSfix
    (numcells := numcells)
  have hlabeq := stPerm_lab_eq hstep
    (by
      intro q hq
      rw [hVstOk.ptnSize] at hq
      exact hdisc q hq)
    (by rw [hVstOk.labSize, hVstOk.ptnSize])
  have hlabeq' : (refine ctx (level + 1)
      (breakout lab ptn (level + 1) tc lab[tc + 1]!).1
      (ptn.set! tc (level + 1)) (insert 0 tc)
      (numcells + 1)).lab =
    (refine ctx (level + 1)
      (breakout lab ptn (level + 1) tc lab[tc + 0]!).1
      (ptn.set! tc (level + 1)) (insert 0 tc)
      (numcells + 1)).lab.map
        (renamingOfFlip f ctx.n hfb hinvol).toFun := hlabeq.symm
  rw [hlabeq']
  exact leafRows_map (renamingOfFlip f ctx.n hfb hinvol) rfl rfl
    (rowsMap_of_flip_rows hgsz hfb hinvol hrows)
    hUstOk.labOk hUstOk.labSize

end Branch

end Hex.GraphIso.Nauty

