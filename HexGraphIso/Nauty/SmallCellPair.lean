/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellTriple
import all HexGraphIso.Nauty.Equitable

public section

/-!
The pair-closure involution (SPEC § Verified search refinement, the
code-1 arm of the store-validity obligation).

The pair deviation swaps every pair cell in the `PairMatch`-reachability
closure of the target pair at once. This file constructs that involution
(`pairFlip`: a member of a closure pair maps to its partner, every other
vertex is fixed — a `Classical.choose` over the closure, made
well-defined by the position toolkit's uniqueness facts), proves its
evaluation laws, bounds, and involutivity, and discharges the
`S`-hypotheses of `flip_rows` for it: closure pairs swap
(`pairFlip_first`/`pairFlip_second`), members of non-closure cells are
fixed (`pairFlip_fix_cell`), and the closure is `PairMatch`-closed by
construction (`PairReach.step`). The self-equivalence
(`cellsPerm_self_flip`, stated for any renaming swapping `S`-pairs and
fixing the other cells pointwise, so future flips reuse it) and the
packaged pair deviation (`pair_deviation_leafRows`, through
`deviation_leafRows_self` exactly as the triple instance) complete the
pair analogue of the triple theory.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-! # The involution -/

section PairFlip

open Classical

variable {lab ptn : Array Nat} {level t : Nat}

/-- The involution swapping every pair in the `PairReach` closure of
`t`: a vertex that is a member of a closure pair maps to its partner,
and every other vertex is fixed. -/
noncomputable def pairFlip (ctx : Ctx) (lab ptn : Array Nat)
    (level t : Nat) : Nat → Nat := fun v =>
  if h : ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level ctx.n ∧ v = lab[c]! then
    lab[h.choose + 1]!
  else if h : ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level ctx.n ∧ v = lab[c + 1]! then
    lab[h.choose]!
  else v

/-- Two closure pairs sharing a first member coincide. -/
private theorem first_eq (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab ctx.n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level ctx.n)
    (hcell' : (c', c' + 1) ∈ cells ptn level ctx.n)
    (hv : lab[c]! = lab[c']!) : c = c' := by
  have h1 := cells_bound (by omega) hend _ hcell
  have h2 := cells_bound (by omega) hend _ hcell'
  have h1' : c + 1 < ptn.size := h1
  have h2' : c' + 1 < ptn.size := h2
  exact hinj c c' (by omega) (by omega) hv

/-- Two closure pairs sharing a second member coincide. -/
private theorem second_eq (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab ctx.n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level ctx.n)
    (hcell' : (c', c' + 1) ∈ cells ptn level ctx.n)
    (hv : lab[c + 1]! = lab[c' + 1]!) : c = c' := by
  have h1 : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have h2 : (c', c' + 1).2 < ptn.size :=
    cells_bound (by omega) hend _ hcell'
  have := hinj (c + 1) (c' + 1) (by omega) (by omega) hv
  omega

/-- A first member of one pair cell is never the second member of
another. -/
private theorem first_ne_second (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab ctx.n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level ctx.n)
    (hcell' : (c', c' + 1) ∈ cells ptn level ctx.n)
    (hv : lab[c]! = lab[c' + 1]!) : False := by
  have h1 : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have h2 : (c', c' + 1).2 < ptn.size :=
    cells_bound (by omega) hend _ hcell'
  have heq := hinj c (c' + 1) (by omega) (by omega) hv
  exact pair_start_ne_second (by omega) hend hcell hcell' heq

/-- The flip carries a closure pair's first member to its second. -/
theorem pairFlip_first (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab ctx.n)
    {c : Nat} (hr : PairReach ctx lab ptn level t c)
    (hcell : (c, c + 1) ∈ cells ptn level ctx.n) :
    pairFlip ctx lab ptn level t lab[c]! = lab[c + 1]! := by
  have hex : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level ctx.n ∧ lab[c]! = lab[c']! :=
    ⟨c, hr, hcell, rfl⟩
  obtain ⟨-, hcell', hv⟩ := hex.choose_spec
  have hcc : hex.choose = c :=
    (first_eq hpsz hend hinj hcell hcell' hv).symm
  show (if h : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level ctx.n ∧ lab[c]! = lab[c']! then
      lab[h.choose + 1]!
    else _) = _
  rw [dite_eq_left hex]
  show lab[hex.choose + 1]! = lab[c + 1]!
  rw [hcc]

/-- The flip carries a closure pair's second member to its first. -/
theorem pairFlip_second (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab ctx.n)
    {c : Nat} (hr : PairReach ctx lab ptn level t c)
    (hcell : (c, c + 1) ∈ cells ptn level ctx.n) :
    pairFlip ctx lab ptn level t lab[c + 1]! = lab[c]! := by
  have hno : ¬ ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level ctx.n ∧
        lab[c + 1]! = lab[c']! := by
    rintro ⟨c', -, hcell', hv⟩
    exact first_ne_second hpsz hend hinj hcell' hcell hv.symm
  have hex : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level ctx.n ∧
        lab[c + 1]! = lab[c' + 1]! :=
    ⟨c, hr, hcell, rfl⟩
  obtain ⟨-, hcell', hv⟩ := hex.choose_spec
  have hcc : hex.choose = c :=
    (second_eq hpsz hend hinj hcell hcell' hv).symm
  show (if _ : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level ctx.n ∧
        lab[c + 1]! = lab[c']! then _
    else if h : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level ctx.n ∧
        lab[c + 1]! = lab[c' + 1]! then lab[h.choose]!
    else _) = _
  rw [dite_eq_right hno, dite_eq_left hex]
  show lab[hex.choose]! = lab[c]!
  rw [hcc]

/-- The flip fixes every vertex that is not a closure-pair member. -/
theorem pairFlip_fix {v : Nat}
    (hnone : ∀ c, PairReach ctx lab ptn level t c →
      (c, c + 1) ∈ cells ptn level ctx.n →
        v ≠ lab[c]! ∧ v ≠ lab[c + 1]!) :
    pairFlip ctx lab ptn level t v = v := by
  have h1 : ¬ ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level ctx.n ∧ v = lab[c]! := by
    rintro ⟨c, hr, hcell, hv⟩
    exact (hnone c hr hcell).1 hv
  have h2 : ¬ ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level ctx.n ∧ v = lab[c + 1]! := by
    rintro ⟨c, hr, hcell, hv⟩
    exact (hnone c hr hcell).2 hv
  show (if _ : _ then _ else if _ : _ then _ else v) = v
  rw [dite_eq_right h1, dite_eq_right h2]

/-- The flip is bounded on the vertex range. -/
theorem pairFlip_lt (hpsz : ptn.size = ctx.n)
    (hlsz : lab.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hlb : LabOk lab ctx.n)
    {v : Nat} (hv : v < ctx.n) :
    pairFlip ctx lab ptn level t v < ctx.n := by
  show (if _ : _ then _ else if _ : _ then _ else v) < ctx.n
  split
  · next h =>
    obtain ⟨-, hcell, -⟩ := h.choose_spec
    have hb : (h.choose, h.choose + 1).2 < ptn.size :=
      cells_bound (by omega) hend _ hcell
    exact hlb _ (by rw [hlsz]; omega)
  · split
    · next h =>
      obtain ⟨-, hcell, -⟩ := h.choose_spec
      have hb : (h.choose, h.choose + 1).2 < ptn.size :=
        cells_bound (by omega) hend _ hcell
      exact hlb _ (by rw [hlsz]; omega)
    · exact hv

/-- The flip is an involution on the vertex range. -/
theorem pairFlip_invol (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab ctx.n)
    {v : Nat} :
    pairFlip ctx lab ptn level t
      (pairFlip ctx lab ptn level t v) = v := by
  rcases Decidable.em (∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level ctx.n ∧ v = lab[c]!) with h1 | h1
  · obtain ⟨c, hr, hcell, rfl⟩ := h1
    rw [pairFlip_first hpsz hend hinj hr hcell,
      pairFlip_second hpsz hend hinj hr hcell]
  · rcases Decidable.em (∃ c, PairReach ctx lab ptn level t c ∧
        (c, c + 1) ∈ cells ptn level ctx.n ∧ v = lab[c + 1]!) with
      h2 | h2
    · obtain ⟨c, hr, hcell, rfl⟩ := h2
      rw [pairFlip_second hpsz hend hinj hr hcell,
        pairFlip_first hpsz hend hinj hr hcell]
    · have hfix : pairFlip ctx lab ptn level t v = v := by
        refine pairFlip_fix fun c hr hcell => ⟨?_, ?_⟩
        · intro hcon
          exact h1 ⟨c, hr, hcell, hcon⟩
        · intro hcon
          exact h2 ⟨c, hr, hcell, hcon⟩
      rw [hfix, hfix]

/-- A member of a cell outside the closure is fixed by the flip: its
position would otherwise sit inside a closure pair's window. -/
theorem pairFlip_fix_cell (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab ctx.n)
    {q : Nat × Nat} (hq : q ∈ cells ptn level ctx.n)
    (hnotS : ¬ PairReach ctx lab ptn level t q.1)
    {o : Nat} (ho : o < q.2 + 1 - q.1) :
    pairFlip ctx lab ptn level t lab[q.1 + o]! = lab[q.1 + o]! := by
  have hqbd : q.2 < ptn.size := cells_bound (by omega) hend _ hq
  have hqle := cells_le _ hq
  have hqIs := cells_isCell (by omega) hend _ hq
  refine pairFlip_fix fun c hr hcell => ?_
  have hcbd : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have hcIs := cells_isCell (by omega) hend _ hcell
  rw [show c + 1 + 1 - c = 2 by omega] at hcIs
  constructor
  · intro hcon
    have hpos : q.1 + o = c :=
      hinj (q.1 + o) c (by omega) (by omega) hcon
    rcases isCell_disj_or_eq hqIs hcIs with ⟨he1, he2⟩ | hd | hd
    · have he1' : q.1 = c := he1
      apply hnotS
      rw [he1']
      exact hr
    · omega
    · omega
  · intro hcon
    have hpos : q.1 + o = c + 1 :=
      hinj (q.1 + o) (c + 1) (by omega) (by omega) hcon
    rcases isCell_disj_or_eq hqIs hcIs with ⟨he1, he2⟩ | hd | hd
    · have he1' : q.1 = c := he1
      apply hnotS
      rw [he1']
      exact hr
    · omega
    · omega

end PairFlip

end Hex.GraphIso.Nauty
