/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellPair
import all HexGraphIso.Nauty.Equitable

public section

/-!
The all-leaves node invariant (SPEC § Verified search refinement, the
code-1 arm of the store-validity obligation).

Below a first-branch cheapautom node every deviation is a pair or
triple deviation, and both consume the same node facts: the iteration
invariant, equitability, an accurate boundary count, and the
first-branch shape (every cell a singleton, a pair, or one triple).
This file packages those as `SubtreeOk` and proves the invariant
descends through one individualize-and-refine step
(`subtreeOk_child`): the iteration invariant by `iterOk_child`,
equitability by `equitable_breakout`, the count by
`bcount_breakout_eq` + `refine_bcount`, and the shape by containment —
every child cell sits inside a cell of the split partition
(`childSt_cell_parent`, via `subcell_of_grow` and `refine_frozen`), so
sizes only shrink, and a child triple fills the unique parent triple's
window exactly, keeping it unique.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-- The first-branch shape: every cell is a singleton, a pair, or the
unique triple. -/
def SmallShape (ctx : Ctx) (level : Nat) (ptn : Array Nat) : Prop :=
  ∀ q ∈ cells ptn level ctx.n, q.2 + 1 - q.1 ≤ 2 ∨
    (q.2 + 1 - q.1 = 3 ∧
      ∀ q' ∈ cells ptn level ctx.n, q'.2 + 1 - q'.1 = 3 → q' = q)

/-- The facts every deviation below a first-branch cheapautom node
consumes, carried at each node of the subtree. -/
structure SubtreeOk (ctx : Ctx) (level : Nat) (st : RefineSt) :
    Prop where
  it : IterOk ctx level st
  eqt : Equitable ctx level st.lab st.ptn
  acc : bcount st.ptn level ctx.n = st.numcells
  small : SmallShape ctx level st.ptn

/-- Every cell of the child partition sits inside a cell of the split
partition: refinement only adds boundaries. -/
theorem childSt_cell_parent {st : RefineSt} {level tc e o : Nat}
    (hIt : IterOk ctx level st) (hlvl : level < ctx.n)
    (hcell : (tc, e) ∈ cells st.ptn level ctx.n) (hne : tc < e)
    (ho : o ≤ e - tc) :
    ∀ f ∈ cells (childSt ctx level st tc st.lab[tc + o]!).ptn
        (level + 1) ctx.n,
      ∃ q ∈ cells (st.ptn.set! tc (level + 1)) (level + 1) ctx.n,
        q.1 ≤ f.1 ∧ f.2 ≤ q.2 := by
  intro f hf
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hen : e < ctx.n := target_end_lt hpsz hend hcell
  have hIt' := iterOk_child hIt hlvl hcell hne ho
  have hcpsz := hIt'.ok.ptnSize
  have hcend := hIt'.ok.ptnEnd
  have hssz : (st.ptn.set! tc (level + 1)).size = ctx.n := by
    rw [Array.size_set!, hpsz]
  have hsend : (st.ptn.set! tc (level + 1))[(st.ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hssz]
    rcases Decidable.em (tc = ctx.n - 1) with rfl | hx
    · rw [← hpsz, Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [← hpsz, Array.getElem!_set!_ne _ _ _ _ (by rw [hpsz]; omega)]
      have : st.ptn[ctx.n - 1]! ≤ level := by
        rw [← hpsz]
        exact hend
      omega
  have hbsz : (breakout st.lab st.ptn (level + 1) tc
      st.lab[tc + o]!).1.size = (st.ptn.set! tc (level + 1)).size := by
    rw [breakout_lab_size, hlsz, hssz]
  have hfle := cells_le _ hf
  have hfbd : f.2 < (childSt ctx level st tc
      st.lab[tc + o]!).ptn.size :=
    cells_bound (by omega) hcend _ hf
  rw [hcpsz] at hfbd
  have hfIs := cells_isCell (by omega) hcend _ hf
  have hb : ∀ q : Nat, (st.ptn.set! tc (level + 1))[q]! ≤ level + 1 →
      (childSt ctx level st tc st.lab[tc + o]!).ptn[q]! ≤
        level + 1 := by
    intro q hq
    show (refine ctx (level + 1) _ _ _ _).ptn[q]! ≤ level + 1
    rw [refine_frozen (by rw [hssz]) hbsz hsend hq]
    exact hq
  obtain ⟨c, lenC, hcC, hcle, hcge⟩ := subcell_of_grow
    (ptn0 := st.ptn.set! tc (level + 1))
    (ptnP := (childSt ctx level st tc st.lab[tc + o]!).ptn)
    (by rw [hssz, hcpsz]) hfIs hsend hb (by rw [hssz]; omega)
    (by rw [hssz]; have := isCell_no_cross hcend hfIs (by omega);
        rw [hcpsz] at this; omega)
  have hlenC : 0 < lenC := hcC.1
  have hcbd : c + lenC ≤ (st.ptn.set! tc (level + 1)).size :=
    isCell_no_cross hsend hcC (by rw [hssz]; omega)
  refine ⟨(c, c + lenC - 1), mem_cells_of_isCell (by omega) hsend hcC
    (by rw [hssz] at hcbd; omega) hcbd, by omega, by omega⟩

/-- The first-branch shape descends to the child: sizes only shrink
under containment, and a child triple fills the unique parent triple's
window exactly. -/
theorem smallShape_child {st : RefineSt} {level tc e o : Nat}
    (hIt : IterOk ctx level st) (hlvl : level < ctx.n)
    (hcell : (tc, e) ∈ cells st.ptn level ctx.n) (hne : tc < e)
    (ho : o ≤ e - tc) (hsmall : SmallShape ctx level st.ptn) :
    SmallShape ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!).ptn := by
  have hpsz := hIt.ok.ptnSize
  have hend := hIt.ok.ptnEnd
  have hIt' := iterOk_child hIt hlvl hcell hne ho
  have hcend := hIt'.ok.ptnEnd
  have hcpsz := hIt'.ok.ptnSize
  -- the coordinates a child triple is forced to occupy
  have htri : ∀ f ∈ cells (childSt ctx level st tc
      st.lab[tc + o]!).ptn (level + 1) ctx.n,
      f.2 + 1 - f.1 = 3 →
      ∃ T ∈ cells st.ptn level ctx.n, T.2 + 1 - T.1 = 3 ∧
        f.1 = T.1 ∧ f.2 = T.2 := by
    intro f hf hf3
    obtain ⟨q, hq, hq1, hq2⟩ :=
      childSt_cell_parent hIt hlvl hcell hne ho f hf
    have hqsz : f.2 + 1 - f.1 ≤ q.2 + 1 - q.1 := by
      have := cells_le _ hf
      omega
    rcases child_cells_cases hpsz hend hIt.valsWeak hcell hne hq with hs | hr | hold
    · -- the split singleton: too small
      rw [hs] at hqsz
      omega
    · -- the remainder: at most two positions
      have hts := hsmall _ hcell
      rw [hr] at hqsz hq1 hq2
      rcases hts with h2 | ⟨h3, -⟩
      · omega
      · omega
    · -- an untouched parent cell
      obtain ⟨hqp, -⟩ := hold
      rcases hsmall _ hqp with h2 | ⟨h3, huniq⟩
      · omega
      · refine ⟨q, hqp, h3, by omega, by omega⟩
  intro f hf
  rcases Decidable.em (f.2 + 1 - f.1 ≤ 2) with h2 | h2
  · exact Or.inl h2
  · have hfle := cells_le _ hf
    obtain ⟨q, hq, hq1, hq2⟩ :=
      childSt_cell_parent hIt hlvl hcell hne ho f hf
    have hf3 : f.2 + 1 - f.1 = 3 := by
      have hqsz : f.2 + 1 - f.1 ≤ q.2 + 1 - q.1 := by omega
      rcases child_cells_cases hpsz hend hIt.valsWeak hcell hne hq with hs | hr | hold
      · rw [hs] at hqsz
        omega
      · have hts := hsmall _ hcell
        rw [hr] at hqsz
        rcases hts with ht2 | ⟨ht3, -⟩
        · omega
        · omega
      · obtain ⟨hqp, -⟩ := hold
        rcases hsmall _ hqp with ht2 | ⟨ht3, -⟩
        · omega
        · omega
    obtain ⟨T, hT, hT3, hfT1, hfT2⟩ := htri f hf hf3
    refine Or.inr ⟨hf3, ?_⟩
    intro f' hf' hf'3
    obtain ⟨T', hT', hT'3, hfT'1, hfT'2⟩ := htri f' hf' hf'3
    obtain ⟨-, huniq⟩ :=
      (hsmall _ hT).resolve_left (by omega)
    have hTT : T' = T := huniq T' hT' hT'3
    have h1 : f'.1 = f.1 := by rw [hfT'1, hTT, ← hfT1]
    have h2' : f'.2 = f.2 := by rw [hfT'2, hTT, ← hfT2]
    obtain ⟨fa, fb⟩ := f
    obtain ⟨fa', fb'⟩ := f'
    simp only at h1 h2'
    rw [h1, h2']

/-- The node invariant descends through one subtree step. -/
theorem subtreeOk_child {st : RefineSt} {level tc e o : Nat}
    (h : SubtreeOk ctx level st) (hlvl : level < ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hcell : (tc, e) ∈ cells st.ptn level ctx.n) (hne : tc < e)
    (ho : o ≤ e - tc) :
    SubtreeOk ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!) := by
  have hpsz := h.it.ok.ptnSize
  have hlsz := h.it.ok.labSize
  have hend := h.it.ok.ptnEnd
  have hen : e < ctx.n := target_end_lt hpsz hend hcell
  refine ⟨iterOk_child h.it hlvl hcell hne ho, ?_, ?_,
    smallShape_child h.it hlvl hcell hne ho h.small⟩
  · show Equitable ctx (level + 1)
      (refine ctx (level + 1)
        (breakout st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (insert 0 tc)
        (st.numcells + 1)).lab
      (refine ctx (level + 1)
        (breakout st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (insert 0 tc)
        (st.numcells + 1)).ptn
    exact equitable_breakout hlsz hpsz hend h.it.valsWeak
      h.it.ok.labOk h.it.inj hsymm h.eqt hcell hne ho h.acc
  · -- the boundary count stays accurate
    have htcopen : st.ptn[tc]! > level :=
      target_open hpsz hend hcell tc (Nat.le_refl _) hne
    have hsplit := bcount_breakout_eq (ptn := st.ptn) (level := level)
      (tc := tc) h.it.valsWeak htcopen (by omega) ctx.n
      (Nat.le_refl _)
    have hssz : (st.ptn.set! tc (level + 1)).size = ctx.n := by
      rw [Array.size_set!, hpsz]
    have hsend : (st.ptn.set! tc (level + 1))[(st.ptn.set! tc
        (level + 1)).size - 1]! ≤ level + 1 := by
      rw [hssz]
      rcases Decidable.em (tc = ctx.n - 1) with rfl | hx
      · rw [← hpsz, Array.getElem!_set!_self _ _ _ (by omega)]
        omega
      · rw [← hpsz,
          Array.getElem!_set!_ne _ _ _ _ (by rw [hpsz]; omega)]
        have : st.ptn[ctx.n - 1]! ≤ level := by
          rw [← hpsz]
          exact hend
        omega
    have hbsz : (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1.size =
        (st.ptn.set! tc (level + 1)).size := by
      rw [breakout_lab_size, hlsz, hssz]
    have hrb := refine_bcount (ctx := ctx) (level := level + 1)
      (lab := (breakout st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1)
      (ptn := st.ptn.set! tc (level + 1))
      (active := insert 0 tc) (numcells := st.numcells + 1)
      (by rw [hssz]) hbsz hsend
    have hacc := h.acc
    show bcount (refine ctx (level + 1)
        (breakout st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (insert 0 tc)
        (st.numcells + 1)).ptn (level + 1) ctx.n =
      (refine ctx (level + 1)
        (breakout st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (insert 0 tc)
        (st.numcells + 1)).numcells
    rw [show (if tc < ctx.n then 1 else 0) = 1 from
      ite_eq_left (by omega)] at hsplit
    omega

end Hex.GraphIso.Nauty
