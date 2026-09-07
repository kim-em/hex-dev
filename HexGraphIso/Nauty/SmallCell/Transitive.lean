/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Shapes
public import HexGraphIso.Nauty.Invariant.Store
import all HexGraphIso.Nauty.Equitable.Basic
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Fix

public section

/-!
The cell stabilizer acts transitively on each cell of a cheapautom
partition. The invariant is preserved by individualization and refinement.
Induction over target-cell paths, using refinement equivariance at each
deviation, proves equality of leaf rows and validates the code-1 scatter.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- No boundary strictly inside a window leaves the count unmoved. -/
private theorem bcount_stable {ptn : Array Nat} {level i e : Nat}
    (hint : ∀ j, i ≤ j → j < e → level < ptn[j]!) :
    ∀ m, i ≤ m → m ≤ e → bcount ptn level m = bcount ptn level i := by
  intro m
  induction m with
  | zero =>
    intro h1 _
    have : i = 0 := by omega
    rw [this]
  | succ k ih =>
    intro h1 h2
    rcases Decidable.em (i = k + 1) with rfl | hne
    · rfl
    · have hik : i ≤ k := by omega
      have hke : k < e := by omega
      have hopen : level < ptn[k]! := hint k hik hke
      rw [bcount_succ, ite_eq_right (by omega), ih hik (by omega)]
      omega

/-- A cell contributes exactly one boundary: its end. -/
private theorem bcount_cell_window {ptn : Array Nat} {level i : Nat}
    (hend : ptn[ptn.size - 1]! ≤ level) (hi : i < ptn.size) :
    bcount ptn level (cellEnd ptn level i + 1) =
      bcount ptn level i + 1 := by
  have hge : i ≤ cellEnd ptn level i := cellEnd_ge
  have hstable : bcount ptn level (cellEnd ptn level i) =
      bcount ptn level i :=
    bcount_stable (fun j hj hlt => cellEnd_interior hj hlt) _ hge
      (Nat.le_refl _)
  rw [bcount_succ, hstable,
    ite_eq_left (cellEnd_closed hend hi)]

/-- The cells listed from `i` onwards, plus the boundaries below `i`,
count every boundary. -/
private theorem cells_go_length_bcount {ptn : Array Nat}
    {level nn : Nat} (hps : ptn.size = nn)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel i : Nat), nn ≤ fuel + i → i ≤ nn →
      (cells.go ptn level nn fuel i).length + bcount ptn level i =
        bcount ptn level nn
  | 0, i, hf, hi => by
    have : i = nn := by omega
    rw [cells.go, this]
    simp
  | fuel + 1, i, hf, hi => by
    rw [cells.go]
    rcases Decidable.em (i < nn) with hlt | hge
    · rw [ite_eq_left hlt]
      have hilt : i < ptn.size := by omega
      have hlt' : cellEnd ptn level i < nn := by
        rw [← hps]
        exact cellEnd_lt hilt hend
      have hge' : i ≤ cellEnd ptn level i := cellEnd_ge
      have hrec := cells_go_length_bcount hps hend fuel
        (cellEnd ptn level i + 1) (by omega) (by omega)
      rw [List.length_cons, bcount_cell_window hend hilt] at *
      omega
    · rw [ite_eq_right hge]
      have : i = nn := by omega
      rw [this]
      simp

/-- The number of cells is the number of boundaries. -/
theorem cells_length_eq_bcount {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level) :
    (cells ptn level nn).length = bcount ptn level nn := by
  have h := cells_go_length_bcount hps hend nn 0 (by omega)
    (by omega)
  rw [cells]
  simpa [bcount] using h

/-- The first-branch shape: every cell is a singleton, a pair, or the
unique triple. -/
def SmallShape (n : Nat) (level : Nat) (ptn : Array Nat) : Prop :=
  ∀ q ∈ cells ptn level n, q.2 + 1 - q.1 ≤ 2 ∨
    (q.2 + 1 - q.1 = 3 ∧
      ∀ q' ∈ cells ptn level n, q'.2 + 1 - q'.1 = 3 → q' = q)

/-- The two shapes a passing `cheapautom` guard admits: the
first-branch shape, or a defect of at most four. Both yield flip data
at every cell, and both descend through individualization, which is
why the invariant carries the disjunction rather than either
disjunct. A defect-four node need not have the first-branch shape:
the four-vertex empty graph's root is a single cell of size four. -/
def NodeShape (n : Nat) (level : Nat) (ptn : Array Nat) : Prop :=
  SmallShape n level ptn ∨
    n - (cells ptn level n).length ≤ 4

/-- The facts every deviation below a cheapautom node consumes,
carried at each node of the subtree. -/
structure SubtreeOk (ctx : Ctx n) (level : Nat) (st : RefineSt n) :
    Prop where
  it : IterOk ctx level st
  eqt : Equitable ctx level st.lab st.ptn
  acc : bcount st.ptn level n = st.numcells
  shape : NodeShape n level st.ptn

/-- Every cell of the child partition sits inside a cell of the split
partition: refinement only adds boundaries. -/
theorem childSt_cell_parent {st : RefineSt n} {level tc e o : Nat}
    (hIt : IterOk ctx level st) (hlvl : level < n)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (ho : o ≤ e - tc) :
    ∀ f ∈ cells (childSt ctx level st tc st.lab[tc + o]!).ptn
        (level + 1) n,
      ∃ q ∈ cells (st.ptn.set! tc (level + 1)) (level + 1) n,
        q.1 ≤ f.1 ∧ f.2 ≤ q.2 := by
  intro f hf
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hen : e < n := target_end_lt hpsz hend hcell
  have hIt' := iterOk_child hIt hlvl hcell hne ho
  have hcpsz := hIt'.ok.ptnSize
  have hcend := hIt'.ok.ptnEnd
  have hssz : (st.ptn.set! tc (level + 1)).size = n := by
    rw [Array.size_set!, hpsz]
  have hsend : (st.ptn.set! tc (level + 1))[(st.ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hssz]
    rcases Decidable.em (tc = n - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      have : st.ptn[n - 1]! ≤ level := by
        have h := hend
        rw [hpsz] at h
        exact h
      omega
  have hbsz : (breakout n st.lab st.ptn (level + 1) tc
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
theorem smallShape_child {st : RefineSt n} {level tc e o : Nat}
    (hIt : IterOk ctx level st) (hlvl : level < n)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (ho : o ≤ e - tc) (hsmall : SmallShape n level st.ptn) :
    SmallShape n (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!).ptn := by
  have hpsz := hIt.ok.ptnSize
  have hend := hIt.ok.ptnEnd
  have hIt' := iterOk_child hIt hlvl hcell hne ho
  have hcend := hIt'.ok.ptnEnd
  have hcpsz := hIt'.ok.ptnSize
  -- the coordinates a child triple is forced to occupy
  have htri : ∀ f ∈ cells (childSt ctx level st tc
      st.lab[tc + o]!).ptn (level + 1) n,
      f.2 + 1 - f.1 = 3 →
      ∃ T ∈ cells st.ptn level n, T.2 + 1 - T.1 = 3 ∧
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

/-- The node shape descends: the first-branch shape by containment,
and a defect of at most four because individualization splits a cell
while the vertex count stays fixed, so the cell count strictly
grows. -/
theorem nodeShape_child {st : RefineSt n} {level tc e o : Nat}
    (hIt : IterOk ctx level st) (hlvl : level < n)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (ho : o ≤ e - tc) (hsh : NodeShape n level st.ptn) :
    NodeShape n (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!).ptn := by
  rcases hsh with hsmall | hdef
  · exact Or.inl (smallShape_child hIt hlvl hcell hne ho hsmall)
  refine Or.inr ?_
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hIt' := iterOk_child hIt hlvl hcell hne ho
  have hcpsz := hIt'.ok.ptnSize
  have hcend := hIt'.ok.ptnEnd
  have hen : e < n := target_end_lt hpsz hend hcell
  have hle : tc ≤ e := cells_le _ hcell
  have htcopen : st.ptn[tc]! > level :=
    target_open hpsz hend hcell tc (Nat.le_refl _) hne
  have hssz : (st.ptn.set! tc (level + 1)).size = n := by
    rw [Array.size_set!, hpsz]
  have hsend : (st.ptn.set! tc (level + 1))[(st.ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hssz]
    rcases Decidable.em (tc = n - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      have : st.ptn[n - 1]! ≤ level := by
        have h := hend
        rw [hpsz] at h
        exact h
      omega
  have hbsz : (breakout n st.lab st.ptn (level + 1) tc
      st.lab[tc + o]!).1.size = (st.ptn.set! tc (level + 1)).size := by
    rw [breakout_lab_size, hlsz, hssz]
  have hsplit := bcount_breakout_eq (ptn := st.ptn) (level := level)
    (tc := tc) hIt.valsWeak htcopen (by omega) n (Nat.le_refl _)
  rw [ite_eq_left (by omega : tc < n)] at hsplit
  -- refinement never reopens a closed position
  have hb : ∀ q : Nat, (st.ptn.set! tc (level + 1))[q]! ≤ level + 1 →
      (childSt ctx level st tc st.lab[tc + o]!).ptn[q]! ≤ level + 1 := by
    intro q hq
    show (refine ctx (level + 1) _ _ _ _).ptn[q]! ≤ level + 1
    rw [refine_frozen (by rw [hssz]) hbsz hsend hq]
    exact hq
  have hmono : bcount (st.ptn.set! tc (level + 1)) (level + 1) n ≤
      bcount (childSt ctx level st tc st.lab[tc + o]!).ptn
        (level + 1) n := bcount_mono hb
  rw [cells_length_eq_bcount hcpsz hcend]
  rw [cells_length_eq_bcount hpsz hend] at hdef
  omega

/-- Individualization and refinement preserve the refined-state invariants
and strictly increase the number of cells. No small-cell shape is needed. -/
theorem refined_child {st : RefineSt n} {level tc e o : Nat}
    (hit : IterOk ctx level st) (heqt : Equitable ctx level st.lab st.ptn)
    (hcount : bcount st.ptn level n = st.numcells) (hlvl : level < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (ho : o ≤ e - tc) :
    let child := childSt ctx level st tc st.lab[tc + o]!
    IterOk ctx (level + 1) child ∧ Equitable ctx (level + 1) child.lab child.ptn ∧
      bcount child.ptn (level + 1) n = child.numcells ∧ st.numcells < child.numcells := by
  dsimp only
  have hpsz := hit.ok.ptnSize
  have hlsz := hit.ok.labSize
  have hend := hit.ok.ptnEnd
  have hen : e < n := target_end_lt hpsz hend hcell
  refine ⟨iterOk_child hit hlvl hcell hne ho, ?_, ?_⟩
  · show Equitable ctx (level + 1)
      (refine ctx (level + 1)
        (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
        (st.numcells + 1)).lab
      (refine ctx (level + 1)
        (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
        (st.numcells + 1)).ptn
    exact equitable_breakout hlsz hpsz hend hit.valsWeak
      hit.ok.labOk hit.inj hsymm heqt hcell hne ho hcount
  · -- the boundary count stays accurate
    have htcopen : st.ptn[tc]! > level :=
      target_open hpsz hend hcell tc (Nat.le_refl _) hne
    have hsplit := bcount_breakout_eq (ptn := st.ptn) (level := level)
      (tc := tc) hit.valsWeak htcopen (by omega) n
      (Nat.le_refl _)
    have hssz : (st.ptn.set! tc (level + 1)).size = n := by
      rw [Array.size_set!, hpsz]
    have hsend : (st.ptn.set! tc (level + 1))[(st.ptn.set! tc
        (level + 1)).size - 1]! ≤ level + 1 := by
      rw [hssz]
      rcases Decidable.em (tc = n - 1) with rfl | hx
      · rw [Array.getElem!_set!_self _ _ _ (by omega)]
        omega
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        have : st.ptn[n - 1]! ≤ level := by
          have h := hend
          rw [hpsz] at h
          exact h
        omega
    have hbsz : (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1.size =
        (st.ptn.set! tc (level + 1)).size := by
      rw [breakout_lab_size, hlsz, hssz]
    have hrb := refine_bcount (ctx := ctx) (level := level + 1)
      (lab := (breakout n st.lab st.ptn (level + 1) tc
        st.lab[tc + o]!).1)
      (ptn := st.ptn.set! tc (level + 1))
      (active := VSet.empty.insert tc) (numcells := st.numcells + 1)
      (by rw [hssz]) hbsz hsend
    rw [show (if tc < n then 1 else 0) = 1 from
      ite_eq_left (by omega)] at hsplit
    have hacc : bcount (childSt ctx level st tc st.lab[tc + o]!).ptn (level + 1) n =
        (childSt ctx level st tc st.lab[tc + o]!).numcells := by
      change bcount (refine ctx (level + 1)
          (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
          (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
          (st.numcells + 1)).ptn (level + 1) n =
        (refine ctx (level + 1)
          (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
          (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
          (st.numcells + 1)).numcells
      omega
    refine ⟨hacc, ?_⟩
    have hmono : bcount (st.ptn.set! tc (level + 1)) (level + 1) n ≤
        bcount (childSt ctx level st tc st.lab[tc + o]!).ptn (level + 1) n := by
      apply bcount_mono
      intro q hq
      show (refine ctx (level + 1) _ _ _ _).ptn[q]! ≤ level + 1
      rw [refine_frozen (by rw [hssz]) hbsz hsend hq]
      exact hq
    omega

/-- The node invariant descends through one subtree step. -/
theorem subtreeOk_child {st : RefineSt n} {level tc e o : Nat}
    (h : SubtreeOk ctx level st) (hlvl : level < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (ho : o ≤ e - tc) :
    SubtreeOk ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!) := by
  obtain ⟨hit, heqt, hcount, _⟩ := refined_child h.it h.eqt h.acc hlvl hsymm hcell hne ho
  exact ⟨hit, heqt, hcount, nodeShape_child h.it hlvl hcell hne ho h.shape⟩

/-- A descent recording its target-and-offset path. -/
inductive DescPath (ctx : Ctx n) :
    Nat → RefineSt n → List (Nat × Nat) → Nat → RefineSt n → Prop where
  | refl (level : Nat) (st : RefineSt n) :
      DescPath ctx level st [] level st
  | step {level level' : Nat} {st st' : RefineSt n}
      {path : List (Nat × Nat)} (tc e o : Nat)
      (hlvl : level < n)
      (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
      (ho : o ≤ e - tc)
      (htail : DescPath ctx (level + 1)
        (childSt ctx level st tc st.lab[tc + o]!) path level' st') :
      DescPath ctx level st ((tc, o) :: path) level' st'

/-- Forgetting the path gives a plain descent. -/
theorem DescPath.descends {level level' : Nat} {st st' : RefineSt n}
    {p : List (Nat × Nat)}
    (h : DescPath ctx level st p level' st') :
    Descends ctx level st level' st' := by
  induction h with
  | refl _ _ => exact .refl _ _
  | step tc e o hlvl hcell hne ho htail ih =>
    exact .step tc e o hlvl hcell hne ho ih

/-- An empty path is the trivial descent. -/
theorem descPath_nil {level level' : Nat} {st st' : RefineSt n}
    (h : DescPath ctx level st [] level' st') :
    level' = level ∧ st' = st := by
  cases h
  exact ⟨rfl, rfl⟩

/-- The path-preserving bisimulation: a descent below one state
mirrors below any renamed-equivalent state along the same target
cells. -/
theorem descPath_transport {σ : Renaming n}
    (hg : RowsMap σ ctx.g ctx.g) :
    ∀ {level level' : Nat} {p : List (Nat × Nat)} {U U' V : RefineSt n},
      DescPath ctx level U p level' U' → IterOk ctx level U →
      StPerm level V (mapSt σ U) →
      ∃ V' q, DescPath ctx level V q level' V' ∧
        q.map Prod.fst = p.map Prod.fst ∧
        StPerm level' V' (mapSt σ U')
  | _, _, _, _, _, V, .refl _ _, _, hsp => ⟨V, [], .refl _ _, rfl, hsp⟩
  | level, level', _, U, U', V,
      .step tc e o hlvl hcell hne ho htail, hU, hsp => by
    have hV := iterOk_of_stPerm hU hsp
    have hptn : U.ptn = V.ptn := hsp.ptn
    have hpszV := hV.ok.ptnSize
    have hendV := hV.ok.ptnEnd
    have hcellV : (tc, e) ∈ cells V.ptn level n := by
      rw [← hptn]
      exact hcell
    have hen : e < n := target_end_lt hpszV hendV hcellV
    have hcellIsV : IsCell V.ptn level tc (e + 1 - tc) :=
      cells_isCell (by omega) hendV _ hcellV
    have hmemU : σ.toFun U.lab[tc + o]! ∈
        segN (U.lab.map σ.toFun) tc (e + 1 - tc) := by
      rw [segN_map (by rw [hU.ok.labSize]; omega)]
      exact List.mem_map.mpr
        ⟨U.lab[tc + o]!, mem_segN_iff.mpr ⟨o, by omega, rfl⟩, rfl⟩
    have hcpT := hsp.cells tc (e + 1 - tc) hcellIsV
    have hmemV : σ.toFun U.lab[tc + o]! ∈
        segN V.lab tc (e + 1 - tc) := hcpT.mem_iff.mpr hmemU
    obtain ⟨oV, hoVlt, hoVval⟩ := mem_segN_iff.mp hmemV
    have hsp' := stPerm_child hg hsp hU hcell hne
      (by omega) ho hoVval
    have hUok' := iterOk_child hU hlvl hcell hne ho
    obtain ⟨V', q, hdesc, hq, hspL⟩ :=
      descPath_transport hg htail hUok' hsp'
    exact ⟨V', (tc, oV) :: q,
      .step tc e oV hlvl hcellV hne (by omega) hdesc,
      by rw [List.map_cons, List.map_cons, hq], hspL⟩

/-- The path-preserving leaf collapse: a descent to a discrete state
mirrors along the same target cells with equal leaf rows and the same
final partition. -/
theorem descPath_leafRows {σ : Renaming n}
    (hg : RowsMap σ ctx.g ctx.g)
    {level level' : Nat} {p : List (Nat × Nat)} {U U' V : RefineSt n}
    (h : DescPath ctx level U p level' U')
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U))
    (hdisc : ∀ q, q < n → U'.ptn[q]! ≤ level') :
    ∃ V' q, DescPath ctx level V q level' V' ∧
      q.map Prod.fst = p.map Prod.fst ∧
      leafRows ctx V'.lab = leafRows ctx U'.lab ∧
      V'.ptn = U'.ptn := by
  obtain ⟨V', q, hdesc, hq, hspL⟩ := descPath_transport hg h hU hsp
  have hU' := descends_iterOk h.descends hU
  have hV' := iterOk_of_stPerm hU' hspL
  have hptn : U'.ptn = V'.ptn := hspL.ptn
  have hVdisc : ∀ z, z < V'.ptn.size → V'.ptn[z]! ≤ level' := by
    intro z hz
    rw [← hptn]
    rw [hV'.ok.ptnSize] at hz
    exact hdisc z hz
  have hVsz : V'.lab.size = V'.ptn.size := by
    rw [hV'.ok.labSize, hV'.ok.ptnSize]
  have hlabeq := stPerm_lab_eq hspL hVdisc hVsz
  have hlabeq' : U'.lab.map σ.toFun = V'.lab := hlabeq
  have hlr : leafRows ctx V'.lab = leafRows ctx U'.lab := by
    rw [← hlabeq']
    exact leafRows_map σ hg hU'.ok.labOk hU'.ok.labSize
  exact ⟨V', q, hdesc, hq, hlr, hptn.symm⟩

/-- The path-preserving single-deviation door: a self-symmetry of the
node carrying one child's individualized vertex to another's mirrors
any discrete descent below the first child along the same target
cells. -/
theorem descPath_deviation_self {σ : Renaming n} {st : RefineSt n}
    {level tc e oU oV level' : Nat} {U' : RefineSt n}
    {p : List (Nat × Nat)}
    (hIt : IterOk ctx level st) (hlvl : level < n)
    (hg : RowsMap σ ctx.g ctx.g)
    (hsp : StPerm level st (mapSt σ st))
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hvv : st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]!)
    (hdesc : DescPath ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + oU]!) p level' U')
    (hdisc : ∀ q, q < n → U'.ptn[q]! ≤ level') :
    ∃ V' q, DescPath ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + oV]!) q level' V' ∧
      q.map Prod.fst = p.map Prod.fst ∧
      leafRows ctx V'.lab = leafRows ctx U'.lab ∧
      V'.ptn = U'.ptn := by
  have hsp' := stPerm_child hg hsp hIt hcell hne hoV hoU hvv
  have hU0 := iterOk_child hIt hlvl hcell hne hoU
  exact descPath_leafRows hg hdesc hU0 hsp' hdisc

end Hex.GraphIso.Nauty

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- Any two distinct members of a cell are related by an automorphism
that preserves every cell of the node's partition. -/
theorem stabilizer_transitive {st : RefineSt n} {level tc te oU oV : Nat}
    (hS : SubtreeOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hcell : (tc, te) ∈ cells st.ptn level n) (hne : tc < te)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hone : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  rcases hS.shape with hsmall | hdef
  · rcases hsmall _ hcell with hsz2 | ⟨hsz3, huniq⟩
    · -- a pair target
      have hsz2' : te + 1 - tc ≤ 2 := hsz2
      have he : te = tc + 1 := by omega
      subst he
      have hOdd : ∀ q ∈ cells st.ptn level n,
          q.2 ≠ q.1 + 1 → (q.2 + 1 - q.1) % 2 = 1 := by
        intro q hq hqne
        have hqle := cells_le _ hq
        rcases hsmall _ hq with h2 | ⟨h3, -⟩
        · have h1 : q.2 + 1 - q.1 = 1 := by omega
          omega
        · omega
      exact pair_flip_data hS.it hgsz hsymm hloop hS.eqt
        hcell hOdd (by omega) (by omega) hone
    · -- the triple target
      have hsz3' : te + 1 - tc = 3 := hsz3
      have he : te = tc + 2 := by omega
      subst he
      have hsmall' : ∀ q ∈ cells st.ptn level n,
          q ≠ (tc, tc + 2) → q.2 + 1 - q.1 ≤ 2 := by
        intro q hq hqne
        rcases hsmall _ hq with h2 | ⟨h3, -⟩
        · exact h2
        · exact absurd (huniq q hq h3) hqne
      exact triple_flip_data hS.it hgsz hsymm hloop hS.eqt
        hcell hsmall' (by omega) (by omega) hone
  · -- the exotic shapes
    exact defect4_flip_data hS.it hgsz hsymm hloop hS.eqt hdef
      hcell hoU hoV hone

/-- Two discrete descents below a cheapautom node with the same target-cell
path have equal final levels and leaf rows. -/
theorem descPath_leafRows_all
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (tcs : List Nat) :
    ∀ {level : Nat} {st : RefineSt n} {p₁ p₂ : List (Nat × Nat)}
      {level₁ level₂ : Nat} {U V : RefineSt n},
      SubtreeOk ctx level st →
      DescPath ctx level st p₁ level₁ U →
      p₁.map Prod.fst = tcs →
      (∀ q, q < n → U.ptn[q]! ≤ level₁) →
      DescPath ctx level st p₂ level₂ V →
      p₂.map Prod.fst = tcs →
      (∀ q, q < n → V.ptn[q]! ≤ level₂) →
      level₂ = level₁ ∧ leafRows ctx V.lab = leafRows ctx U.lab := by
  induction tcs with
  | nil =>
    intro level st p₁ p₂ level₁ level₂ U V hS hU hp₁ hUd hV hp₂ hVd
    have h1 : p₁ = [] := by
      cases p₁ with
      | nil => rfl
      | cons a l => simp at hp₁
    have h2 : p₂ = [] := by
      cases p₂ with
      | nil => rfl
      | cons a l => simp at hp₂
    subst h1
    subst h2
    obtain ⟨hl₁, hU'⟩ := descPath_nil hU
    obtain ⟨hl₂, hV'⟩ := descPath_nil hV
    subst hU'
    subst hV'
    exact ⟨by omega, rfl⟩
  | cons tc tcs' ih =>
    intro level st p₁ p₂ level₁ level₂ U V hS hU hp₁ hUd hV hp₂ hVd
    cases p₁ with
    | nil => exact absurd hp₁ (by simp)
    | cons h₁ tl₁ =>
    cases p₂ with
    | nil => exact absurd hp₂ (by simp)
    | cons h₂ tl₂ =>
    obtain ⟨a₁, o₁⟩ := h₁
    obtain ⟨a₂, o₂⟩ := h₂
    rw [List.map_cons] at hp₁ hp₂
    injection hp₁ with hh₁ ht₁
    injection hp₂ with hh₂ ht₂
    have ha₁ : tc = a₁ := hh₁.symm
    subst ha₁
    have ha₂ : tc = a₂ := hh₂.symm
    subst ha₂
    cases hU with
    | step _ e₁ _ hlvl hcell₁ hne₁ ho₁ htail₁ =>
    cases hV with
    | step _ e₂ _ hlvl₂ hcell₂ hne₂ ho₂ htail₂ =>
    have hpsz := hS.it.ok.ptnSize
    have hend := hS.it.ok.ptnEnd
    have hee : e₁ = e₂ := cells_eq_of_start (by omega) hend
      hcell₁ hcell₂
    subst hee
    rcases Decidable.em (st.lab[tc + o₁]! = st.lab[tc + o₂]!) with
      hval | hval
    · -- the same child: recurse directly
      rw [← hval] at htail₂
      exact ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₁)
        htail₁ ht₁ hUd htail₂ ht₂ hVd
    · -- a deviation at this level, by the target's size
      have hflip := stabilizer_transitive hS hgsz hsymm hloop
        hcell₁ hne₁ ho₁ ho₂ (fun h => hval (by rw [h]))
      obtain ⟨σ, hgm, hspσ, hvv⟩ := hflip
      obtain ⟨W, qW, hdescW, hqW, hlrW, hptnW⟩ :=
        descPath_deviation_self hS.it hlvl hgm hspσ hcell₁ hne₁
          ho₁ ho₂ hvv htail₁ hUd
      have hWd : ∀ q, q < n → W.ptn[q]! ≤ level₁ := by
        intro q hq
        rw [hptnW]
        exact hUd q hq
      obtain ⟨hlev, hlr₂⟩ :=
        ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₂)
          hdescW (by rw [hqW, ht₁]) hWd htail₂ ht₂ hVd
      exact ⟨hlev, hlr₂.trans hlrW⟩

end Hex.GraphIso.Nauty

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- The search's child loops perform `breakout` at the parent and then
the child node's `refine` on the returned labelling, split partition,
and singleton active set. That composite is `childSt` of the parent's
post-refine state. -/
theorem childSt_eq_search_step (r : RefineSt n) (level tc tv : Nat) :
    refine ctx (level + 1)
      (breakout n r.lab r.ptn (level + 1) tc tv).1
      (breakout n r.lab r.ptn (level + 1) tc tv).2.1
      (breakout n r.lab r.ptn (level + 1) tc tv).2.2
      (r.numcells + 1) =
    childSt ctx level r tc tv := rfl

/-- A surviving target-cell vertex is a window member: any vertex of
the cell set `maketargetcell` returns sits at some offset of the
target cell, in the shape a `DescPath` step consumes. -/
theorem maketargetcell_mem {r : RefineSt n} {level tcLevel : Nat}
    {hint : Int} {tcPos size tv : Nat} {cellSet : VSet n}
    (hn1 : 1 ≤ level) (hsz : r.ptn.size = n)
    (hend : r.ptn[r.ptn.size - 1]! ≤ level)
    (hlive : bcount r.ptn level n < n)
    (hmk : maketargetcell ctx r.lab r.ptn level tcLevel hint =
      (tcPos, cellSet, size))
    (htv : cellSet.mem tv = true) :
    ∃ e o, (tcPos, e) ∈ cells r.ptn level n ∧ tcPos < e ∧
      o ≤ e - tcPos ∧ r.lab[tcPos + o]! = tv := by
  obtain ⟨tc, len, hmk', hic, hlen2, hbd⟩ :=
    maketargetcell_open (lab := r.lab) (tcLevel := tcLevel)
      (hint := hint) hn1 hsz hend hlive
  rw [hmk] at hmk'
  injection hmk' with h1 h23
  injection h23 with h2 h3
  subst h1
  subst h2
  subst h3
  have hmem : tv ∈ segN r.lab tcPos (tcPos + size - 1 + 1 - tcPos) :=
    (mem_worksetOf_iff.mp htv).2
  obtain ⟨o, ho, hov⟩ := mem_segN_iff.mp hmem
  refine ⟨tcPos + size - 1, o,
    mem_cells_of_isCell (by omega) hend hic (by omega) (by omega),
    by omega, by omega, hov⟩

/-- A passing guard gives the first-branch shape or the exotic
defect-at-most-four configuration: a cell of size four or five, or two
triples. The defect-four flip analogues discharge the second
disjunct. -/
theorem cheapautom_shape_or_exotic {ptn : Array Nat} {level : Nat}
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hch : cheapautom ptn level n = true) :
    SmallShape n level ptn ∨
      n - (cells ptn level n).length ≤ 4 := by
  rcases (cheapautom_iff hps hend).mp hch with hb1 | hb4
  · refine Or.inl fun q hq => ?_
    rcases cells_shape_of_defect_le hps hend hb1 q hq with
      h1 | h2 | h3
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr h3
  · exact Or.inr hb4

/-- The node invariant at a guard-passing node. The guard's two
branches are exactly the invariant's two shapes, so nothing is left
over: a defect-four node keeps its own shape rather than being forced
into the first-branch one, which it need not have. -/
theorem subtreeOk_of_cheapautom {r : RefineSt n} {level : Nat}
    (hIt : IterOk ctx level r)
    (heqt : Equitable ctx level r.lab r.ptn)
    (hacc : bcount r.ptn level n = r.numcells)
    (hch : cheapautom r.ptn level n = true) :
    SubtreeOk ctx level r :=
  ⟨hIt, heqt, hacc,
    cheapautom_shape_or_exotic hIt.ok.ptnSize hIt.ok.ptnEnd hch⟩

/-- The tie's central consequence: two discrete same-target descents
below a first-branch node end with equal leaf rows. The run-level
bookkeeping (`gcaFirst`, `eqlevFirst`, `firsttc`) supplies the two
descents with the same target path; this theorem turns them into the
rows equality the admission exits consume. -/
theorem leafRows_eq_of_descPaths
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {r : RefineSt n} {level : Nat} (hS : SubtreeOk ctx level r)
    {p₁ p₂ : List (Nat × Nat)} {level₁ level₂ : Nat} {U V : RefineSt n}
    (hU : DescPath ctx level r p₁ level₁ U)
    (hV : DescPath ctx level r p₂ level₂ V)
    (htcs : p₂.map Prod.fst = p₁.map Prod.fst)
    (hUd : ∀ q, q < n → U.ptn[q]! ≤ level₁)
    (hVd : ∀ q, q < n → V.ptn[q]! ≤ level₂) :
    leafRows ctx V.lab = leafRows ctx U.lab :=
  (descPath_leafRows_all hgsz hsymm hloop (p₁.map Prod.fst)
    hS hU rfl hUd hV htcs hVd).2

/-- The code-1 admission is a checked automorphism: the scatter
of the second descent's leaf labelling over the first's passes
`checkAutom`, with no `isautom` scan. -/
theorem checkAutom_scatter_of_descPaths
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {r : RefineSt n} {level : Nat} (hS : SubtreeOk ctx level r)
    {p₁ p₂ : List (Nat × Nat)} {level₁ level₂ : Nat} {U V : RefineSt n}
    (hU : DescPath ctx level r p₁ level₁ U)
    (hV : DescPath ctx level r p₂ level₂ V)
    (htcs : p₂.map Prod.fst = p₁.map Prod.fst)
    (hUd : ∀ q, q < n → U.ptn[q]! ≤ level₁)
    (hVd : ∀ q, q < n → V.ptn[q]! ≤ level₂)
    {γ : Array Nat} (hγsz : γ.size = n)
    (hsc : ∀ i, i < n → γ[U.lab[i]!]! = V.lab[i]!) :
    checkAutom ctx.g γ = true := by
  have hUok := descends_iterOk hU.descends hS.it
  have hVok := descends_iterOk hV.descends hS.it
  exact checkAutom_scatter_of_leafRows_eq hγsz hUok.ok.labSize
    (labInj_perm_range hUok.ok.labSize hUok.ok.labOk hUok.inj)
    hVok.ok.labSize
    (labInj_perm_range hVok.ok.labSize hVok.ok.labOk hVok.inj)
    hsc
    (leafRows_eq_of_descPaths hgsz hsymm hloop hS hU hV htcs
      hUd hVd).symm

end Hex.GraphIso.Nauty
