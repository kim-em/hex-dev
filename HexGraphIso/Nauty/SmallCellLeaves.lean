/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellPair
import all HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.EquitableStep
import all HexGraphIso.Nauty.EquitableStep
public import HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.EquitableFix

public section

/-!
The all-leaves node invariant (SPEC § Verified search refinement, the
code-1 arm of the store-validity obligation).

Every deviation below a cheapautom node consumes the same node facts:
the iteration invariant, equitability, an accurate boundary count, and
the node's shape. A passing guard admits two shapes, and `NodeShape`
carries their disjunction: the first-branch shape (every cell a
singleton, a pair, or one triple), or a defect of at most four. The
second is not a special case of the first. The four-vertex empty
graph's root is one cell of size four, so it has a defect of three and
no first-branch shape, and the instrumentation probe records it as a
reachable admission witness.

This file packages those facts as `SubtreeOk` and proves the invariant
descends through one individualize-and-refine step
(`subtreeOk_child`): the iteration invariant by `iterOk_child`,
equitability by `equitable_breakout`, the count by
`bcount_breakout_eq` + `refine_bcount`, and the shape by
`nodeShape_child`. The first-branch shape descends by containment,
every child cell sitting inside a cell of the split partition
(`childSt_cell_parent`, via `subcell_of_grow` and `refine_frozen`), so
sizes only shrink and a child triple fills the unique parent triple's
window exactly. A defect of at most four descends because
individualization splits a cell while the vertex count stays fixed, so
the cell count grows; `cells_length_eq_bcount` reads that count off
the boundary count, where `bcount_breakout_eq` and `refine_frozen`
already measure it.

Turning either shape into flip data belongs to `SmallCellAll`, above
the exotic layer where the defect-four analogues are proved.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # The cell count as a boundary count -/

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
def SmallShape (ctx : Ctx n) (level : Nat) (ptn : Array Nat) : Prop :=
  ∀ q ∈ cells ptn level n, q.2 + 1 - q.1 ≤ 2 ∨
    (q.2 + 1 - q.1 = 3 ∧
      ∀ q' ∈ cells ptn level n, q'.2 + 1 - q'.1 = 3 → q' = q)

/-- The two shapes a passing `cheapautom` guard admits: the
first-branch shape, or a defect of at most four. Both yield flip data
at every cell, and both descend through individualization, which is
why the invariant carries the disjunction rather than either
disjunct. A defect-four node need not have the first-branch shape:
the four-vertex empty graph's root is a single cell of size four. -/
def NodeShape (ctx : Ctx n) (level : Nat) (ptn : Array Nat) : Prop :=
  SmallShape ctx level ptn ∨
    n - (cells ptn level n).length ≤ 4

/-- The facts every deviation below a cheapautom node consumes,
carried at each node of the subtree. -/
structure SubtreeOk (ctx : Ctx n) (level : Nat) (st : RefineSt n) :
    Prop where
  it : IterOk ctx level st
  eqt : Equitable ctx level st.lab st.ptn
  acc : bcount st.ptn level n = st.numcells
  shape : NodeShape ctx level st.ptn

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
    (ho : o ≤ e - tc) (hsh : NodeShape ctx level st.ptn) :
    NodeShape ctx (level + 1)
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

/-- The node invariant descends through one subtree step. -/
theorem subtreeOk_child {st : RefineSt n} {level tc e o : Nat}
    (h : SubtreeOk ctx level st) (hlvl : level < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (ho : o ≤ e - tc) :
    SubtreeOk ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + o]!) := by
  have hpsz := h.it.ok.ptnSize
  have hlsz := h.it.ok.labSize
  have hend := h.it.ok.ptnEnd
  have hen : e < n := target_end_lt hpsz hend hcell
  refine ⟨iterOk_child h.it hlvl hcell hne ho, ?_, ?_,
    nodeShape_child h.it hlvl hcell hne ho h.shape⟩
  · show Equitable ctx (level + 1)
      (refine ctx (level + 1)
        (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
        (st.numcells + 1)).lab
      (refine ctx (level + 1)
        (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
        (st.numcells + 1)).ptn
    exact equitable_breakout hlsz hpsz hend h.it.valsWeak
      h.it.ok.labOk h.it.inj hsymm h.eqt hcell hne ho h.acc
  · -- the boundary count stays accurate
    have htcopen : st.ptn[tc]! > level :=
      target_open hpsz hend hcell tc (Nat.le_refl _) hne
    have hsplit := bcount_breakout_eq (ptn := st.ptn) (level := level)
      (tc := tc) h.it.valsWeak htcopen (by omega) n
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
    have hacc := h.acc
    show bcount (refine ctx (level + 1)
        (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
        (st.numcells + 1)).ptn (level + 1) n =
      (refine ctx (level + 1)
        (breakout n st.lab st.ptn (level + 1) tc st.lab[tc + o]!).1
        (st.ptn.set! tc (level + 1)) (VSet.empty.insert tc)
        (st.numcells + 1)).numcells
    rw [show (if tc < n then 1 else 0) = 1 from
      ite_eq_left (by omega)] at hsplit
    omega

/-! # Descents that record their paths

The all-leaves induction compares two descents choosing the same
target cell at every level but possibly different vertices. `DescPath`
is `Descends` with the target-and-offset path recorded; the transport
and leaf-collapse theorems mirror the `Descends` versions, additionally
preserving the target projection of the path (the bisimulation reuses
each step's target cell), which is what lets the induction recurse on
the transported descent. -/

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
