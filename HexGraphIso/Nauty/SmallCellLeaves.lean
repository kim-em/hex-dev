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

/-! # Descents that record their paths

The all-leaves induction compares two descents choosing the same
target cell at every level but possibly different vertices. `DescPath`
is `Descends` with the target-and-offset path recorded; the transport
and leaf-collapse theorems mirror the `Descends` versions, additionally
preserving the target projection of the path (the bisimulation reuses
each step's target cell), which is what lets the induction recurse on
the transported descent. -/

/-- A descent recording its target-and-offset path. -/
inductive DescPath (ctx : Ctx) :
    Nat → RefineSt → List (Nat × Nat) → Nat → RefineSt → Prop where
  | refl (level : Nat) (st : RefineSt) :
      DescPath ctx level st [] level st
  | step {level level' : Nat} {st st' : RefineSt}
      {path : List (Nat × Nat)} (tc e o : Nat)
      (hlvl : level < ctx.n)
      (hcell : (tc, e) ∈ cells st.ptn level ctx.n) (hne : tc < e)
      (ho : o ≤ e - tc)
      (htail : DescPath ctx (level + 1)
        (childSt ctx level st tc st.lab[tc + o]!) path level' st') :
      DescPath ctx level st ((tc, o) :: path) level' st'

/-- Forgetting the path gives a plain descent. -/
theorem DescPath.descends {level level' : Nat} {st st' : RefineSt}
    {p : List (Nat × Nat)}
    (h : DescPath ctx level st p level' st') :
    Descends ctx level st level' st' := by
  induction h with
  | refl _ _ => exact .refl _ _
  | step tc e o hlvl hcell hne ho htail ih =>
    exact .step tc e o hlvl hcell hne ho ih

/-- An empty path is the trivial descent. -/
theorem descPath_nil {level level' : Nat} {st st' : RefineSt}
    (h : DescPath ctx level st [] level' st') :
    level' = level ∧ st' = st := by
  cases h
  exact ⟨rfl, rfl⟩

/-- The path-preserving bisimulation: a descent below one state
mirrors below any renamed-equivalent state along the same target
cells. -/
theorem descPath_transport {σ : Renaming ctx.n}
    (hg : RowsMap σ ctx.g ctx.g) :
    ∀ {level level' : Nat} {p : List (Nat × Nat)} {U U' V : RefineSt},
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
    have hcellV : (tc, e) ∈ cells V.ptn level ctx.n := by
      rw [← hptn]
      exact hcell
    have hen : e < ctx.n := target_end_lt hpszV hendV hcellV
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
theorem descPath_leafRows {σ : Renaming ctx.n}
    (hg : RowsMap σ ctx.g ctx.g)
    {level level' : Nat} {p : List (Nat × Nat)} {U U' V : RefineSt}
    (h : DescPath ctx level U p level' U')
    (hU : IterOk ctx level U) (hsp : StPerm level V (mapSt σ U))
    (hdisc : ∀ q, q < ctx.n → U'.ptn[q]! ≤ level') :
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
    exact leafRows_map σ rfl rfl hg hU'.ok.labOk hU'.ok.labSize
  exact ⟨V', q, hdesc, hq, hlr, hptn.symm⟩

/-- The path-preserving single-deviation door: a self-symmetry of the
node carrying one child's individualized vertex to another's mirrors
any discrete descent below the first child along the same target
cells. -/
theorem descPath_deviation_self {σ : Renaming ctx.n} {st : RefineSt}
    {level tc e oU oV level' : Nat} {U' : RefineSt}
    {p : List (Nat × Nat)}
    (hIt : IterOk ctx level st) (hlvl : level < ctx.n)
    (hg : RowsMap σ ctx.g ctx.g)
    (hsp : StPerm level st (mapSt σ st))
    (hcell : (tc, e) ∈ cells st.ptn level ctx.n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hvv : st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]!)
    (hdesc : DescPath ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + oU]!) p level' U')
    (hdisc : ∀ q, q < ctx.n → U'.ptn[q]! ≤ level') :
    ∃ V' q, DescPath ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + oV]!) q level' V' ∧
      q.map Prod.fst = p.map Prod.fst ∧
      leafRows ctx V'.lab = leafRows ctx U'.lab ∧
      V'.ptn = U'.ptn := by
  have hsp' := stPerm_child hg hsp hIt hcell hne hoV hoU hvv
  have hU0 := iterOk_child hIt hlvl hcell hne hoU
  exact descPath_leafRows hg hdesc hU0 hsp' hdisc

/-! # All leaves below a first-branch node have equal rows -/

/-- Any two discrete descents below a first-branch node choosing the
same target cells have equal leaf rows: equal choices recurse, and a
differing choice is one pair or triple deviation glued to the
transported deeper path. -/
theorem descPath_leafRows_all
    (hgsz : ctx.g.size = ctx.n)
    (hgb : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (tcs : List Nat) :
    ∀ {level : Nat} {st : RefineSt} {p₁ p₂ : List (Nat × Nat)}
      {level₁ level₂ : Nat} {U V : RefineSt},
      SubtreeOk ctx level st →
      DescPath ctx level st p₁ level₁ U →
      p₁.map Prod.fst = tcs →
      (∀ q, q < ctx.n → U.ptn[q]! ≤ level₁) →
      DescPath ctx level st p₂ level₂ V →
      p₂.map Prod.fst = tcs →
      (∀ q, q < ctx.n → V.ptn[q]! ≤ level₂) →
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
      have hflip : ∃ σ : Renaming ctx.n, RowsMap σ ctx.g ctx.g ∧
          StPerm level st (mapSt σ st) ∧
          st.lab[tc + o₂]! = σ.toFun st.lab[tc + o₁]! := by
        have hone : o₁ ≠ o₂ := fun h => hval (by rw [h])
        rcases hS.small _ hcell₁ with hsz2 | ⟨hsz3, huniq⟩
        · -- a pair target
          have hsz2' : e₁ + 1 - tc ≤ 2 := hsz2
          have hne₁' : tc < e₁ := hne₁
          have he : e₁ = tc + 1 := by omega
          subst he
          have hOdd : ∀ q ∈ cells st.ptn level ctx.n,
              q.2 ≠ q.1 + 1 → (q.2 + 1 - q.1) % 2 = 1 := by
            intro q hq hqne
            have hqle := cells_le _ hq
            rcases hS.small _ hq with h2 | ⟨h3, -⟩
            · have h1 : q.2 + 1 - q.1 = 1 := by omega
              omega
            · omega
          exact pair_flip_data hS.it hgsz hgb hsymm hloop hS.eqt
            hcell₁ hOdd (by omega) (by omega) hone
        · -- the triple target
          have hsz3' : e₁ + 1 - tc = 3 := hsz3
          have hne₁' : tc < e₁ := hne₁
          have he : e₁ = tc + 2 := by omega
          subst he
          have hsmall' : ∀ q ∈ cells st.ptn level ctx.n,
              q ≠ (tc, tc + 2) → q.2 + 1 - q.1 ≤ 2 := by
            intro q hq hqne
            rcases hS.small _ hq with h2 | ⟨h3, -⟩
            · exact h2
            · exact absurd (huniq q hq h3) hqne
          exact triple_flip_data hS.it hgsz hgb hsymm hloop hS.eqt
            hcell₁ hsmall' (by omega) (by omega) hone
      obtain ⟨σ, hgm, hspσ, hvv⟩ := hflip
      obtain ⟨W, qW, hdescW, hqW, hlrW, hptnW⟩ :=
        descPath_deviation_self hS.it hlvl hgm hspσ hcell₁ hne₁
          ho₁ ho₂ hvv htail₁ hUd
      have hWd : ∀ q, q < ctx.n → W.ptn[q]! ≤ level₁ := by
        intro q hq
        rw [hptnW]
        exact hUd q hq
      obtain ⟨hlev, hlr₂⟩ :=
        ih (subtreeOk_child hS hlvl hsymm hcell₁ hne₁ ho₂)
          hdescW (by rw [hqW, ht₁]) hWd htail₂ ht₂ hVd
      exact ⟨hlev, hlr₂.trans hlrW⟩

end Hex.GraphIso.Nauty
