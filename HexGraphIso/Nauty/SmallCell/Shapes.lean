/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Guard
public import HexGraphIso.Nauty.SmallCell.Flip
import all HexGraphIso.Nauty.Equitable.Basic
import all HexGraphIso.Nauty.Equitable.Step
import all HexGraphIso.Nauty.Equitable.Fix

public section

/-!
Cell-stabilizing automorphisms for equitable partitions admitted by
cheapautom. Pair cells use matching closure. The remaining shapes use
balanced distinguishing sets and regularity inside cells of size at most
five. Every construction uses the same transposition and cell-map criteria.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- Members of the triple cell have identical bits at every member of
any other cell of size at most two. -/
theorem triple_const {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {d : Nat} (hT : (d, d + 2) ∈ cells ptn level n)
    {c ce : Nat} (hC : (c, ce) ∈ cells ptn level n)
    (hsz : ce + 1 - c ≤ 2)
    {o o' w : Nat} (ho : o < 3) (ho' : o' < 3) (hw : w < ce + 1 - c) :
    (ctx.g[lab[d + o]!]!).mem lab[c + w]! =
      (ctx.g[lab[d + o']!]!).mem lab[c + w]! := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hce : ce < n := by
    have := cells_bound (by omega) hend _ hC
    omega
  have hcce := cells_le _ hC
  have hcount := hE _ hT _ hC o o' (by omega) (by omega)
  rcases Decidable.em (ce = c) with hone | htwo
  · -- a singleton
    subst hone
    have hw0 : w = 0 := by omega
    subst hw0
    rw [worksetOf_singleton, VSet.cardInter_singleton,
      VSet.cardInter_singleton] at hcount
    rcases hb : (ctx.g[lab[d + o]!]!).mem lab[ce]! with _ | _ <;>
      rcases hb' : (ctx.g[lab[d + o']!]!).mem lab[ce]! with _ | _ <;>
        rw [hb, hb'] at hcount <;> simp_all
  · -- a pair
    have hpair : ce = c + 1 := by omega
    subst hpair
    have hC' : (c, c + 1) ∈ cells ptn level n := hC
    have hodd3 : (d + 2 + 1 - d) % 2 = 1 := by omega
    have hboth := pair_odd_eq hE hps hend hinj hlb hsymm hC' hT
      hodd3
    have hb_o := hboth o (by omega)
    have hb_o' := hboth o' (by omega)
    -- transport the pair-side equalities to the triple side
    have hto : o ≤ 2 := by omega
    have hto' : o' ≤ 2 := by omega
    have hself_o : (ctx.g[lab[d + o]!]!).mem lab[c]! =
        (ctx.g[lab[d + o]!]!).mem lab[c + 1]! := by
      rw [hsymm lab[d + o]! lab[c]! (hlb (d + o) (by omega))
          (hlb c (by omega)),
        hsymm lab[d + o]! lab[c + 1]! (hlb (d + o) (by omega))
          (hlb (c + 1) (by omega))]
      exact hb_o
    have hself_o' : (ctx.g[lab[d + o']!]!).mem lab[c]! =
        (ctx.g[lab[d + o']!]!).mem lab[c + 1]! := by
      rw [hsymm lab[d + o']! lab[c]! (hlb (d + o') (by omega))
          (hlb c (by omega)),
        hsymm lab[d + o']! lab[c + 1]! (hlb (d + o') (by omega))
          (hlb (c + 1) (by omega))]
      exact hb_o'
    rw [count_into_cell hps hend hinj hC',
      count_into_cell hps hend hinj hC',
      show c + 1 + 1 - c = 2 by omega, sum_range_two,
      sum_range_two] at hcount
    simp only [Nat.add_zero] at hcount
    have hcnt_o : bitCnt ctx.g[lab[d + o]!]! lab[c]! =
        bitCnt ctx.g[lab[d + o]!]! lab[c + 1]! :=
      bitCnt_inj.mpr hself_o
    have hcnt_o' : bitCnt ctx.g[lab[d + o']!]! lab[c]! =
        bitCnt ctx.g[lab[d + o']!]! lab[c + 1]! :=
      bitCnt_inj.mpr hself_o'
    have hkey : bitCnt ctx.g[lab[d + o]!]! lab[c]! =
        bitCnt ctx.g[lab[d + o']!]! lab[c]! := by omega
    have hbit0 : (ctx.g[lab[d + o]!]!).mem lab[c]! =
        (ctx.g[lab[d + o']!]!).mem lab[c]! := bitCnt_inj.mp hkey
    rcases Decidable.em (w = 0) with rfl | hw1
    · exact hbit0
    · have hw1' : w = 1 := by omega
      subst hw1'
      rw [← hself_o, ← hself_o']
      exact hbit0

/-- All off-diagonal internal bits of the triple agree. -/
theorem triple_internal {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    {d : Nat} (hT : (d, d + 2) ∈ cells ptn level n) :
    ∀ o o' u u', o < 3 → o' < 3 → u < 3 → u' < 3 → o ≠ o' → u ≠ u' →
      (ctx.g[lab[d + o]!]!).mem lab[d + o']! =
        (ctx.g[lab[d + u]!]!).mem lab[d + u']! := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hbnd : ∀ o, o < 3 → d + o < n := by
    intro o ho
    omega
  -- the three row sums are equal
  have hrow : ∀ o o', o < 3 → o' < 3 →
      bitCnt ctx.g[lab[d + o]!]! lab[d + 0]! +
        bitCnt ctx.g[lab[d + o]!]! lab[d + 1]! +
        bitCnt ctx.g[lab[d + o]!]! lab[d + 2]! =
      bitCnt ctx.g[lab[d + o']!]! lab[d + 0]! +
        bitCnt ctx.g[lab[d + o']!]! lab[d + 1]! +
        bitCnt ctx.g[lab[d + o']!]! lab[d + 2]! := by
    intro o o' ho ho'
    have hcount := hE _ hT _ hT o o' (by omega) (by omega)
    rw [count_into_cell hps hend hinj hT,
      count_into_cell hps hend hinj hT,
      show d + 2 + 1 - d = 3 by omega, sum_range_three,
      sum_range_three] at hcount
    exact hcount
  -- the diagonal is zero
  have hdiag : ∀ o, o < 3 →
      bitCnt ctx.g[lab[d + o]!]! lab[d + o]! = 0 := by
    intro o ho
    exact bitCnt_eq_zero.mpr (hloop _ (hlb _ (hbnd o ho)))
  -- symmetry at the bit-count level
  have hsym : ∀ o o', o < 3 → o' < 3 →
      bitCnt ctx.g[lab[d + o]!]! lab[d + o']! =
        bitCnt ctx.g[lab[d + o']!]! lab[d + o]! := by
    intro o o' ho ho'
    exact bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (hbnd o ho)) (hlb _ (hbnd o' ho')))
  -- name the three off-diagonal counts
  have h01 := hrow 0 1 (by omega) (by omega)
  have h12 := hrow 1 2 (by omega) (by omega)
  rw [hdiag 0 (by omega), hdiag 1 (by omega)] at h01
  rw [hdiag 1 (by omega), hdiag 2 (by omega)] at h12
  rw [hsym 1 0 (by omega) (by omega)] at h01
  rw [hsym 1 0 (by omega) (by omega),
    hsym 2 0 (by omega) (by omega),
    hsym 2 1 (by omega) (by omega)] at h12
  -- h01 : 0 + c01 + c02 = c01 + 0 + c12  →  c02 = c12
  -- h12 : c01 + 0 + c12 = c02 + c12 + 0  →  c01 = c02
  have hle01 := bitCnt_le_one ctx.g[lab[d + 0]!]! lab[d + 1]!
  have hle02 := bitCnt_le_one ctx.g[lab[d + 0]!]! lab[d + 2]!
  have hle12 := bitCnt_le_one ctx.g[lab[d + 1]!]! lab[d + 2]!
  have hall : bitCnt ctx.g[lab[d + 0]!]! lab[d + 1]! =
      bitCnt ctx.g[lab[d + 0]!]! lab[d + 2]! ∧
      bitCnt ctx.g[lab[d + 0]!]! lab[d + 2]! =
      bitCnt ctx.g[lab[d + 1]!]! lab[d + 2]! := by omega
  -- every off-diagonal bit equals bit (0,1)
  have hcanon : ∀ o o', o < 3 → o' < 3 → o ≠ o' →
      bitCnt ctx.g[lab[d + o]!]! lab[d + o']! =
        bitCnt ctx.g[lab[d + 0]!]! lab[d + 1]! := by
    intro o o' ho ho' hne
    have ho3 : o = 0 ∨ o = 1 ∨ o = 2 := by omega
    have ho'3 : o' = 0 ∨ o' = 1 ∨ o' = 2 := by omega
    rcases ho3 with rfl | rfl | rfl <;>
      rcases ho'3 with rfl | rfl | rfl
    · omega
    · rfl
    · omega
    · rw [hsym 1 0 (by omega) (by omega)]
    · omega
    · omega
    · rw [hsym 2 0 (by omega) (by omega)]
      omega
    · rw [hsym 2 1 (by omega) (by omega)]
      omega
    · omega
  intro o o' u u' ho ho' hu hu' hoo huu
  exact bitCnt_inj.mp
    ((hcanon o o' ho ho' hoo).trans (hcanon u u' hu hu' huu).symm)

section TripleFlip

variable {lab ptn : Array Nat} {level d : Nat} {f : Nat → Nat}

/-- Vertices outside the transposed pair have identical bits at the
two transposed members. -/
private theorem triple_adj_aux
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hT : (d, d + 2) ∈ cells ptn level n)
    (hsmall : ∀ q ∈ cells ptn level n, q ≠ (d, d + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    {j : Nat} (hj : j < n)
    (hjA : lab[j]! ≠ lab[d + a]!) (hjB : lab[j]! ≠ lab[d + b]!) :
    (ctx.g[lab[d + a]!]!).mem lab[j]! =
      (ctx.g[lab[d + b]!]!).mem lab[j]! := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  obtain ⟨q, hq, hj1, hj2⟩ := cells_cover (ptn := ptn)
    (level := level) j hj
  rcases Decidable.em (q = (d, d + 2)) with rfl | hqT
  · -- j sits inside the triple: the third member
    have hj1' : d ≤ j := hj1
    have hj2' : j ≤ d + 2 := hj2
    have hw3 : j - d < 3 := by omega
    have hwa : j - d ≠ a := fun hcon => hjA (by
      have : j = d + a := by omega
      rw [this])
    have hwb : j - d ≠ b := fun hcon => hjB (by
      have : j = d + b := by omega
      rw [this])
    have hint := triple_internal hE hps hend hinj hlb hsymm hloop
      hT a (j - d) b (j - d) ha hw3 hb hw3
      (fun hcon => hwa hcon.symm) (fun hcon => hwb hcon.symm)
    rw [show d + (j - d) = j by omega] at hint
    exact hint
  · -- j sits in another, small cell
    have hqsz := hsmall q hq hqT
    have hconst := triple_const hE hps hend hinj hlb hsymm hT hq
      hqsz (o := a) (o' := b) (w := j - q.1) ha hb (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at hconst
    exact hconst

/-- The triple flip theorem: the transposition of two triple members,
fixing every other vertex, preserves the adjacency rows. -/
theorem triple_flip_rows
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsurj : ∀ v, v < n → ∃ i, i < n ∧ lab[i]! = v)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hT : (d, d + 2) ∈ cells ptn level n)
    (hsmall : ∀ q ∈ cells ptn level n, q ≠ (d, d + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    (hswap : f lab[d + a]! = lab[d + b]! ∧ f lab[d + b]! = lab[d + a]!)
    (hfix : ∀ v, v < n → v ≠ lab[d + a]! → v ≠ lab[d + b]! →
      f v = v) :
    ∀ v, v < n → ctx.g[f v]! = (ctx.g[v]!).image f := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hAn : lab[d + a]! < n := hlb _ (by omega)
  have hBn : lab[d + b]! < n := hlb _ (by omega)
  apply rows_of_bits hfb hinvol
  apply flip_bits (P := fun u v => u = lab[d + a]! ∧ v = lab[d + b]!) hsymm hfb
  · rintro u v ⟨rfl, rfl⟩
    exact hswap
  · intro z hz
    by_cases hza : z = lab[d + a]!
    · exact Or.inr ⟨_, _, hAn, hBn, ⟨rfl, rfl⟩, Or.inl hza⟩
    by_cases hzb : z = lab[d + b]!
    · exact Or.inr ⟨_, _, hAn, hBn, ⟨rfl, rfl⟩, Or.inr hzb⟩
    exact Or.inl (hfix z hz hza hzb)
  · rintro z hz hf u v ⟨rfl, rfl⟩
    by_cases hAB : lab[d + a]! = lab[d + b]!
    · rw [hAB]
    have hza := fixed_ne hf hswap.1 hAB
    have hzb := fixed_ne hf hswap.2 (Ne.symm hAB)
    obtain ⟨j, hj, rfl⟩ := hsurj z hz
    rw [hsymm _ _ (hlb j hj) hAn, hsymm _ _ (hlb j hj) hBn]
    exact triple_adj_aux hE hps hend hinj hlb hsymm hloop hT hsmall ha hb hj hza hzb
  · rintro u v x y ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
    exact ⟨by rw [hloop _ hAn, hloop _ hBn], hsymm _ _ hAn hBn⟩

end TripleFlip

/-- The flip data at a triple target: a row-preserving self-symmetry
of the node carrying one child's individualized vertex to the
other's. -/
theorem triple_flip_data {st : RefineSt n} {level tc : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT : (tc, tc + 2) ∈ cells st.ptn level n)
    (hsmall : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3) (hab : a ≠ b) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + b]! = σ.toFun st.lab[tc + a]! := by
  have hd2 : tc + 2 < n := by
    have := cells_bound (by rw [hIt.ok.ptnSize]; omega)
      hIt.ok.ptnEnd _ hT
    rw [hIt.ok.ptnSize] at this
    omega
  have hlb' : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hIt.ok.labSize]; omega)
  have hAn : st.lab[tc + a]! < n := hlb' (tc + a) (by omega)
  have hBn : st.lab[tc + b]! < n := hlb' (tc + b) (by omega)
  have hABne : st.lab[tc + a]! ≠ st.lab[tc + b]! := by
    intro hcon
    have := hIt.inj (tc + a) (tc + b) (by omega) (by omega) hcon
    omega
  let f := sw1 st.lab[tc + a]! st.lab[tc + b]!
  have hswapf : f st.lab[tc + a]! = st.lab[tc + b]! ∧
      f st.lab[tc + b]! = st.lab[tc + a]! := ⟨sw1_u, sw1_v hABne⟩
  have hfixf : ∀ v, v < n → v ≠ st.lab[tc + a]! →
      v ≠ st.lab[tc + b]! → f v = v := fun _ _ h1 h2 => sw1_fix h1 h2
  have hfb : ∀ v, v < n → f v < n := sw1_lt hAn hBn
  have hinvol : ∀ v, v < n → f (f v) = v := fun v _ => sw1_invol hABne v
  have hsurj := labInj_surj
    (by rw [hIt.ok.labSize] ; exact Nat.le_refl _ : n ≤ _)
    hIt.ok.labOk hIt.inj
  have hrows := triple_flip_rows hE hIt.ok.ptnSize hIt.ok.ptnEnd
    hIt.inj hlb' hsurj hsymm hloop hfb hinvol hT hsmall ha hb
    hswapf hfixf
  have hgmap := rowsMap_of_flip_rows hgsz hfb hinvol hrows
  refine ⟨renamingOfFlip f n hfb hinvol, hgmap,
    stPerm_self_setwise hIt.ok hIt.inj hfb hinvol
      (sw1_cells hIt.ok hIt.inj hT (by omega) (by omega) hab), ?_⟩
  rw [renamingOfFlip_at hfb hinvol hAn]
  exact hswapf.1.symm

section PairClosure

variable {lab ptn : Array Nat} {level : Nat}

/-- The `PairMatch`-reachability closure of a pair-cell start. -/
inductive PairReach (ctx : Ctx n) (lab ptn : Array Nat) (level : Nat)
    (t : Nat) : Nat → Prop where
  | base : PairReach ctx lab ptn level t t
  | step {c e : Nat} : PairReach ctx lab ptn level t c →
      (c, c + 1) ∈ cells ptn level n →
      (e, e + 1) ∈ cells ptn level n →
      PairMatch ctx.g lab[c]! lab[c + 1]! lab[e]! lab[e + 1]! →
      PairReach ctx lab ptn level t e

/-- A cell is determined by its start. -/
theorem cells_eq_of_start {nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {c e e' : Nat} (h1 : (c, e) ∈ cells ptn level nn)
    (h2 : (c, e') ∈ cells ptn level nn) : e = e' := by
  obtain ⟨-, -, he⟩ := (mem_cells_iff hnn hend).mp h1
  obtain ⟨-, -, he'⟩ := (mem_cells_iff hnn hend).mp h2
  rw [he, he']

/-- A pair start is never another pair's second position. -/
theorem pair_start_ne_second {nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {c c' : Nat} (h1 : (c, c + 1) ∈ cells ptn level nn)
    (h2 : (c', c' + 1) ∈ cells ptn level nn) : c ≠ c' + 1 := by
  intro heq
  obtain ⟨hlt', -, he'⟩ := (mem_cells_iff hnn hend).mp h2
  obtain ⟨-, hstart, -⟩ := (mem_cells_iff hnn hend).mp h1
  have hopen : ptn[c']! > level := by
    have hIs := cells_isCell hnn hend _ h2
    rw [show c' + 1 + 1 - c' = 2 by omega] at hIs
    exact hIs.2.2.1 c' (Nat.le_refl _) (by omega)
  rcases hstart with h0 | hcl
  · omega
  · rw [heq, show c' + 1 - 1 = c' by omega] at hcl
    omega

/-- Every member of the closure of a pair start is itself a pair-cell
start. -/
theorem pairReach_pair {t c : Nat}
    (hroot : (t, t + 1) ∈ cells ptn level n)
    (h : PairReach ctx lab ptn level t c) :
    (c, c + 1) ∈ cells ptn level n := by
  induction h with
  | base => exact hroot
  | step hr hc he hm ih => exact he

/-- Distinct closure pairs occupy disjoint positions. -/
theorem pair_cells_disj {nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    {c c' : Nat} (h1 : (c, c + 1) ∈ cells ptn level nn)
    (h2 : (c', c' + 1) ∈ cells ptn level nn) (hne : c ≠ c') :
    c + 2 ≤ c' ∨ c' + 2 ≤ c := by
  have hIs1 := cells_isCell hnn hend _ h1
  have hIs2 := cells_isCell hnn hend _ h2
  rw [show c + 1 + 1 - c = 2 by omega] at hIs1
  rw [show c' + 1 + 1 - c' = 2 by omega] at hIs2
  rcases isCell_disj_or_eq hIs1 hIs2 with ⟨heq, -⟩ | hd | hd
  · exact absurd heq hne
  · exact Or.inl hd
  · exact Or.inr hd

end PairClosure

end Hex.GraphIso.Nauty

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

section PairFlip

open Classical

variable {lab ptn : Array Nat} {level t : Nat}

/-- The involution swapping every pair in the `PairReach` closure of
`t`: a vertex that is a member of a closure pair maps to its partner,
and every other vertex is fixed. -/
noncomputable def pairFlip (ctx : Ctx n) (lab ptn : Array Nat)
    (level t : Nat) : Nat → Nat := fun v =>
  if h : ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]! then
    lab[h.choose + 1]!
  else if h : ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]! then
    lab[h.choose]!
  else v

/-- Two closure pairs sharing a first member coincide. -/
private theorem first_eq (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c]! = lab[c']!) : c = c' := by
  have h1 := cells_bound (by omega) hend _ hcell
  have h2 := cells_bound (by omega) hend _ hcell'
  have h1' : c + 1 < ptn.size := h1
  have h2' : c' + 1 < ptn.size := h2
  exact hinj c c' (by omega) (by omega) hv

/-- Two closure pairs sharing a second member coincide. -/
private theorem second_eq (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c + 1]! = lab[c' + 1]!) : c = c' := by
  have h1 : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have h2 : (c', c' + 1).2 < ptn.size :=
    cells_bound (by omega) hend _ hcell'
  have := hinj (c + 1) (c' + 1) (by omega) (by omega) hv
  omega

/-- A first member of one pair cell is never the second member of
another. -/
private theorem first_ne_second (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c c' : Nat} (hcell : (c, c + 1) ∈ cells ptn level n)
    (hcell' : (c', c' + 1) ∈ cells ptn level n)
    (hv : lab[c]! = lab[c' + 1]!) : False := by
  have h1 : (c, c + 1).2 < ptn.size := cells_bound (by omega) hend _ hcell
  have h2 : (c', c' + 1).2 < ptn.size :=
    cells_bound (by omega) hend _ hcell'
  have heq := hinj c (c' + 1) (by omega) (by omega) hv
  exact pair_start_ne_second (by omega) hend hcell hcell' heq

/-- The flip carries a closure pair's first member to its second. -/
theorem pairFlip_first (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c : Nat} (hr : PairReach ctx lab ptn level t c)
    (hcell : (c, c + 1) ∈ cells ptn level n) :
    pairFlip ctx lab ptn level t lab[c]! = lab[c + 1]! := by
  have hex : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧ lab[c]! = lab[c']! :=
    ⟨c, hr, hcell, rfl⟩
  obtain ⟨-, hcell', hv⟩ := hex.choose_spec
  have hcc : hex.choose = c :=
    (first_eq hpsz hend hinj hcell hcell' hv).symm
  show (if h : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧ lab[c]! = lab[c']! then
      lab[h.choose + 1]!
    else _) = _
  rw [dite_eq_left hex]
  show lab[hex.choose + 1]! = lab[c + 1]!
  rw [hcc]

/-- The flip carries a closure pair's second member to its first. -/
theorem pairFlip_second (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {c : Nat} (hr : PairReach ctx lab ptn level t c)
    (hcell : (c, c + 1) ∈ cells ptn level n) :
    pairFlip ctx lab ptn level t lab[c + 1]! = lab[c]! := by
  have hno : ¬ ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c']! := by
    rintro ⟨c', -, hcell', hv⟩
    exact first_ne_second hpsz hend hinj hcell' hcell hv.symm
  have hex : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c' + 1]! :=
    ⟨c, hr, hcell, rfl⟩
  obtain ⟨-, hcell', hv⟩ := hex.choose_spec
  have hcc : hex.choose = c :=
    (second_eq hpsz hend hinj hcell hcell' hv).symm
  show (if _ : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c']! then _
    else if h : ∃ c', PairReach ctx lab ptn level t c' ∧
      (c', c' + 1) ∈ cells ptn level n ∧
        lab[c + 1]! = lab[c' + 1]! then lab[h.choose]!
    else _) = _
  rw [dite_eq_right hno, dite_eq_left hex]
  show lab[hex.choose]! = lab[c]!
  rw [hcc]

/-- The flip fixes every vertex that is not a closure-pair member. -/
theorem pairFlip_fix {v : Nat}
    (hnone : ∀ c, PairReach ctx lab ptn level t c →
      (c, c + 1) ∈ cells ptn level n →
        v ≠ lab[c]! ∧ v ≠ lab[c + 1]!) :
    pairFlip ctx lab ptn level t v = v := by
  have h1 : ¬ ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]! := by
    rintro ⟨c, hr, hcell, hv⟩
    exact (hnone c hr hcell).1 hv
  have h2 : ¬ ∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]! := by
    rintro ⟨c, hr, hcell, hv⟩
    exact (hnone c hr hcell).2 hv
  show (if _ : _ then _ else if _ : _ then _ else v) = v
  rw [dite_eq_right h1, dite_eq_right h2]

/-- The flip is bounded on the vertex range. -/
theorem pairFlip_lt (hpsz : ptn.size = n)
    (hlsz : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hlb : LabOk lab n)
    {v : Nat} (hv : v < n) :
    pairFlip ctx lab ptn level t v < n := by
  show (if _ : _ then _ else if _ : _ then _ else v) < n
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
theorem pairFlip_invol (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {v : Nat} :
    pairFlip ctx lab ptn level t
      (pairFlip ctx lab ptn level t v) = v := by
  rcases Decidable.em (∃ c, PairReach ctx lab ptn level t c ∧
      (c, c + 1) ∈ cells ptn level n ∧ v = lab[c]!) with h1 | h1
  · obtain ⟨c, hr, hcell, rfl⟩ := h1
    rw [pairFlip_first hpsz hend hinj hr hcell,
      pairFlip_second hpsz hend hinj hr hcell]
  · rcases Decidable.em (∃ c, PairReach ctx lab ptn level t c ∧
        (c, c + 1) ∈ cells ptn level n ∧ v = lab[c + 1]!) with
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
theorem pairFlip_fix_cell (hpsz : ptn.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level) (hinj : LabInj lab n)
    {q : Nat × Nat} (hq : q ∈ cells ptn level n)
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

/-- The flip data at a pair target: a row-preserving self-symmetry of
the node carrying one child's individualized vertex to the other's. -/
theorem pair_flip_data {st : RefineSt n} {level tc : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hP : (tc, tc + 1) ∈ cells st.ptn level n)
    (hOdd : ∀ q ∈ cells st.ptn level n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1)
    {a b : Nat} (ha : a < 2) (hb : b < 2) (hab : a ≠ b) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + b]! = σ.toFun st.lab[tc + a]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinjr : ∀ i j, i < n → j < n →
      st.lab[i]! = st.lab[j]! → i = j := hIt.inj
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hfb : ∀ v, v < n →
      pairFlip ctx st.lab st.ptn level tc v < n := fun v hv =>
    pairFlip_lt hpsz hlsz hend hIt.ok.labOk hv
  have hinvol : ∀ v, v < n →
      pairFlip ctx st.lab st.ptn level tc
        (pairFlip ctx st.lab st.ptn level tc v) = v := fun v _ =>
    pairFlip_invol hpsz hend hIt.inj
  have hSpair : ∀ p ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 → p.2 = p.1 + 1 := by
    intro p hp hS
    have hcell := pairReach_pair hP hS
    have hpm : (p.1, p.2) ∈ cells st.ptn level n := hp
    exact cells_eq_of_start (by omega) hend hpm hcell
  have hSswap : ∀ p ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 →
      pairFlip ctx st.lab st.ptn level tc st.lab[p.1]! =
          st.lab[p.1 + 1]! ∧
        pairFlip ctx st.lab st.ptn level tc st.lab[p.1 + 1]! =
          st.lab[p.1]! := by
    intro p hp hS
    have hcell := pairReach_pair hP hS
    exact ⟨pairFlip_first hpsz hend hIt.inj hS hcell,
      pairFlip_second hpsz hend hIt.inj hS hcell⟩
  have hSfix : ∀ p ∈ cells st.ptn level n,
      ¬ PairReach ctx st.lab st.ptn level tc p.1 →
      ∀ o, o < p.2 + 1 - p.1 →
        pairFlip ctx st.lab st.ptn level tc st.lab[p.1 + o]! =
          st.lab[p.1 + o]! := by
    intro p hp hS o ho
    exact pairFlip_fix_cell hpsz hend hIt.inj hp hS ho
  have hSclosed : ∀ p ∈ cells st.ptn level n,
      ∀ q ∈ cells st.ptn level n,
      PairReach ctx st.lab st.ptn level tc p.1 → q.2 = q.1 + 1 →
      PairMatch ctx.g st.lab[p.1]! st.lab[p.1 + 1]!
        st.lab[q.1]! st.lab[q.1 + 1]! →
      PairReach ctx st.lab st.ptn level tc q.1 := by
    intro p hp q hq hS hq2 hm
    have hqm : (q.1, q.1 + 1) ∈ cells st.ptn level n := by
      have hqm' : (q.1, q.2) ∈ cells st.ptn level n := hq
      rw [hq2] at hqm'
      exact hqm'
    exact PairReach.step hS (pairReach_pair hP hS) hqm hm
  have hsurj := labInj_surj
    (by rw [hlsz]; exact Nat.le_refl _ : n ≤ st.lab.size)
    hIt.ok.labOk hIt.inj
  have hrows := flip_rows hE hpsz hend hinjr hlb hsurj hsymm
    hloop hfb hinvol hSpair hSswap hSfix hSclosed hOdd
  have hgmap := rowsMap_of_flip_rows hgsz hfb hinvol hrows
  have hsp := stPerm_self_setwise hIt.ok hIt.inj hfb hinvol (by
    intro p hp o ho
    by_cases hs : PairReach ctx st.lab st.ptn level tc p.1
    · have he := hSpair p hp hs
      obtain ⟨hf1, hf2⟩ := hSswap p hp hs
      by_cases hz : o = 0
      · subst o
        exact ⟨1, by omega, by simpa only [Nat.add_zero] using hf1⟩
      · have ho1 : o = 1 := by omega
        subst o
        exact ⟨0, by omega, by simpa only [Nat.add_zero] using hf2⟩
    · exact ⟨o, ho, hSfix p hp hs o ho⟩)
  have hbd : (tc, tc + 1).2 < st.ptn.size :=
    cells_bound (by omega) hend _ hP
  have hbase : PairReach ctx st.lab st.ptn level tc tc :=
    PairReach.base
  have hvv : st.lab[tc + b]! =
      (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
        hfb hinvol).toFun st.lab[tc + a]! := by
    have hat : ∀ i, i < n →
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[i]! =
          pairFlip ctx st.lab st.ptn level tc st.lab[i]! := fun i hi =>
      renamingOfFlip_at hfb hinvol (hlb i hi)
    rcases Decidable.em (a = 0) with rfl | ha0
    · have hb1 : b = 1 := by omega
      subst hb1
      show st.lab[tc + 1]! =
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[tc]!
      rw [hat tc (by rw [hpsz] at hbd; omega),
        pairFlip_first hpsz hend hIt.inj hbase hP]
    · have ha1 : a = 1 := by omega
      have hb0 : b = 0 := by omega
      subst ha1; subst hb0
      show st.lab[tc]! =
        (renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
          hfb hinvol).toFun st.lab[tc + 1]!
      rw [hat (tc + 1) (by rw [hpsz] at hbd; omega),
        pairFlip_second hpsz hend hIt.inj hbase hP]
  exact ⟨renamingOfFlip (pairFlip ctx st.lab st.ptn level tc) n
    hfb hinvol, hgmap, hsp, hvv⟩

end Hex.GraphIso.Nauty

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

theorem flip_data_of_bits {st : RefineSt n} {level : Nat}
    {f : Nat → Nat}
    (hIt : IterOk ctx level st) (hgsz : ctx.g.size = n)
    (hfb : ∀ w, w < n → f w < n)
    (hinvol : ∀ w, w < n → f (f w) = w)
    (hbits : ∀ z z', z < n → z' < n →
      (ctx.g[f z]!).mem (f z') = (ctx.g[z]!).mem z')
    (hset : ∀ p ∈ cells st.ptn level n, ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        f st.lab[p.1 + o]! = st.lab[p.1 + o']!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      ∀ i, i < n → σ.toFun st.lab[i]! = f st.lab[i]! := by
  refine ⟨renamingOfFlip f n hfb hinvol, ?_, ?_, ?_⟩
  · exact rowsMap_of_flip_rows hgsz hfb hinvol
      (rows_of_bits hfb hinvol hbits)
  · exact stPerm_self_setwise hIt.ok hIt.inj hfb hinvol hset
  · intro i hi
    exact renamingOfFlip_at hfb hinvol
      (hIt.ok.labOk i (by rw [hIt.ok.labSize]; omega))

private theorem mem_erase_nodup :
    ∀ {l : List Nat}, l.Nodup → ∀ a w,
      (w ∈ l.erase a ↔ w ∈ l ∧ w ≠ a)
  | [], _, a, w => by simp
  | b :: t, hnd, a, w => by
    rw [List.nodup_cons] at hnd
    rcases Decidable.em (b = a) with rfl | hba
    · rw [List.erase_cons_head]
      constructor
      · intro hw
        exact ⟨List.mem_cons_of_mem _ hw,
          fun hcon => hnd.1 (hcon ▸ hw)⟩
      · rintro ⟨hw, hne⟩
        rcases List.mem_cons.mp hw with rfl | hmem
        · exact absurd rfl hne
        · exact hmem
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hba)]
      rw [List.mem_cons, List.mem_cons,
        mem_erase_nodup hnd.2 a w]
      constructor
      · rintro (rfl | ⟨hw, hne⟩)
        · exact ⟨Or.inl rfl, hba⟩
        · exact ⟨Or.inr hw, hne⟩
      · rintro ⟨rfl | hw, hne⟩
        · exact Or.inl rfl
        · exact Or.inr ⟨hw, hne⟩

/-- The count of one row into a singleton cell is its bit there, so
equitability makes the bits of all members of a cell agree at every
singleton-cell vertex. -/
theorem cell_const_into_singleton {lab ptn : Array Nat}
    {level : Nat}
    (hE : Equitable ctx level lab ptn)
    {tc te : Nat} (hC : (tc, te) ∈ cells ptn level n)
    {s : Nat} (hS : (s, s) ∈ cells ptn level n)
    {o o' : Nat} (ho : o ≤ te - tc) (ho' : o' ≤ te - tc) :
    (ctx.g[lab[tc + o]!]!).mem lab[s]! =
      (ctx.g[lab[tc + o']!]!).mem lab[s]! := by
  have hle : tc ≤ te := cells_le _ hC
  have h := hE _ hC _ hS o o' (by omega) (by omega)
  rw [worksetOf_singleton, VSet.cardInter_singleton,
    VSet.cardInter_singleton] at h
  rcases hb : (ctx.g[lab[tc + o]!]!).mem lab[s]! with _ | _ <;>
    rcases hb' : (ctx.g[lab[tc + o']!]!).mem lab[s]! with _ | _ <;>
      rw [hb, hb'] at h <;> simp_all

section OneCell

variable {st : RefineSt n} {level tc te oU oV : Nat}

/-- The transposition route: every other window member has equal bits
at the two swapped ones. -/
private theorem oneCell_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, te) →
      q.2 = q.1)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hAllEq : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV →
      (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oV]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have huv : st.lab[tc + oU]! ≠ st.lab[tc + oV]! := by
    intro hcon
    have := hinj (tc + oU) (tc + oV) (by omega) (by omega) hcon
    omega
  -- every other reachable vertex has equal bits at the pair
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, te)) with rfl | hpC
    · -- j sits in the target window
      have hw : j - tc ≤ te - tc := by
        have h2 : j ≤ te := hj2
        omega
      have hwu : j - tc ≠ oU := by
        intro hcon
        refine hzu ?_
        have h1 : tc ≤ j := hj1
        have : j = tc + oU := by omega
        rw [this]
      have hwv : j - tc ≠ oV := by
        intro hcon
        refine hzv ?_
        have h1 : tc ≤ j := hj1
        have : j = tc + oV := by omega
        rw [this]
      have h := hAllEq (j - tc) hw hwu hwv
      have h1 : tc ≤ j := hj1
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    · -- j sits in a singleton cell
      have hps : p.2 = p.1 := hsing p hp hpC
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨pa, pb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      have hconst := cell_const_into_singleton hE hC hpmem hoU hoV
      rw [← hjp] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at hconst
      exact hconst
  -- the swap permutes every cell within itself
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    exact sw1_cells hIt.ok hIt.inj hC hoU hoV hne
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[tc + oU]! st.lab[tc + oV]!) hIt hgsz
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw1_u]

set_option maxHeartbeats 4000000 in
/-- The crossed-pair route: the two chosen members swap together with
the differ pair, every other window member having equal bits at both
pairs. -/
private theorem oneCell_sw2 {wa wb : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, te) →
      q.2 = q.1)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hwa : wa ≤ te - tc) (hwb : wb ≤ te - tc) (hab : wa ≠ wb)
    (hau : wa ≠ oU) (hav : wa ≠ oV) (hbu : wb ≠ oU) (hbv : wb ≠ oV)
    (htau : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oU]! =
      true)
    (htav : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oV]! =
      false)
    (htbu : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oU]! =
      false)
    (htbv : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oV]! =
      true)
    (hRestEq : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV → w ≠ wa → w ≠ wb →
      (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oV]!)
    (hWfix : ∀ w, w ≤ te - tc → w ≠ oU → w ≠ oV → w ≠ wa → w ≠ wb →
      (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + wa]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + wb]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hvne : ∀ w w' : Nat, w ≤ te - tc → w' ≤ te - tc → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hOk : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + wa]! st.lab[tc + wb]! :=
    ⟨hlb _ (by omega), hlb _ (by omega), hlb _ (by omega),
      hlb _ (by omega), hvne _ _ hoU hoV hne,
      hvne _ _ hoU hwa (fun h => hau h.symm),
      hvne _ _ hoU hwb (fun h => hbu h.symm),
      hvne _ _ hoV hwa (fun h => hav h.symm),
      hvne _ _ hoV hwb (fun h => hbv h.symm),
      hvne _ _ hwa hwb hab⟩
  obtain ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩ := hOk
  have hOk2 : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + wa]! st.lab[tc + wb]! :=
    ⟨hun, hvn, hxn, hyn, huv, hux, huy, hvx, hvy, hxy⟩
  -- fixed vertices have equal bits at both pairs
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + wa]! →
      z ≠ st.lab[tc + wb]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[tc + wa]! =
        (ctx.g[z]!).mem st.lab[tc + wb]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, te)) with rfl | hpC
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ te := hj2
      have hw : j - tc ≤ te - tc := by omega
      have hwneq : ∀ w' : Nat, w' ≤ te - tc →
          st.lab[j]! ≠ st.lab[tc + w']! → j - tc ≠ w' := by
        intro w' hw' hne' hcon
        exact hne' (by rw [show j = tc + w' by omega])
      have hwu := hwneq oU hoU hzu
      have hwv := hwneq oV hoV hzv
      have hwx := hwneq wa hwa hzx
      have hwy := hwneq wb hwb hzy
      have hr := hRestEq (j - tc) hw hwu hwv hwx hwy
      have hf := hWfix (j - tc) hw hwu hwv hwx hwy
      rw [show tc + (j - tc) = j by omega] at hr hf
      exact ⟨hr, hf⟩
    · have hps : p.2 = p.1 := hsing p hp hpC
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨pa, pb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      constructor
      · have hconst := cell_const_into_singleton hE hC hpmem hoU hoV
        rw [← hjp] at hconst
        rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
        rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at hconst
        rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at hconst
        exact hconst
      · have hconst := cell_const_into_singleton hE hC hpmem hwa hwb
        rw [← hjp] at hconst
        rw [hsymm _ _ hz hxn, hsymm _ _ hz hyn]
        rw [hsymm _ _ hxn hz, hsymm _ _ hyn hz] at hconst
        rw [hsymm _ _ hz hxn, hsymm _ _ hz hyn] at hconst
        exact hconst
  -- the cross bits between the two pairs match diagonally
  have hc1 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + wa]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + wb]! := by
    rw [hsymm _ _ hun hxn, hsymm _ _ hvn hyn, htau, htbv]
  have hc2 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + wb]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + wa]! := by
    rw [hsymm _ _ hun hyn, hsymm _ _ hvn hxn, htbu, htav]
  -- the double swap permutes every cell within itself
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + wa]!
          st.lab[tc + wb]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    exact sw2_cells hOk2 (sw1_cells hIt.ok hIt.inj hC hoU hoV hne)
      (sw1_cells hIt.ok hIt.inj hC hwa hwb hab)
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + wa]!
      st.lab[tc + wb]!) hIt hgsz
    (sw2_lt hOk2) (fun w _ => sw2_invol hOk2 w)
    (sw2_bits hsymm hloop hOk2 hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

private theorem nodup_erase :
    ∀ {l : List Nat}, l.Nodup → ∀ a, (l.erase a).Nodup
  | [], _, _ => by simp
  | b :: t, hnd, a => by
    rw [List.nodup_cons] at hnd
    rcases Decidable.em (b = a) with rfl | hba
    · rw [List.erase_cons_head]
      exact hnd.2
    · rw [List.erase_cons_tail (by simp only [beq_iff_eq]; exact hba),
        List.nodup_cons]
      refine ⟨fun hmem => ?_, nodup_erase hnd.2 a⟩
      exact hnd.1 ((mem_erase_nodup hnd.2 a b).mp hmem).1

private theorem nodup_subset_length :
    ∀ (l r : List Nat), l.Nodup → (∀ x ∈ l, x ∈ r) →
      l.length ≤ r.length
  | [], r, _, _ => by simp
  | a :: t, r, hnd, hsub => by
    rw [List.nodup_cons] at hnd
    have ha : a ∈ r := hsub a List.mem_cons_self
    have hlen := (List.perm_cons_erase ha).length_eq
    have hsub' : ∀ x ∈ t, x ∈ r.erase a := fun x hx =>
      (List.mem_erase_of_ne (fun hcon => hnd.1
        (by rw [← hcon]; exact hx))).mpr
        (hsub x (List.mem_cons_of_mem _ hx))
    have h := nodup_subset_length t (r.erase a) hnd.2 hsub'
    simp only [List.length_cons] at hlen ⊢
    omega

set_option maxHeartbeats 1000000 in
/-- In a five-member window, the member outside a crossed pair has
equal bits at the pair: the pair's two row sums expand over the five
named offsets, the crossed types cancel, and the shared internal bit
cancels by symmetry. -/
private theorem oneCell_wfix {wa wb wf : Nat}
    (hIt : IterOk ctx level st)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hm : te + 1 - tc = 5)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV)
    (hwa : wa ≤ te - tc) (hwb : wb ≤ te - tc) (hwf : wf ≤ te - tc)
    (hab : wa ≠ wb) (haf : wa ≠ wf) (hbf : wb ≠ wf)
    (hau : wa ≠ oU) (hav : wa ≠ oV) (hbu : wb ≠ oU) (hbv : wb ≠ oV)
    (hfu : wf ≠ oU) (hfv : wf ≠ oV)
    (htau : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oU]! =
      true)
    (htav : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oV]! =
      false)
    (htbu : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oU]! =
      false)
    (htbv : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oV]! =
      true) :
    (ctx.g[st.lab[tc + wf]!]!).mem st.lab[tc + wa]! =
      (ctx.g[st.lab[tc + wf]!]!).mem st.lab[tc + wb]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hnd : ([oU, oV, wa, wb, wf] : List Nat).Nodup := by
    simp only [List.nodup_cons, List.mem_cons,
      List.not_mem_nil, List.nodup_nil]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rintro (h | h | h | h | h) <;> omega
    · rintro (h | h | h | h) <;> omega
    · rintro (h | h | h) <;> omega
    · rintro (h | h) <;> omega
    · simp
  have hbd : ∀ x ∈ ([oU, oV, wa, wb, wf] : List Nat),
      x < te + 1 - tc := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have hxf : x = wf := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  have hcic : ∀ o : Nat, o ≤ te - tc →
      (worksetOf n st.lab tc te).cardInter
          ctx.g[st.lab[tc + o]!]! =
        ((List.range (te + 1 - tc)).map fun w =>
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w]!).sum := by
    intro o ho
    exact count_into_cell hpsz hend hinj hC
  have hrow := hE _ hC _ hC wa wb (by omega) (by omega)
  rw [hcic wa hwa, hcic wb hwb, hm] at hrow
  rw [sum_range_of_distinct _ (by simp) hnd
      (by rw [← hm]; exact hbd),
    sum_range_of_distinct _ (by simp) hnd
      (by rw [← hm]; exact hbd)] at hrow
  simp only [List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hrow
  have hloopa : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wa]! =
      0 := bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hloopb : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wb]! =
      0 := bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsymab : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wb]! =
      bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wa]! :=
    bitCnt_inj.mpr (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have h1 : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + oU]! = 1 :=
    bitCnt_eq_one.mpr htau
  have h2 : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + oV]! = 0 :=
    bitCnt_eq_zero.mpr htav
  have h3 : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + oU]! = 0 :=
    bitCnt_eq_zero.mpr htbu
  have h4 : bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + oV]! = 1 :=
    bitCnt_eq_one.mpr htbv
  have hkey : bitCnt ctx.g[st.lab[tc + wa]!]! st.lab[tc + wf]! =
      bitCnt ctx.g[st.lab[tc + wb]!]! st.lab[tc + wf]! := by
    omega
  have hbit := bitCnt_inj.mp hkey
  rw [hsymm _ _ (hlb (tc + wf) (by omega)) (hlb (tc + wa) (by omega)),
    hsymm _ _ (hlb (tc + wf) (by omega)) (hlb (tc + wb) (by omega))]
  exact hbit

set_option maxHeartbeats 2000000 in
/-- The flip data at a nontrivial cell of size at most five whose
companions are all singletons: the differ classification of the two
chosen members is forced by the window row sums, and the flip is the
bare transposition or the crossed double swap. -/
theorem oneCell_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, te) ∈ cells st.ptn level n)
    (hm : te + 1 - tc ≤ 5)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, te) →
      q.2 = q.1)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hcle : tc ≤ te := cells_le _ hC
  have hten : te < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  -- the window row sums
  have hcic : ∀ o : Nat, o ≤ te - tc →
      (worksetOf n st.lab tc te).cardInter
          ctx.g[st.lab[tc + o]!]! =
        ((List.range (te + 1 - tc)).map fun w =>
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w]!).sum := by
    intro o ho
    exact count_into_cell hpsz hend hinj hC
  have hrow := hE _ hC _ hC oU oV (by omega) (by omega)
  rw [hcic oU hoU, hcic oV hoV] at hrow
  -- the remaining window offsets
  have hnd1 := nodup_erase (List.nodup_range (n := te + 1 - tc)) oU
  have hndL := nodup_erase hnd1 oV
  have hoUm : oU ∈ List.range (te + 1 - tc) :=
    List.mem_range.mpr (by omega)
  have hoVm : oV ∈ (List.range (te + 1 - tc)).erase oU :=
    (mem_erase_nodup (List.nodup_range) oU oV).mpr
      ⟨List.mem_range.mpr (by omega), fun h => hne h.symm⟩
  have hmemL : ∀ w,
      w ∈ ((List.range (te + 1 - tc)).erase oU).erase oV ↔
        (w < te + 1 - tc ∧ w ≠ oU ∧ w ≠ oV) := by
    intro w
    rw [mem_erase_nodup hnd1 oV w,
      mem_erase_nodup (List.nodup_range) oU w, List.mem_range]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨⟨h1, h2⟩, h3⟩
  have hlenL :
      (((List.range (te + 1 - tc)).erase oU).erase oV).length + 2 =
        te + 1 - tc := by
    have l1 := (List.perm_cons_erase hoUm).length_eq
    have l2 := (List.perm_cons_erase hoVm).length_eq
    rw [List.length_range] at l1
    simp only [List.length_cons] at l1 l2
    omega
  -- split the two row sums at the chosen offsets
  have hsplit : ∀ F : Nat → Nat,
      ((List.range (te + 1 - tc)).map F).sum =
        F oU + F oV +
          (((((List.range (te + 1 - tc)).erase oU).erase oV)).map
            F).sum := by
    intro F
    have e1 := sum_of_perm ((List.perm_cons_erase hoUm).map F)
    have e2 := sum_of_perm ((List.perm_cons_erase hoVm).map F)
    simp only [List.map_cons, List.sum_cons] at e1 e2
    omega
  rw [hsplit, hsplit] at hrow
  have hlu : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + oU]! = 0 :=
    bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hlv : bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + oV]! = 0 :=
    bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsuv : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + oV]! =
      bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + oU]! :=
    bitCnt_inj.mpr (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have hrest :
      (((((List.range (te + 1 - tc)).erase oU).erase oV)).map
          fun w => bitCnt ctx.g[st.lab[tc + oU]!]!
            st.lab[tc + w]!).sum =
      (((((List.range (te + 1 - tc)).erase oU).erase oV)).map
          fun w => bitCnt ctx.g[st.lab[tc + oV]!]!
            st.lab[tc + w]!).sum := by
    omega
  have hcount :
      (((List.range (te + 1 - tc)).erase oU).erase oV).countP
          (fun w => (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + w]!) =
        (((List.range (te + 1 - tc)).erase oU).erase oV).countP
          (fun w => (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + w]!) := by
    have he :
        (((((List.range (te + 1 - tc)).erase oU).erase oV).map
          (fun w => st.lab[tc + w]!))).countP (ctx.g[st.lab[tc + oU]!]!).mem =
        (((((List.range (te + 1 - tc)).erase oU).erase oV).map
          (fun w => st.lab[tc + w]!))).countP (ctx.g[st.lab[tc + oV]!]!).mem := by
      rw [countP_bits, countP_bits]
      simpa only [List.map_map, Function.comp_def] using hrest
    simpa only [List.countP_map, Function.comp_def] using he
  rcases differ_pair _ _ (by omega) hcount with heq |
      ⟨wa, hwa, wb, hwb, hab, hAu, hAv, hBu, hBv, hfix⟩
  · refine oneCell_sw1 hIt hgsz hsymm hloop hE hC hsing hoU hoV hne ?_
    intro w hw hwu hwv
    rw [hsymm _ _ (hlb (tc + w) (by omega)) (hlb (tc + oU) (by omega)),
      hsymm _ _ (hlb (tc + w) (by omega)) (hlb (tc + oV) (by omega))]
    exact heq w ((hmemL w).mpr ⟨by omega, hwu, hwv⟩)
  · obtain ⟨ha, hau, hav⟩ := (hmemL wa).mp hwa
    obtain ⟨hb, hbu, hbv⟩ := (hmemL wb).mp hwb
    have htau : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oU]! = true := by
      rw [hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega))]
      exact hAu
    have htav : (ctx.g[st.lab[tc + wa]!]!).mem st.lab[tc + oV]! = false := by
      rw [hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega))]
      exact hAv
    have htbu : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oU]! = false := by
      rw [hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega))]
      exact hBu
    have htbv : (ctx.g[st.lab[tc + wb]!]!).mem st.lab[tc + oV]! = true := by
      rw [hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega))]
      exact hBv
    refine oneCell_sw2 hIt hgsz hsymm hloop hE hC hsing hoU hoV hne
      (by omega) (by omega) hab hau hav hbu hbv htau htav htbu htbv ?_ ?_
    · intro w hw hwu hwv hwa hwb
      rw [hsymm _ _ (hlb (tc + w) (by omega)) (hlb (tc + oU) (by omega)),
        hsymm _ _ (hlb (tc + w) (by omega)) (hlb (tc + oV) (by omega))]
      exact hfix w ((hmemL w).mpr ⟨by omega, hwu, hwv⟩) hwa hwb
    · intro w hw hwu hwv hwa hwb
      have hnd : ([oU, oV, wa, wb, w] : List Nat).Nodup := by
        simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, List.nodup_nil]
        grind
      have hsub : ∀ x ∈ ([oU, oV, wa, wb, w] : List Nat),
          x ∈ List.range (te + 1 - tc) := by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil] at hx
        apply List.mem_range.mpr
        grind
      have hlen := nodup_subset_length _ _ hnd hsub
      simp only [List.length_cons, List.length_nil, List.length_range] at hlen
      exact oneCell_wfix hIt hsymm hloop hE hC (by omega) hoU hoV hne
        (by omega) (by omega) hw hab (Ne.symm hwa) (Ne.symm hwb)
        hau hav hbu hbv hwu hwv htau htav htbu htbv

end OneCell

end Hex.GraphIso.Nauty

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

section TwoTriple

variable {st : RefineSt n} {level tc d2 oU oV : Nat}

set_option maxHeartbeats 4000000 in
/-- The cross-cell double swap: the two chosen members of the target
triple swap together with their partners in the other triple. -/
theorem twoTriple_sw2 {pa pb : Nat}
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV)
    (hpa : pa ≤ 2) (hpb : pb ≤ 2) (hpab : pa ≠ pb)
    (hfixT1 : ∀ w, w ≤ 2 → w ≠ oU → w ≠ oV →
      ((ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[tc + oV]!) ∧
      ((ctx.g[st.lab[tc + w]!]!).mem st.lab[d2 + pa]! =
        (ctx.g[st.lab[tc + w]!]!).mem st.lab[d2 + pb]!))
    (hfixT2 : ∀ w, w ≤ 2 → w ≠ pa → w ≠ pb →
      ((ctx.g[st.lab[d2 + w]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[d2 + w]!]!).mem st.lab[tc + oV]!) ∧
      ((ctx.g[st.lab[d2 + w]!]!).mem st.lab[d2 + pa]! =
        (ctx.g[st.lab[d2 + w]!]!).mem st.lab[d2 + pb]!))
    (hc1 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + pa]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + pb]!)
    (hc2 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + pb]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + pa]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have ht1n : tc + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT1
    rw [hpsz] at this
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT2
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  -- the two windows are disjoint
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT1
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT2
  rw [show tc + 2 + 1 - tc = 3 by omega] at hI1
  rw [show d2 + 2 + 1 - d2 = 3 by omega] at hI2
  have hdisj : tc + 3 ≤ d2 ∨ d2 + 3 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hT12
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 →
      st.lab[tc + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hcon
    have := hinj (tc + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hin1 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hin2 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[d2 + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (d2 + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hOk : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[d2 + pa]! st.lab[d2 + pb]! :=
    ⟨hlb _ (by omega), hlb _ (by omega), hlb _ (by omega),
      hlb _ (by omega), hin1 _ _ hoU hoV hne,
      hcross _ _ hoU hpa, hcross _ _ hoU hpb,
      hcross _ _ hoV hpa, hcross _ _ hoV hpb,
      hin2 _ _ hpa hpb hpab⟩
  -- fixed vertices have equal bits at both pairs
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[d2 + pa]! →
      z ≠ st.lab[d2 + pb]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[d2 + pa]! =
        (ctx.g[z]!).mem st.lab[d2 + pb]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 2)) with rfl | hpT1
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ tc + 2 := hj2
      have hw : j - tc ≤ 2 := by omega
      have hwu : j - tc ≠ oU := fun hcon =>
        hzu (by rw [show j = tc + oU by omega])
      have hwv : j - tc ≠ oV := fun hcon =>
        hzv (by rw [show j = tc + oV by omega])
      have h := hfixT1 (j - tc) hw hwu hwv
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    rcases Decidable.em (p = (d2, d2 + 2)) with rfl | hpT2
    · have h1 : d2 ≤ j := hj1
      have h2 : j ≤ d2 + 2 := hj2
      have hw : j - d2 ≤ 2 := by omega
      have hwa : j - d2 ≠ pa := fun hcon =>
        hzx (by rw [show j = d2 + pa by omega])
      have hwb : j - d2 ≠ pb := fun hcon =>
        hzy (by rw [show j = d2 + pb by omega])
      have h := hfixT2 (j - d2) hw hwa hwb
      rw [show d2 + (j - d2) = j by omega] at h
      exact h
    · have hps : p.2 = p.1 := hsing p hp hpT1 hpT2
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      constructor
      · have hconst := cell_const_into_singleton hE hT1 hpmem
          (o := oU) (o' := oV) (by omega) (by omega)
        rw [← hjp] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))]
        rw [hsymm _ _ (hlb (tc + oU) (by omega)) hz,
          hsymm _ _ (hlb (tc + oV) (by omega)) hz] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))] at hconst
        exact hconst
      · have hconst := cell_const_into_singleton hE hT2 hpmem
          (o := pa) (o' := pb) (by omega) (by omega)
        rw [← hjp] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))]
        rw [hsymm _ _ (hlb (d2 + pa) (by omega)) hz,
          hsymm _ _ (hlb (d2 + pb) (by omega)) hz] at hconst
        rw [hsymm _ _ hz (hlb _ (by omega)),
          hsymm _ _ hz (hlb _ (by omega))] at hconst
        exact hconst
  -- the swap permutes both triples within themselves
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[d2 + pa]!
          st.lab[d2 + pb]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    exact sw2_cells hOk (sw1_cells hIt.ok hIt.inj hT1 (by omega) (by omega) hne)
      (sw1_cells hIt.ok hIt.inj hT2 (by omega) (by omega) hpab)
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[d2 + pa]!
      st.lab[d2 + pb]!) hIt hgsz
    (sw2_lt hOk) (fun w _ => sw2_invol hOk w)
    (sw2_bits hsymm hloop hOk hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

private theorem sum3_eq_of_cover {f : Nat → Nat} {a b c : Nat}
    (ha : a ≤ 2) (hb : b ≤ 2) (hc : c ≤ 2)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    f 0 + f 1 + f 2 = f a + f b + f c := by
  have h0 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
  have h1 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  have h2 : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    rcases h2 with rfl | rfl | rfl <;> omega

set_option maxHeartbeats 4000000 in
/-- The uniform cross-count route: the other triple's bits do not
distinguish the two chosen members, so the bare transposition
suffices. -/
theorem twoTriple_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV)
    (huni : ∀ q, q ≤ 2 →
      (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + q]! =
        (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + q]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have ht1n : tc + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT1
    rw [hpsz] at this
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hT2
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hinj := hIt.inj
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT1
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hT2
  rw [show tc + 2 + 1 - tc = 3 by omega] at hI1
  rw [show d2 + 2 + 1 - d2 = 3 by omega] at hI2
  have hdisj : tc + 3 ≤ d2 ∨ d2 + 3 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hT12
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 →
      st.lab[tc + w]! ≠ st.lab[d2 + w']! := by
    intro w w' hw hw' hcon
    have := hinj (tc + w) (d2 + w') (by omega) (by omega) hcon
    omega
  have hin1 : ∀ w w' : Nat, w ≤ 2 → w' ≤ 2 → w ≠ w' →
      st.lab[tc + w]! ≠ st.lab[tc + w']! := by
    intro w w' hw hw' hne' hcon
    have := hinj (tc + w) (tc + w') (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have huv := hin1 _ _ hoU hoV hne
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 2)) with rfl | hpT1
    · have h1 : tc ≤ j := hj1
      have h2 : j ≤ tc + 2 := hj2
      have hw : j - tc ≤ 2 := by omega
      have hwu : j - tc ≠ oU := fun hcon =>
        hzu (by rw [show j = tc + oU by omega])
      have hwv : j - tc ≠ oV := fun hcon =>
        hzv (by rw [show j = tc + oV by omega])
      have h := triple_internal hE hpsz hend hinj hlb hsymm hloop
        hT1 (j - tc) oU (j - tc) oV (by omega) (by omega) (by omega)
        (by omega) hwu hwv
      rw [show tc + (j - tc) = j by omega] at h
      exact h
    rcases Decidable.em (p = (d2, d2 + 2)) with rfl | hpT2
    · have h1 : d2 ≤ j := hj1
      have h2 : j ≤ d2 + 2 := hj2
      have hw : j - d2 ≤ 2 := by omega
      have h := huni (j - d2) hw
      rw [show d2 + (j - d2) = j by omega] at h
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at h
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at h
      exact h
    · have hps : p.2 = p.1 := hsing p hp hpT1 hpT2
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← this]
        exact hp
      have hconst := cell_const_into_singleton hE hT1 hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      rw [← hjp] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn]
      rw [hsymm _ _ hun hz, hsymm _ _ hvn hz] at hconst
      rw [hsymm _ _ hz hun, hsymm _ _ hz hvn] at hconst
      exact hconst
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    exact sw1_cells hIt.ok hIt.inj hT1 (by omega) (by omega) hne
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[tc + oU]! st.lab[tc + oV]!) hIt hgsz
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw1_u]

set_option maxHeartbeats 4000000 in
/-- The flip data at a triple target beside a second triple, all other
cells singletons: the constant cross-count is uniform (`0` or `3`,
reducing to the bare transposition) or matched (`1` or `2`, pairing
each chosen member with its unique minority partner and swapping the
partners along). -/
theorem twoTriple_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT1 : (tc, tc + 2) ∈ cells st.ptn level n)
    (hT2 : (d2, d2 + 2) ∈ cells st.ptn level n)
    (hT12 : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q ≠ (d2, d2 + 2) → q.2 = q.1)
    (hoU : oU ≤ 2) (hoV : oV ≤ 2) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have ht1n : tc + 2 < n := by
    have := cells_bound (by omega) hend _ hT1
    omega
  have ht2n : d2 + 2 < n := by
    have := cells_bound (by omega) hend _ hT2
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hIt.ok.labSize]; exact hi)
  have hcount := hE _ hT1 _ hT2 oU oV (by omega) (by omega)
  rw [← countP_cell hpsz hend hinj hT2, ← countP_cell hpsz hend hinj hT2,
    show d2 + 2 + 1 - d2 = 3 by omega] at hcount
  simp only at hcount
  rcases differ_pair _ _ (by simp) hcount with heq |
      ⟨pa, hpa, pb, hpb, hpab, hAu, hAv, hBu, hBv, hfix⟩
  · exact twoTriple_sw1 hIt hgsz hsymm hloop hE hT1 hT2 hT12 hsing hoU hoV hne
      (fun q hq => heq q (List.mem_range.mpr (by omega)))
  · have ha : pa ≤ 2 := by have := List.mem_range.mp hpa; omega
    have hb : pb ≤ 2 := by have := List.mem_range.mp hpb; omega
    refine twoTriple_sw2 hIt hgsz hsymm hloop hE hT1 hT2 hT12 hsing
      hoU hoV hne ha hb hpab ?_ ?_ ?_ ?_
    · intro w hw hwu hwv
      refine ⟨triple_internal hE hpsz hend hinj hlb hsymm hloop hT1
        w oU w oV (by omega) (by omega) (by omega) (by omega) hwu hwv, ?_⟩
      have hrow := hE _ hT2 _ hT1 pa pb (by omega) (by omega)
      rw [count_into_cell hpsz hend hinj hT1,
        count_into_cell hpsz hend hinj hT1,
        show tc + 2 + 1 - tc = 3 by omega, sum_range_three, sum_range_three] at hrow
      rw [sum3_eq_of_cover (f := fun j => bitCnt ctx.g[st.lab[d2 + pa]!]! st.lab[tc + j]!)
          hoU hoV hw hne (Ne.symm hwu) (Ne.symm hwv),
        sum3_eq_of_cover (f := fun j => bitCnt ctx.g[st.lab[d2 + pb]!]! st.lab[tc + j]!)
          hoU hoV hw hne (Ne.symm hwu) (Ne.symm hwv)] at hrow
      have h1 : bitCnt ctx.g[st.lab[d2 + pa]!]! st.lab[tc + oU]! = 1 := by
        rw [bitCnt_symm hsymm (hlb _ (by omega)) (hlb _ (by omega))]
        exact bitCnt_eq_one.mpr hAu
      have h2 : bitCnt ctx.g[st.lab[d2 + pa]!]! st.lab[tc + oV]! = 0 := by
        rw [bitCnt_symm hsymm (hlb _ (by omega)) (hlb _ (by omega))]
        exact bitCnt_eq_zero.mpr hAv
      have h3 : bitCnt ctx.g[st.lab[d2 + pb]!]! st.lab[tc + oU]! = 0 := by
        rw [bitCnt_symm hsymm (hlb _ (by omega)) (hlb _ (by omega))]
        exact bitCnt_eq_zero.mpr hBu
      have h4 : bitCnt ctx.g[st.lab[d2 + pb]!]! st.lab[tc + oV]! = 1 := by
        rw [bitCnt_symm hsymm (hlb _ (by omega)) (hlb _ (by omega))]
        exact bitCnt_eq_one.mpr hBv
      rw [hsymm _ _ (hlb (tc + w) (by omega)) (hlb (d2 + pa) (by omega)),
        hsymm _ _ (hlb (tc + w) (by omega)) (hlb (d2 + pb) (by omega))]
      apply bitCnt_inj.mp
      omega
    · intro w hw hwa hwb
      constructor
      · rw [hsymm _ _ (hlb (d2 + w) (by omega)) (hlb (tc + oU) (by omega)),
          hsymm _ _ (hlb (d2 + w) (by omega)) (hlb (tc + oV) (by omega))]
        exact hfix w (List.mem_range.mpr (by omega)) hwa hwb
      · exact triple_internal hE hpsz hend hinj hlb hsymm hloop hT2
          w pa w pb (by omega) (by omega) (by omega) (by omega) hwa hwb
    · rw [hAu, hBv]
    · rw [hBu, hAv]

end TwoTriple

end Hex.GraphIso.Nauty

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

section FourCell

variable {st : RefineSt n} {level tc d2 oU oV w1 w2 : Nat}

/-- Complementary pairs of a four-cell are equally adjacent. -/
theorem fourCell_comp
    (hIt : IterOk ctx level st)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hnd : ([oU, oV, w1, w2] : List Nat).Nodup) :
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + w1]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + w2]! ∧
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + w2]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[tc + w1]! ∧
    (ctx.g[st.lab[tc + oU]!]!).mem st.lab[tc + oV]! =
      (ctx.g[st.lab[tc + w1]!]!).mem st.lab[tc + w2]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hbd : ∀ x ∈ ([oU, oV, w1, w2] : List Nat), x < 4 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have : x = w2 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  have hm : tc + 3 + 1 - tc = 4 := by omega
  -- each member's count into the cell, reindexed by the four names
  have hdeg : ∀ o, o ≤ 3 →
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + oU]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + oV]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w1]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + w2]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hC
    rw [hm] at h
    rw [h, sum_range_of_distinct _ (by simp) hnd hbd]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  -- the diagonal terms vanish and the off-diagonal ones are symmetric
  have hz : ∀ o, o ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + o]! = 0 := by
    intro o ho
    exact bitCnt_eq_zero.mpr (hloop _ (hlb _ (by omega)))
  have hsy : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[tc + o']! =
        bitCnt ctx.g[st.lab[tc + o']!]! st.lab[tc + o]! := by
    intro o o' ho ho'
    exact bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  -- the four degrees agree
  have hUV := hE _ hC _ hC oU oV (by omega) (by omega)
  have hUw1 := hE _ hC _ hC oU w1 (by omega) (by omega)
  have hUw2 := hE _ hC _ hC oU w2 (by omega) (by omega)
  rw [hdeg oU hoU, hdeg oV hoV] at hUV
  rw [hdeg oU hoU, hdeg w1 hw1] at hUw1
  rw [hdeg oU hoU, hdeg w2 hw2] at hUw2
  have e1 := hz oU hoU
  have e2 := hz oV hoV
  have e3 := hz w1 hw1
  have e4 := hz w2 hw2
  have s1 := hsy oV oU hoV hoU
  have s2 := hsy w1 oU hw1 hoU
  have s3 := hsy w1 oV hw1 hoV
  have s4 := hsy w2 oU hw2 hoU
  have s5 := hsy w2 oV hw2 hoV
  have s6 := hsy w2 w1 hw2 hw1
  obtain ⟨c1, c2, c3⟩ :=
    reg4_comp (e01 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + oV]!)
      (e02 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + w1]!)
      (e03 := bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[tc + w2]!)
      (e12 := bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + w1]!)
      (e13 := bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[tc + w2]!)
      (e23 := bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[tc + w2]!)
      (by omega) (by omega) (by omega)
  exact ⟨bitCnt_inj.mp c2, bitCnt_inj.mp c3, bitCnt_inj.mp c1⟩

/-- The double-swap route at a four-cell beside a pair. -/
theorem fourPair_sw2
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hUV : oU ≠ oV) (hUw1 : oU ≠ w1) (hUw2 : oU ≠ w2)
    (hVw1 : oV ≠ w1) (hVw2 : oV ≠ w2) (h12 : w1 ≠ w2)
    (hPfix : ∀ q, q ≤ 1 →
      (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + oU]! =
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + oV]! ∧
      (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + w1]! =
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + w2]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hUV, hUw1, hUw2, hVw1, hVw2, h12]
  have hcover : ∀ o, o ≤ 3 → o = oU ∨ o = oV ∨ o = w1 ∨ o = w2 := by
    intro o ho
    omega
  -- distinct labels inside the cell and across the two cells
  have hin1 : ∀ o o' : Nat, o ≤ 3 → o' ≤ 3 → o ≠ o' →
      st.lab[tc + o]! ≠ st.lab[tc + o']! := by
    intro o o' ho ho' hne' hcon
    have := hinj (tc + o) (tc + o') (by omega) (by omega) hcon
    omega
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hC
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hP
  rw [show tc + 3 + 1 - tc = 4 by omega] at hI1
  rw [show d2 + 1 + 1 - d2 = 2 by omega] at hI2
  have hdisj : tc + 4 ≤ d2 ∨ d2 + 2 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hCP
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ o q : Nat, o ≤ 3 → q ≤ 1 →
      st.lab[tc + o]! ≠ st.lab[d2 + q]! := by
    intro o q ho hq hcon
    have := hinj (tc + o) (d2 + q) (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have hxn : st.lab[tc + w1]! < n := hlb _ (by omega)
  have hyn : st.lab[tc + w2]! < n := hlb _ (by omega)
  have hOk : Sw2Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + w1]! st.lab[tc + w2]! :=
    ⟨hun, hvn, hxn, hyn, hin1 _ _ hoU hoV hUV,
      hin1 _ _ hoU hw1 hUw1, hin1 _ _ hoU hw2 hUw2,
      hin1 _ _ hoV hw1 hVw1, hin1 _ _ hoV hw2 hVw2,
      hin1 _ _ hw1 hw2 h12⟩
  obtain ⟨hc1, hc2, -⟩ := fourCell_comp hIt hsymm hloop hE hC
    hoU hoV hw1 hw2 hnd
  -- everything outside the four moved members treats them in pairs
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + w1]! →
      z ≠ st.lab[tc + w2]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[tc + w1]! =
        (ctx.g[z]!).mem st.lab[tc + w2]! := by
    intro z hz hzu hzv hzx hzy
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · -- a member of the four-cell is one of the four moved labels
      have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rcases hcover (j - tc) hw with h | h | h | h <;>
        rw [hjt, h] at hzu hzv hzx hzy
      · exact absurd rfl hzu
      · exact absurd rfl hzv
      · exact absurd rfl hzx
      · exact absurd rfl hzy
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      rw [hjd]
      exact hPfix (j - d2) hq
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hc := cell_const_into_singleton hE hC hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      have hd := cell_const_into_singleton hE hC hpmem
        (o := w1) (o' := w2) (by omega) (by omega)
      rw [← hjp] at hc hd
      have hjn : st.lab[j]! < n := hlb j hj
      constructor
      · rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]
        exact hc
      · rw [hsymm _ _ hjn hxn, hsymm _ _ hjn hyn]
        exact hd
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
            st.lab[tc + w2]! st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    exact sw2_cells hOk (sw1_cells hIt.ok hIt.inj hC (by omega) (by omega) hUV)
      (sw1_cells hIt.ok hIt.inj hC (by omega) (by omega) h12)
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw2 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
      st.lab[tc + w2]!) hIt hgsz (sw2_lt hOk)
    (fun w _ => sw2_invol hOk w)
    (sw2_bits hsymm hloop hOk hfix hc1 hc2) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (tc + oU) (by omega), sw2_u]

/-- The triple-swap route at a four-cell beside a pair: the chosen
members cross the pair coherently, as they do on opposite sides of a
matched split. -/
theorem fourPair_sw3
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hw1 : w1 ≤ 3) (hw2 : w2 ≤ 3)
    (hUV : oU ≠ oV) (hUw1 : oU ≠ w1) (hUw2 : oU ≠ w2)
    (hVw1 : oV ≠ w1) (hVw2 : oV ≠ w2) (h12 : w1 ≠ w2)
    (hUV0 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + 0]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + 1]!)
    (hUV1 : (ctx.g[st.lab[tc + oU]!]!).mem st.lab[d2 + 1]! =
      (ctx.g[st.lab[tc + oV]!]!).mem st.lab[d2 + 0]!)
    (hW0 : (ctx.g[st.lab[tc + w1]!]!).mem st.lab[d2 + 0]! =
      (ctx.g[st.lab[tc + w2]!]!).mem st.lab[d2 + 1]!)
    (hW1 : (ctx.g[st.lab[tc + w1]!]!).mem st.lab[d2 + 1]! =
      (ctx.g[st.lab[tc + w2]!]!).mem st.lab[d2 + 0]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! ∧
      st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
      st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hUV, hUw1, hUw2, hVw1, hVw2, h12]
  have hcover : ∀ o, o ≤ 3 → o = oU ∨ o = oV ∨ o = w1 ∨ o = w2 := by
    intro o ho
    omega
  have hin1 : ∀ o o' : Nat, o ≤ 3 → o' ≤ 3 → o ≠ o' →
      st.lab[tc + o]! ≠ st.lab[tc + o']! := by
    intro o o' ho ho' hne' hcon
    have := hinj (tc + o) (tc + o') (by omega) (by omega) hcon
    omega
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hC
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hP
  rw [show tc + 3 + 1 - tc = 4 by omega] at hI1
  rw [show d2 + 1 + 1 - d2 = 2 by omega] at hI2
  have hdisj : tc + 4 ≤ d2 ∨ d2 + 2 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hCP
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ o q : Nat, o ≤ 3 → q ≤ 1 →
      st.lab[tc + o]! ≠ st.lab[d2 + q]! := by
    intro o q ho hq hcon
    have := hinj (tc + o) (d2 + q) (by omega) (by omega) hcon
    omega
  have hpne : st.lab[d2 + 0]! ≠ st.lab[d2 + 1]! := by
    intro hcon
    have := hinj (d2 + 0) (d2 + 1) (by omega) (by omega) hcon
    omega
  have hun : st.lab[tc + oU]! < n := hlb _ (by omega)
  have hvn : st.lab[tc + oV]! < n := hlb _ (by omega)
  have hxn : st.lab[tc + w1]! < n := hlb _ (by omega)
  have hyn : st.lab[tc + w2]! < n := hlb _ (by omega)
  have han : st.lab[d2 + 0]! < n := hlb _ (by omega)
  have hbn : st.lab[d2 + 1]! < n := hlb _ (by omega)
  have hOk : Sw3Ok n st.lab[tc + oU]! st.lab[tc + oV]!
      st.lab[tc + w1]! st.lab[tc + w2]! st.lab[d2 + 0]!
      st.lab[d2 + 1]! :=
    ⟨hun, hvn, hxn, hyn, han, hbn,
      hin1 _ _ hoU hoV hUV, hin1 _ _ hoU hw1 hUw1,
      hin1 _ _ hoU hw2 hUw2, hcross oU 0 hoU (by omega),
      hcross oU 1 hoU (by omega),
      hin1 _ _ hoV hw1 hVw1, hin1 _ _ hoV hw2 hVw2,
      hcross oV 0 hoV (by omega), hcross oV 1 hoV (by omega),
      hin1 _ _ hw1 hw2 h12, hcross w1 0 hw1 (by omega),
      hcross w1 1 hw1 (by omega), hcross w2 0 hw2 (by omega),
      hcross w2 1 hw2 (by omega), hpne⟩
  obtain ⟨hc1, hc2, -⟩ := fourCell_comp hIt hsymm hloop hE hC
    hoU hoV hw1 hw2 hnd
  -- only the singletons remain outside the six moved members
  have hfix : ∀ z, z < n → z ≠ st.lab[tc + oU]! →
      z ≠ st.lab[tc + oV]! → z ≠ st.lab[tc + w1]! →
      z ≠ st.lab[tc + w2]! → z ≠ st.lab[d2 + 0]! →
      z ≠ st.lab[d2 + 1]! →
      (ctx.g[z]!).mem st.lab[tc + oU]! =
        (ctx.g[z]!).mem st.lab[tc + oV]! ∧
      (ctx.g[z]!).mem st.lab[tc + w1]! =
        (ctx.g[z]!).mem st.lab[tc + w2]! ∧
      (ctx.g[z]!).mem st.lab[d2 + 0]! =
        (ctx.g[z]!).mem st.lab[d2 + 1]! := by
    intro z hz hzu hzv hzx hzy hza hzb
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rcases hcover (j - tc) hw with h | h | h | h <;>
        rw [hjt, h] at hzu hzv hzx hzy
      · exact absurd rfl hzu
      · exact absurd rfl hzv
      · exact absurd rfl hzx
      · exact absurd rfl hzy
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      have hq2 : j - d2 = 0 ∨ j - d2 = 1 := by omega
      rcases hq2 with h | h <;> rw [hjd, h] at hza hzb
      · exact absurd rfl hza
      · exact absurd rfl hzb
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hcU := cell_const_into_singleton hE hC hpmem
        (o := oU) (o' := oV) (by omega) (by omega)
      have hcW := cell_const_into_singleton hE hC hpmem
        (o := w1) (o' := w2) (by omega) (by omega)
      have hcP := cell_const_into_singleton hE hP hpmem
        (o := 0) (o' := 1) (by omega) (by omega)
      rw [← hjp] at hcU hcW hcP
      have hjn : st.lab[j]! < n := hlb j hj
      refine ⟨?_, ?_, ?_⟩
      · rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]; exact hcU
      · rw [hsymm _ _ hjn hxn, hsymm _ _ hjn hyn]; exact hcW
      · rw [hsymm _ _ hjn han, hsymm _ _ hjn hbn]; exact hcP
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw3 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
            st.lab[tc + w2]! st.lab[d2 + 0]! st.lab[d2 + 1]!
            st.lab[p.1 + o]! = st.lab[p.1 + o']! := by
    exact sw3_cells hOk (sw1_cells hIt.ok hIt.inj hC (by omega) (by omega) hUV)
      (sw1_cells hIt.ok hIt.inj hC (by omega) (by omega) h12)
      (sw1_cells hIt.ok hIt.inj hP (a := 0) (b := 1) (by omega) (by omega) (by omega))
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw3 st.lab[tc + oU]! st.lab[tc + oV]! st.lab[tc + w1]!
      st.lab[tc + w2]! st.lab[d2 + 0]! st.lab[d2 + 1]!)
    hIt hgsz (sw3_lt hOk) (fun w _ => sw3_invol hOk w)
    (sw3_bits hsymm hloop hOk hfix hc1 hc2 hUV0 hUV1 hW0 hW1) hset
  refine ⟨σ, hrm, hsp, ?_, ?_, ?_⟩
  · rw [hat (tc + oU) (by omega), sw3_u]
  · rw [hat (d2 + 0) (by omega), sw3_a hOk]
  · rw [hat (d2 + 1) (by omega), sw3_b hOk]

/-- Two distinct offsets below four leave two more. -/
private theorem other_two {p q : Nat} (hp : p ≤ 3) (hq : q ≤ 3)
    (hpq : p ≠ q) :
    ∃ r s, r ≤ 3 ∧ s ≤ 3 ∧ p ≠ r ∧ p ≠ s ∧ q ≠ r ∧ q ≠ s ∧
      r ≠ s := by
  have hp3 : p = 0 ∨ p = 1 ∨ p = 2 ∨ p = 3 := by omega
  have hq3 : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 := by omega
  rcases hp3 with rfl | rfl | rfl | rfl <;>
    rcases hq3 with rfl | rfl | rfl | rfl <;>
    first
      | exact absurd rfl hpq
      | exact ⟨2, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨1, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨1, 2, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 3, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 2, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩
      | exact ⟨0, 1, by omega, by omega, by omega, by omega,
          by omega, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
/-- The flip data at a four-cell target beside a pair, all other cells
singletons. -/
theorem fourPair_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hoU : oU ≤ 3) (hoV : oV ≤ 3) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  obtain ⟨w1, w2, hw1, hw2, hUw1, hUw2, hVw1, hVw2, h12⟩ :=
    other_two hoU hoV hne
  have hnd : ([oU, oV, w1, w2] : List Nat).Nodup := by
    simp [hne, hUw1, hUw2, hVw1, hVw2, h12]
  have hbd : ∀ x ∈ ([oU, oV, w1, w2] : List Nat), x < 4 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    rcases List.mem_cons.mp hx with rfl | hx
    · omega
    · have : x = w2 := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rfl
        · exact absurd hx (by simp)
      omega
  -- the forward counts into the pair
  have hfwd : ∀ o, o ≤ 3 →
      (worksetOf n st.lab d2 (d2 + 1)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hP
    rw [show d2 + 1 + 1 - d2 = 2 by omega, sum_range_two] at h
    exact h
  -- the reverse counts into the four-cell
  have hrev : ∀ q, q ≤ 1 →
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[d2 + q]!]! =
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + oU]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + oV]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + w1]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + w2]! := by
    intro q hq
    have h := count_into_cell (ctx := ctx) (u := st.lab[d2 + q]!) hpsz hend hinj hC
    rw [show tc + 3 + 1 - tc = 4 by omega] at h
    rw [h, sum_range_of_distinct _ (by simp) hnd hbd]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  -- forward constancy across the four-cell, reverse across the pair
  have hfc : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! =
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 1]! := by
    intro o o' ho ho'
    have h := hE _ hC _ hP o o' (by omega) (by omega)
    rw [hfwd o ho, hfwd o' ho'] at h
    exact h
  have hrc := hE _ hP _ hC 0 1 (by omega) (by omega)
  rw [hrev 0 (by omega), hrev 1 (by omega)] at hrc
  -- the two directions agree termwise
  have hsy : ∀ o q, o ≤ 3 → q ≤ 1 →
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + o]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! :=
    fun o q ho hq => bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have hle : ∀ o q : Nat,
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! ≤ 1 :=
    fun o q => bitCnt_le_one _ _
  -- the pair's view of the four members, in the two useful shapes
  have hbit : ∀ o q, o ≤ 3 → q ≤ 1 →
      ((ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + q]! = true ↔
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! = 1) :=
    fun o q ho hq => ⟨fun h => bitCnt_eq_one.mpr h,
      fun h => bitCnt_eq_one.mp h⟩
  have hPof : ∀ o o', o ≤ 3 → o' ≤ 3 →
      (∀ q, q ≤ 1 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! =
          bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + q]!) →
      ∀ q, q ≤ 1 →
        (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + o]! =
          (ctx.g[st.lab[d2 + q]!]!).mem st.lab[tc + o']! := by
    intro o o' ho ho' h q hq
    have h1 := hsy o q ho hq
    have h2 := hsy o' q ho' hq
    exact bitCnt_inj.mp (by rw [h1, h2]; exact h q hq)
  -- the constant cross-count is zero, one or two
  have hsum : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 0 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 1 ∨
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 1]! = 2 := by
    have := hle oU 0
    have := hle oU 1
    omega
  have hUVc := hfc oU oV hoU hoV
  have hUw1c := hfc oU w1 hoU hw1
  have hUw2c := hfc oU w2 hoU hw2
  rcases hsum with h0 | h1 | h2
  · -- no edges between the two cells
    refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
    intro q hq
    have e1 := hle oU 0
    have e2 := hle oU 1
    have e3 := hle oV 0
    have e4 := hle oV 1
    have e5 := hle w1 0
    have e6 := hle w1 1
    have e7 := hle w2 0
    have e8 := hle w2 1
    constructor
    · exact hPof oU oV hoU hoV (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
    · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
  · -- each member meets exactly one of the pair
    have hr0 : bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + w2]!]! st.lab[d2 + 0]! = 2 := by
      have s1 := hsy oU 0 hoU (by omega)
      have s2 := hsy oV 0 hoV (by omega)
      have s3 := hsy w1 0 hw1 (by omega)
      have s4 := hsy w2 0 hw2 (by omega)
      have s5 := hsy oU 1 hoU (by omega)
      have s6 := hsy oV 1 hoV (by omega)
      have s7 := hsy w1 1 hw1 (by omega)
      have s8 := hsy w2 1 hw2 (by omega)
      omega
    rcases Decidable.em
        (bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]! =
          bitCnt ctx.g[st.lab[tc + oV]!]! st.lab[d2 + 0]!)
      with hsame | hdiff
    · -- the chosen members sit on the same side of the split
      refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
        hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
      intro q hq
      have e1 := hle oU 0
      have e2 := hle oU 1
      have e3 := hle oV 0
      have e4 := hle oV 1
      have e5 := hle w1 0
      have e6 := hle w1 1
      have e7 := hle w2 0
      have e8 := hle w2 1
      constructor
      · exact hPof oU oV hoU hoV (fun q' hq' => by
          rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
          q hq
      · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
          rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
          q hq
    · -- opposite sides: name the partner of each chosen member
      have e1 := hle oU 0
      have e2 := hle oU 1
      have e3 := hle oV 0
      have e4 := hle oV 1
      have e5 := hle w1 0
      have e6 := hle w1 1
      have e7 := hle w2 0
      have e8 := hle w2 1
      have hVc := hfc oV w1 hoV hw1
      rcases Decidable.em
          (bitCnt ctx.g[st.lab[tc + w1]!]! st.lab[d2 + 0]! =
            bitCnt ctx.g[st.lab[tc + oU]!]! st.lab[d2 + 0]!)
        with hw1U | hw1V
      · obtain ⟨σ, hrm, hsp, hfl, -, -⟩ :=
          fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP
            hsing hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        exact ⟨σ, hrm, hsp, hfl⟩
      · obtain ⟨σ, hrm, hsp, hfl, -, -⟩ :=
          fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP
            hsing hoU hoV hw2 hw1 hne hUw2 hUw1 hVw2 hVw1
            (Ne.symm h12)
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
            (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        exact ⟨σ, hrm, hsp, hfl⟩
  · -- every member meets both of the pair
    refine fourPair_sw2 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hoU hoV hw1 hw2 hne hUw1 hUw2 hVw1 hVw2 h12 ?_
    intro q hq
    have e1 := hle oU 0
    have e2 := hle oU 1
    have e3 := hle oV 0
    have e4 := hle oV 1
    have e5 := hle w1 0
    have e6 := hle w1 1
    have e7 := hle w2 0
    have e8 := hle w2 1
    constructor
    · exact hPof oU oV hoU hoV (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq
    · exact hPof w1 w2 hw1 hw2 (fun q' hq' => by
        rcases (by omega : q' = 0 ∨ q' = 1) with rfl | rfl <;> omega)
        q hq

/-- The transposition route at a pair target beside a four-cell. -/
theorem pairFour_sw1
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hqU : qU ≤ 1) (hqV : qV ≤ 1) (hqne : qU ≠ qV)
    (huni : ∀ o, o ≤ 3 →
      (ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + qU]! =
        (ctx.g[st.lab[tc + o]!]!).mem st.lab[d2 + qV]!) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[d2 + qV]! = σ.toFun st.lab[d2 + qU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hI1 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hC
  have hI2 := cells_isCell (by rw [hpsz]; exact Nat.le_refl _)
    hend _ hP
  rw [show tc + 3 + 1 - tc = 4 by omega] at hI1
  rw [show d2 + 1 + 1 - d2 = 2 by omega] at hI2
  have hdisj : tc + 4 ≤ d2 ∨ d2 + 2 ≤ tc := by
    rcases isCell_disj_or_eq hI1 hI2 with ⟨h1, -⟩ | hd | hd
    · exact absurd h1 hCP
    · exact Or.inl hd
    · exact Or.inr hd
  have hcross : ∀ o q : Nat, o ≤ 3 → q ≤ 1 →
      st.lab[tc + o]! ≠ st.lab[d2 + q]! := by
    intro o q ho hq hcon
    have := hinj (tc + o) (d2 + q) (by omega) (by omega) hcon
    omega
  have hin2 : ∀ q q' : Nat, q ≤ 1 → q' ≤ 1 → q ≠ q' →
      st.lab[d2 + q]! ≠ st.lab[d2 + q']! := by
    intro q q' hq hq' hne' hcon
    have := hinj (d2 + q) (d2 + q') (by omega) (by omega) hcon
    omega
  have hun : st.lab[d2 + qU]! < n := hlb _ (by omega)
  have hvn : st.lab[d2 + qV]! < n := hlb _ (by omega)
  have huv := hin2 _ _ hqU hqV hqne
  have hfix : ∀ z, z < n → z ≠ st.lab[d2 + qU]! →
      z ≠ st.lab[d2 + qV]! →
      (ctx.g[z]!).mem st.lab[d2 + qU]! =
        (ctx.g[z]!).mem st.lab[d2 + qV]! := by
    intro z hz hzu hzv
    obtain ⟨j, hj, rfl⟩ := labInj_surj
      (by rw [hlsz]; exact Nat.le_refl _) hIt.ok.labOk hinj z hz
    obtain ⟨p, hp, hj1, hj2⟩ := cells_cover (ptn := st.ptn)
      (level := level) (nn := n) j (by omega)
    have hjn : st.lab[j]! < n := hlb j hj
    rcases Decidable.em (p = (tc, tc + 3)) with rfl | hpC
    · have hw : j - tc ≤ 3 := by
        have h1 : tc ≤ j := hj1
        have h2 : j ≤ tc + 3 := hj2
        omega
      have hjt : j = tc + (j - tc) := by
        have h1 : tc ≤ j := hj1
        omega
      rw [hjt]
      exact huni (j - tc) hw
    rcases Decidable.em (p = (d2, d2 + 1)) with rfl | hpP
    · have hq : j - d2 ≤ 1 := by
        have h1 : d2 ≤ j := hj1
        have h2 : j ≤ d2 + 1 := hj2
        omega
      have hjd : j = d2 + (j - d2) := by
        have h1 : d2 ≤ j := hj1
        omega
      have hq2 : j - d2 = qU ∨ j - d2 = qV := by omega
      rcases hq2 with h | h <;> rw [hjd, h] at hzu hzv
      · exact absurd rfl hzu
      · exact absurd rfl hzv
    · have hps : p.2 = p.1 := hsing p hp hpC hpP
      have hjp : j = p.1 := by omega
      have hpmem : (p.1, p.1) ∈ cells st.ptn level n := by
        have hpe : p = (p.1, p.1) := by
          obtain ⟨qa, qb⟩ := p
          simp only at hps ⊢
          rw [hps]
        rw [← hpe]
        exact hp
      have hc := cell_const_into_singleton hE hP hpmem
        (o := qU) (o' := qV) (by omega) (by omega)
      rw [← hjp] at hc
      rw [hsymm _ _ hjn hun, hsymm _ _ hjn hvn]
      exact hc
  have hset : ∀ p ∈ cells st.ptn level n,
      ∀ o, o < p.2 + 1 - p.1 →
      ∃ o', o' < p.2 + 1 - p.1 ∧
        sw1 st.lab[d2 + qU]! st.lab[d2 + qV]! st.lab[p.1 + o]! =
          st.lab[p.1 + o']! := by
    exact sw1_cells hIt.ok hIt.inj hP (by omega) (by omega) hqne
  obtain ⟨σ, hrm, hsp, hat⟩ := flip_data_of_bits
    (f := sw1 st.lab[d2 + qU]! st.lab[d2 + qV]!) hIt hgsz
    (sw1_lt hun hvn) (fun w _ => sw1_invol huv w)
    (sw1_bits hsymm hloop hun hvn huv hfix) hset
  refine ⟨σ, hrm, hsp, ?_⟩
  rw [hat (d2 + qU) (by omega), sw1_u]

set_option maxHeartbeats 1000000 in
/-- The flip data at a pair target beside a four-cell, all other cells
singletons. -/
theorem pairFour_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hC : (tc, tc + 3) ∈ cells st.ptn level n)
    (hP : (d2, d2 + 1) ∈ cells st.ptn level n)
    (hCP : tc ≠ d2)
    (hsing : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 3) →
      q ≠ (d2, d2 + 1) → q.2 = q.1)
    (hqU : qU ≤ 1) (hqV : qV ≤ 1) (hqne : qU ≠ qV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[d2 + qV]! = σ.toFun st.lab[d2 + qU]! := by
  have hpsz := hIt.ok.ptnSize
  have hlsz := hIt.ok.labSize
  have hend := hIt.ok.ptnEnd
  have hinj := hIt.inj
  have htn : tc + 3 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hC
    rw [hpsz] at this
    omega
  have hdn : d2 + 1 < n := by
    have := cells_bound (by rw [hpsz]; exact Nat.le_refl _) hend _ hP
    rw [hpsz] at this
    omega
  have hlb : ∀ i, i < n → st.lab[i]! < n := fun i hi =>
    hIt.ok.labOk i (by rw [hlsz]; omega)
  have hfwd : ∀ o, o ≤ 3 →
      (worksetOf n st.lab d2 (d2 + 1)).cardInter
          ctx.g[st.lab[tc + o]!]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! := by
    intro o ho
    have h := count_into_cell (ctx := ctx) (u := st.lab[tc + o]!) hpsz hend hinj hP
    rw [show d2 + 1 + 1 - d2 = 2 by omega, sum_range_two] at h
    exact h
  have hrev : ∀ q, q ≤ 1 →
      (worksetOf n st.lab tc (tc + 3)).cardInter
          ctx.g[st.lab[d2 + q]!]! =
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 0]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 1]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 2]! +
        bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + 3]! := by
    intro q hq
    have h := count_into_cell (ctx := ctx) (u := st.lab[d2 + q]!) hpsz hend hinj hC
    rw [show tc + 3 + 1 - tc = 4 by omega] at h
    rw [h, sum_range_of_distinct _ (l := [0, 1, 2, 3]) (by simp)
      (by simp) (by intro x hx; simp at hx; omega)]
    simp only [List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil]
    omega
  have hfc : ∀ o o', o ≤ 3 → o' ≤ 3 →
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! =
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + o']!]! st.lab[d2 + 1]! := by
    intro o o' ho ho'
    have h := hE _ hC _ hP o o' (by omega) (by omega)
    rw [hfwd o ho, hfwd o' ho'] at h
    exact h
  have hrc := hE _ hP _ hC 0 1 (by omega) (by omega)
  rw [hrev 0 (by omega), hrev 1 (by omega)] at hrc
  have hsy : ∀ o q, o ≤ 3 → q ≤ 1 →
      bitCnt ctx.g[st.lab[d2 + q]!]! st.lab[tc + o]! =
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! :=
    fun o q ho hq => bitCnt_inj.mpr
      (hsymm _ _ (hlb _ (by omega)) (hlb _ (by omega)))
  have hle : ∀ o q : Nat,
      bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + q]! ≤ 1 :=
    fun o q => bitCnt_le_one _ _
  -- the matched route, given the split named explicitly
  have route : ∀ a b c d : Nat, a ≤ 3 → b ≤ 3 → c ≤ 3 → d ≤ 3 →
      a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      bitCnt ctx.g[st.lab[tc + a]!]! st.lab[d2 + 0]! = 1 →
      bitCnt ctx.g[st.lab[tc + b]!]! st.lab[d2 + 0]! = 1 →
      bitCnt ctx.g[st.lab[tc + c]!]! st.lab[d2 + 0]! = 0 →
      bitCnt ctx.g[st.lab[tc + d]!]! st.lab[d2 + 0]! = 0 →
      (∀ o, o ≤ 3 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! = 1) →
      ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
        StPerm level st (mapSt σ st) ∧
        st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
        st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
    intro a b c d ha hb hc hd hab hac had hbc hbd hcd hAa hAb hAc
      hAd hone
    have o1 := hone a ha
    have o2 := hone b hb
    have o3 := hone c hc
    have o4 := hone d hd
    obtain ⟨σ, hrm, hsp, -, hp1, hp2⟩ :=
      fourPair_sw3 hIt hgsz hsymm hloop hE hC hP hCP hsing
        ha hc hb hd hac hab had (Ne.symm hbc) hcd hbd
        (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
        (bitCnt_inj.mp (by omega)) (bitCnt_inj.mp (by omega))
    exact ⟨σ, hrm, hsp, hp1, hp2⟩
  have hsum : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 0 ∨
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 1 ∨
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
      bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 1]! = 2 := by
    have := hle 0 0
    have := hle 0 1
    omega
  have c1 := hfc 0 1 (by omega) (by omega)
  have c2 := hfc 0 2 (by omega) (by omega)
  have c3 := hfc 0 3 (by omega) (by omega)
  have e1 := hle 0 0
  have e2 := hle 0 1
  have e3 := hle 1 0
  have e4 := hle 1 1
  have e5 := hle 2 0
  have e6 := hle 2 1
  have e7 := hle 3 0
  have e8 := hle 3 1
  rcases hsum with h0 | h1 | h2
  · -- the pair meets no member of the four-cell
    refine pairFour_sw1 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hqU hqV hqne ?_
    intro o ho
    have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases ho4 with rfl | rfl | rfl | rfl <;>
      exact bitCnt_inj.mp (by omega)
  · -- each member meets exactly one, so the four-cell splits in two
    have hone : ∀ o, o ≤ 3 →
        bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 0]! +
          bitCnt ctx.g[st.lab[tc + o]!]! st.lab[d2 + 1]! = 1 := by
      intro o ho
      have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      rcases ho4 with rfl | rfl | rfl | rfl <;> omega
    have hr0 : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! +
        bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 2 := by
      have s1 := hsy 0 0 (by omega) (by omega)
      have s2 := hsy 1 0 (by omega) (by omega)
      have s3 := hsy 2 0 (by omega) (by omega)
      have s4 := hsy 3 0 (by omega) (by omega)
      have s5 := hsy 0 1 (by omega) (by omega)
      have s6 := hsy 1 1 (by omega) (by omega)
      have s7 := hsy 2 1 (by omega) (by omega)
      have s8 := hsy 3 1 (by omega) (by omega)
      omega
    have hpick : ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
        StPerm level st (mapSt σ st) ∧
        st.lab[d2 + 1]! = σ.toFun st.lab[d2 + 0]! ∧
        st.lab[d2 + 0]! = σ.toFun st.lab[d2 + 1]! := by
      have v0 : bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 0]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v1 : bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 1]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v2 : bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 2]!]! st.lab[d2 + 0]! = 1 := by
        omega
      have v3 : bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 0 ∨
          bitCnt ctx.g[st.lab[tc + 3]!]! st.lab[d2 + 0]! = 1 := by
        omega
      rcases v0 with q0 | q0 <;> rcases v1 with q1 | q1 <;>
        rcases v2 with q2 | q2 <;> rcases v3 with q3 | q3 <;>
        first
          | (exfalso; omega)
          | exact route 0 1 2 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 0 2 1 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 0 3 1 2 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 1 2 0 3 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 1 3 0 2 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
          | exact route 2 3 0 1 (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) (by omega) (by omega) (by omega) (by omega)
              (by omega) hone
    obtain ⟨σ, hrm, hsp, hp1, hp2⟩ := hpick
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨σ, hrm, hsp, hp1⟩
    · exact ⟨σ, hrm, hsp, hp2⟩
  · -- the pair meets every member of the four-cell
    refine pairFour_sw1 hIt hgsz hsymm hloop hE hC hP hCP hsing
      hqU hqV hqne ?_
    intro o ho
    have ho4 : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
    have hqq : (qU = 0 ∧ qV = 1) ∨ (qU = 1 ∧ qV = 0) := by omega
    rcases hqq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases ho4 with rfl | rfl | rfl | rfl <;>
      exact bitCnt_inj.mp (by omega)

end FourCell

section Shape

end Shape

section Dispatch

variable {st : RefineSt n} {level tc te oU oV : Nat}

set_option maxHeartbeats 1000000 in
/-- Flip data at every cell of a partition whose defect is at most
four. This is the shape the cheapautom guard's second branch admits;
it dispatches to the pair and triple routes of the first branch
together with the four exotic routes. -/
theorem defect4_flip_data
    (hIt : IterOk ctx level st)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ z w, z < n → w < n →
      (ctx.g[z]!).mem w = (ctx.g[w]!).mem z)
    (hloop : ∀ z, z < n → (ctx.g[z]!).mem z = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hdef : n - (cells st.ptn level n).length ≤ 4)
    (hT : (tc, te) ∈ cells st.ptn level n)
    (hoU : oU ≤ te - tc) (hoV : oV ≤ te - tc) (hne : oU ≠ oV) :
    ∃ σ : Renaming n, RowsMap σ ctx.g ctx.g ∧
      StPerm level st (mapSt σ st) ∧
      st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]! := by
  have hpsz := hIt.ok.ptnSize
  have hend := hIt.ok.ptnEnd
  have hnn : n ≤ st.ptn.size := by rw [hpsz]; exact Nat.le_refl _
  have hexc := exc_sum_eq_defect (nn := n) (level := level)
    (ptn := st.ptn) hpsz hend
  have hle : tc ≤ te := cells_le _ hT
  have hsize5 : ∀ q ∈ cells st.ptn level n, q.2 - q.1 ≤ 4 := by
    intro q hq
    have := exc_ge_one (q := q) _ hq
    omega
  have hpair2 : ∀ q ∈ cells st.ptn level n,
      ∀ q' ∈ cells st.ptn level n, q ≠ q' →
        (q.2 - q.1) + (q'.2 - q'.1) ≤ 4 := by
    intro q hq q' hq' hqq
    have := exc_ge_two (q := q) (q' := q') _ hq hq' hqq
    omega
  have htri3 : ∀ q ∈ cells st.ptn level n,
      ∀ q' ∈ cells st.ptn level n,
      ∀ q'' ∈ cells st.ptn level n, q ≠ q' → q ≠ q'' → q' ≠ q'' →
        (q.2 - q.1) + (q'.2 - q'.1) + (q''.2 - q''.1) ≤ 4 := by
    intro q hq q' hq' q'' hq'' h1 h2 h3
    have := exc_ge_three (q := q) (q' := q') (q'' := q'') _ hq hq'
      hq'' h1 h2 h3
    omega
  have hT5 := hsize5 _ hT
  have hs : te - tc = 1 ∨ te - tc = 2 ∨ te - tc = 3 ∨ te - tc = 4 := by
    omega
  rcases hs with hs | hs | hs | hs
  · -- a pair target
    have hte : te = tc + 1 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 1)) - (Prod.fst (tc, tc + 1)) = 1 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        3 ≤ q.2 - q.1) with ⟨C, hC, hCbig⟩ | hnobig
    · -- a four-cell beside it: the exotic route
      have hCle : C.1 ≤ C.2 := cells_le _ hC
      have hCne : C ≠ (tc, tc + 1) := by
        intro hcon
        rw [hcon] at hCbig
        omega
      have hCex : C.2 - C.1 = 3 := by
        have := hpair2 _ hC _ hT hCne
        omega
      have hCform : C = (C.1, C.1 + 3) := by
        obtain ⟨ca, cb⟩ := C
        simp only at hCex ⊢
        have hcb : cb = ca + 3 := by omega
        rw [hcb]
      have hC' : (C.1, C.1 + 3) ∈ cells st.ptn level n :=
        hCform ▸ hC
      have hCP : C.1 ≠ tc := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hC' hT (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        simp only [Prod.mk.injEq] at heq
        omega
      refine pairFour_flip_data hIt hgsz hsymm hloop hE hC' hT
        hCP ?_ (by omega) (by omega) hne
      intro q hq hqC hqP
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hCq : C ≠ q := fun hcon => hqC (by rw [← hcon, ← hCform])
        have h3 := htri3 _ hC _ hT _ hq hCne hCq
          (fun hcon => hqP hcon.symm)
        omega
    · -- no large cell: the first branch's pair route applies
      refine pair_flip_data hIt hgsz hsymm hloop hE hT ?_
        (by omega) (by omega) hne
      intro q hq hqp
      have hql := cells_le _ hq
      have hq2 : q.2 - q.1 ≤ 2 := by
        rcases Nat.lt_or_ge (q.2 - q.1) 3 with h | h
        · omega
        · exact absurd ⟨q, hq, h⟩ hnobig
      omega
  · -- a triple target
    have hte : te = tc + 2 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 2)) - (Prod.fst (tc, tc + 2)) = 2 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        q ≠ (tc, tc + 2) ∧ q.2 - q.1 = 2) with ⟨D, hD, hDne, hDex⟩ |
      hnotri
    · -- two triples: the exotic route
      have hDform : D = (D.1, D.1 + 2) := by
        obtain ⟨da, db⟩ := D
        simp only at hDex ⊢
        have hdb : db = da + 2 := by omega
        rw [hdb]
      have hD' : (D.1, D.1 + 2) ∈ cells st.ptn level n :=
        hDform ▸ hD
      have hTD : tc ≠ D.1 := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hT hD' (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        exact hDne (by rw [hDform, ← heq])
      refine twoTriple_flip_data hIt hgsz hsymm hloop hE hT hD'
        hTD ?_ (by omega) (by omega) hne
      intro q hq hqT hqD
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hDq : D ≠ q := fun hcon => hqD (by rw [← hcon, ← hDform])
        have h3 := htri3 _ hT _ hD _ hq (Ne.symm hDne) 
          (fun hcon => hqT hcon.symm) hDq
        omega
    · -- a unique triple with everything else small
      refine triple_flip_data hIt hgsz hsymm hloop hE hT ?_
        (by omega) (by omega) hne
      intro q hq hqT
      have hql := cells_le _ hq
      rcases Decidable.em (q.2 - q.1 = 2) with h2 | h2
      · exact absurd ⟨q, hq, hqT, h2⟩ hnotri
      · have := hpair2 _ hq _ hT hqT
        omega
  · -- a four-cell target
    have hte : te = tc + 3 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 3)) - (Prod.fst (tc, tc + 3)) = 3 :=
      by omega
    rcases Decidable.em (∃ q ∈ cells st.ptn level n,
        q ≠ (tc, tc + 3) ∧ q.1 < q.2) with ⟨P, hP, hPne, hPnt⟩ |
      hnopair
    · -- a pair beside it: the exotic route
      have hPle := cells_le _ hP
      have hPex : P.2 - P.1 = 1 := by
        have := hpair2 _ hT _ hP (fun hcon => hPne hcon.symm)
        omega
      have hPform : P = (P.1, P.1 + 1) := by
        obtain ⟨pa, pb⟩ := P
        simp only at hPex ⊢
        have hpb : pb = pa + 1 := by omega
        rw [hpb]
      have hP' : (P.1, P.1 + 1) ∈ cells st.ptn level n :=
        hPform ▸ hP
      have hCP : tc ≠ P.1 := by
        intro hcon
        have heq := cells_eq_of_shared hnn hend hT hP' (j := tc)
          (by omega) (by omega) (by omega) (by omega)
        simp only [Prod.mk.injEq] at heq
        omega
      refine fourPair_flip_data hIt hgsz hsymm hloop hE hT hP'
        hCP ?_ (by omega) (by omega) hne
      intro q hq hqT hqP
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exfalso
        have hPq : P ≠ q := fun hcon => hqP (by rw [← hcon, ← hPform])
        have h3 := htri3 _ hT _ hP _ hq (Ne.symm hPne)
          (fun hcon => hqT hcon.symm) hPq
        omega
    · -- a lone four-cell
      refine oneCell_flip_data hIt hgsz hsymm hloop hE hT
        (by omega) ?_ (by omega) (by omega) hne
      intro q hq hqT
      rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
      · exact heq.symm
      · exact absurd ⟨q, hq, hqT, hlt⟩ hnopair
  · -- a five-cell target: nothing else can be nontrivial
    have hte : te = tc + 4 := by omega
    subst hte
    have hTe : (Prod.snd (tc, tc + 4)) - (Prod.fst (tc, tc + 4)) = 4 :=
      by omega
    refine oneCell_flip_data hIt hgsz hsymm hloop hE hT
      (by omega) ?_ (by omega) (by omega) hne
    intro q hq hqT
    rcases Nat.eq_or_lt_of_le (cells_le _ hq) with heq | hlt
    · exact heq.symm
    · exfalso
      have := hpair2 _ hT _ hq (fun h => hqT h.symm)
      omega

end Dispatch

end Hex.GraphIso.Nauty
