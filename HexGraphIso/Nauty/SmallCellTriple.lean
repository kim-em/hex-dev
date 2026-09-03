/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellIter
import all HexGraphIso.Nauty.Equitable

public section

/-!
The cheapautom triple analogues (SPEC § Verified search refinement,
the code-1 arm of the store-validity obligation).

The first guard branch (`defect ≤ nontrivial + 1`) forces every cell
of the partition to be a singleton, a pair, or one triple, and any two
size-three cells to coincide (the sharpened form of
`hOdd_of_defect_le`'s counting argument). On that shape this file
proves the triple analogues of the pair flip theory:

* `triple_const`: the triple's members have identical bits at every
  member of any other cell of size at most two — the count into a
  singleton is the adjacency bit, and the count into a pair is twice
  it by `pair_odd_eq`'s both-or-neither;
* `triple_internal`: the induced graph on the triple is empty or
  complete — the off-diagonal bits are all equal, by the three row-sum
  equalities of equitability (a one-regular graph on three vertices
  is impossible);
* `triple_flip_rows`: the transposition of any two triple members,
  fixing every other vertex, preserves the adjacency rows. Unlike the
  pair flip no matching closure is needed: every other cell is small,
  so the triple's relations to it are constant across the triple.

Remaining on top of this file: the self-equivalence `StPerm` of a
row-preserving flip and the generalized single-deviation theorem, the
pair-closure involution construction, the all-leaves induction, the
`noncheaplevel` event lemma and arm-2 assembly — plus the exotic
defect-four configurations outside the first branch.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-! # The sharpened guard: sizes at most three, at most one triple -/

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

private theorem sum_excess_ge_countP_add2 {q q' : Nat × Nat} :
    ∀ (l : List (Nat × Nat)), (∀ p ∈ l, p.1 ≤ p.2) → q ∈ l → q' ∈ l →
      q ≠ q' →
      ((l.map fun p => p.2 - p.1).sum ≥
        (l.countP fun p => decide (p.1 < p.2)) +
          (q.2 - q.1) + (q'.2 - q'.1) - 2)
  | [], _, hq, _, _ => absurd hq (by simp)
  | a :: l, hwf, hq, hq', hne => by
    rw [List.map_cons, List.sum_cons, List.countP_cons]
    have hwl : ∀ p ∈ l, p.1 ≤ p.2 :=
      fun p hp => hwf p (List.mem_cons_of_mem _ hp)
    rcases List.mem_cons.mp hq with rfl | hmem
    · have hq'l : q' ∈ l := by
        rcases List.mem_cons.mp hq' with heq | hmem'
        · exact absurd heq.symm hne
        · exact hmem'
      have ih := sum_excess_ge_countP_add (q := q') l hwl hq'l
      rcases Decidable.em (q.1 < q.2) with h | h
      · rw [ite_eq_left (decide_eq_true h)]
        omega
      · rw [ite_eq_right (by simpa using h)]
        omega
    · rcases List.mem_cons.mp hq' with rfl | hmem'
      · have ih := sum_excess_ge_countP_add (q := q) l hwl hmem
        rcases Decidable.em (q'.1 < q'.2) with h | h
        · rw [ite_eq_left (decide_eq_true h)]
          omega
        · rw [ite_eq_right (by simpa using h)]
          omega
      · have ih := sum_excess_ge_countP_add2 l hwl hmem hmem' hne
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

/-- In the first guard branch every cell has size at most three. -/
theorem size_le_three_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn, q.2 + 1 - q.1 ≤ 3 := by
  intro q hq
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
  omega

/-- In the first guard branch any two size-three cells coincide. -/
theorem triple_uniq_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn, ∀ q' ∈ cells ptn level nn,
      q.2 + 1 - q.1 = 3 → q'.2 + 1 - q'.1 = 3 → q = q' := by
  intro q hq q' hq' hs hs'
  rcases Decidable.em (q = q') with heq | hne
  · exact heq
  · exfalso
    have hwf : ∀ p ∈ cells ptn level nn, p.1 ≤ p.2 :=
      fun p hp => cells_le p hp
    have hsum : ((cells ptn level nn).map fun p =>
        p.2 + 1 - p.1).sum = nn := by
      rw [cells]
      have h := cells_go_sizes_sum hps hend nn 0 (by omega)
      rw [show nn - 0 = nn by omega] at h
      exact h
    have hsplit := sum_sizes_split (cells ptn level nn) hwf
    have hmem := sum_excess_ge_countP_add2 (cells ptn level nn) hwf
      hq hq' hne
    have hq12 := hwf q hq
    have hq12' := hwf q' hq'
    omega

/-- The first-branch shape: every cell is a singleton, a pair, or the
unique triple. -/
theorem cells_shape_of_defect_le {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn,
      q.2 + 1 - q.1 = 1 ∨ q.2 + 1 - q.1 = 2 ∨
        (q.2 + 1 - q.1 = 3 ∧
          ∀ q' ∈ cells ptn level nn, q'.2 + 1 - q'.1 = 3 → q' = q) := by
  intro q hq
  have hle := size_le_three_of_defect_le hps hend hguard q hq
  have hge := cells_le q hq
  rcases Decidable.em (q.2 + 1 - q.1 = 3) with h3 | h3
  · exact Or.inr (Or.inr ⟨h3, fun q' hq' hs' =>
      triple_uniq_of_defect_le hps hend hguard q' hq' q hq hs' h3⟩)
  · rcases Decidable.em (q.2 + 1 - q.1 = 2) with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inl (by omega)

/-! # Counting toolkit for windows of three -/

private theorem sum_range_succ (f : Nat → Nat) (m : Nat) :
    ((List.range (m + 1)).map f).sum =
      ((List.range m).map f).sum + f m := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

private theorem sum_range_two (f : Nat → Nat) :
    ((List.range 2).map f).sum = f 0 + f 1 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, sum_range_succ,
    show (1 : Nat) = 0 + 1 from rfl, sum_range_succ]
  simp

private theorem sum_range_three (f : Nat → Nat) :
    ((List.range 3).map f).sum = f 0 + f 1 + f 2 := by
  rw [show (3 : Nat) = 2 + 1 from rfl, sum_range_succ, sum_range_two]

/-! # The triple against small cells

The triple's members have identical bits at every member of any other
cell of size at most two: the count into a singleton is the adjacency
bit, and the count into a pair is twice the bit at either member by
`pair_odd_eq`'s both-or-neither. -/

/-- Members of the triple cell have identical bits at every member of
any other cell of size at most two. -/
theorem triple_const {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    {d : Nat} (hT : (d, d + 2) ∈ cells ptn level ctx.n)
    {c ce : Nat} (hC : (c, ce) ∈ cells ptn level ctx.n)
    (hsz : ce + 1 - c ≤ 2)
    {o o' w : Nat} (ho : o < 3) (ho' : o' < 3) (hw : w < ce + 1 - c) :
    (ctx.g[lab[d + o]!]!).testBit lab[c + w]! =
      (ctx.g[lab[d + o']!]!).testBit lab[c + w]! := by
  have hd2 : d + 2 < ctx.n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hce : ce < ctx.n := by
    have := cells_bound (by omega) hend _ hC
    omega
  have hcce := cells_le _ hC
  have hcount := hE _ hT _ hC o o' (by omega) (by omega)
  rcases Decidable.em (ce = c) with hone | htwo
  · -- a singleton
    subst hone
    have hw0 : w = 0 := by omega
    subst hw0
    rw [worksetOf_singleton, popCount_and_single,
      popCount_and_single] at hcount
    rcases hb : (ctx.g[lab[d + o]!]!).testBit lab[ce]! with _ | _ <;>
      rcases hb' : (ctx.g[lab[d + o']!]!).testBit lab[ce]! with _ | _ <;>
        rw [hb, hb'] at hcount <;> simp_all
  · -- a pair
    have hpair : ce = c + 1 := by omega
    subst hpair
    have hC' : (c, c + 1) ∈ cells ptn level ctx.n := hC
    have hodd3 : (d + 2 + 1 - d) % 2 = 1 := by omega
    have hboth := pair_odd_eq hE hps hend hinj hlb hg hsymm hC' hT
      hodd3
    have hb_o := hboth o (by omega)
    have hb_o' := hboth o' (by omega)
    -- transport the pair-side equalities to the triple side
    have hto : o ≤ 2 := by omega
    have hto' : o' ≤ 2 := by omega
    have hself_o : (ctx.g[lab[d + o]!]!).testBit lab[c]! =
        (ctx.g[lab[d + o]!]!).testBit lab[c + 1]! := by
      rw [hsymm lab[d + o]! lab[c]! (hlb (d + o) (by omega))
          (hlb c (by omega)),
        hsymm lab[d + o]! lab[c + 1]! (hlb (d + o) (by omega))
          (hlb (c + 1) (by omega))]
      exact hb_o
    have hself_o' : (ctx.g[lab[d + o']!]!).testBit lab[c]! =
        (ctx.g[lab[d + o']!]!).testBit lab[c + 1]! := by
      rw [hsymm lab[d + o']! lab[c]! (hlb (d + o') (by omega))
          (hlb c (by omega)),
        hsymm lab[d + o']! lab[c + 1]! (hlb (d + o') (by omega))
          (hlb (c + 1) (by omega))]
      exact hb_o'
    rw [count_into_cell hps hend hinj hlb hC'
        (hg _ (hlb _ (by omega))),
      count_into_cell hps hend hinj hlb hC'
        (hg _ (hlb _ (by omega))),
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
    have hbit0 : (ctx.g[lab[d + o]!]!).testBit lab[c]! =
        (ctx.g[lab[d + o']!]!).testBit lab[c]! := bitCnt_inj.mp hkey
    rcases Decidable.em (w = 0) with rfl | hw1
    · exact hbit0
    · have hw1' : w = 1 := by omega
      subst hw1'
      rw [← hself_o, ← hself_o']
      exact hbit0

/-! # The triple's internal structure

The induced graph on the triple is empty or complete: the three
off-diagonal bits are all equal, forced by the row-sum equalities of
equitability, symmetry, and looplessness (a one-regular graph on three
vertices would need an odd handshake). -/

/-- All off-diagonal internal bits of the triple agree. -/
theorem triple_internal {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    {d : Nat} (hT : (d, d + 2) ∈ cells ptn level ctx.n) :
    ∀ o o' u u', o < 3 → o' < 3 → u < 3 → u' < 3 → o ≠ o' → u ≠ u' →
      (ctx.g[lab[d + o]!]!).testBit lab[d + o']! =
        (ctx.g[lab[d + u]!]!).testBit lab[d + u']! := by
  have hd2 : d + 2 < ctx.n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hbnd : ∀ o, o < 3 → d + o < ctx.n := by
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
    rw [count_into_cell hps hend hinj hlb hT
        (hg _ (hlb _ (hbnd o ho))),
      count_into_cell hps hend hinj hlb hT
        (hg _ (hlb _ (hbnd o' ho'))),
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

/-! # The triple flip theorem

The transposition of any two triple members, fixing every other
vertex, preserves the adjacency rows. Unlike the pair flip no matching
closure is needed: under the first-branch shape every other cell has
size at most two, so the triple's relations to it are constant across
the triple (`triple_const`), and the internal bits are off-diagonally
constant (`triple_internal`). -/

section TripleFlip

variable {lab ptn : Array Nat} {level d : Nat} {f : Nat → Nat}

/-- Vertices outside the transposed pair have identical bits at the
two transposed members. -/
private theorem triple_adj_aux
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hT : (d, d + 2) ∈ cells ptn level ctx.n)
    (hsmall : ∀ q ∈ cells ptn level ctx.n, q ≠ (d, d + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    {j : Nat} (hj : j < ctx.n)
    (hjA : lab[j]! ≠ lab[d + a]!) (hjB : lab[j]! ≠ lab[d + b]!) :
    (ctx.g[lab[d + a]!]!).testBit lab[j]! =
      (ctx.g[lab[d + b]!]!).testBit lab[j]! := by
  have hd2 : d + 2 < ctx.n := by
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
    have hint := triple_internal hE hps hend hinj hlb hg hsymm hloop
      hT a (j - d) b (j - d) ha hw3 hb hw3
      (fun hcon => hwa hcon.symm) (fun hcon => hwb hcon.symm)
    rw [show d + (j - d) = j by omega] at hint
    exact hint
  · -- j sits in another, small cell
    have hqsz := hsmall q hq hqT
    have hconst := triple_const hE hps hend hinj hlb hg hsymm hT hq
      hqsz (o := a) (o' := b) (w := j - q.1) ha hb (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at hconst
    exact hconst

/-- Bit invariance under the triple transposition. -/
private theorem triple_flip_bit
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hT : (d, d + 2) ∈ cells ptn level ctx.n)
    (hsmall : ∀ q ∈ cells ptn level ctx.n, q ≠ (d, d + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    (hswap : f lab[d + a]! = lab[d + b]! ∧ f lab[d + b]! = lab[d + a]!)
    (hfix : ∀ v, v < ctx.n → v ≠ lab[d + a]! → v ≠ lab[d + b]! →
      f v = v) :
    ∀ i j, i < ctx.n → j < ctx.n →
      (ctx.g[f lab[i]!]!).testBit (f lab[j]!) =
        (ctx.g[lab[i]!]!).testBit lab[j]! := by
  have hd2 : d + 2 < ctx.n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hAn : lab[d + a]! < ctx.n := hlb (d + a) (by omega)
  have hBn : lab[d + b]! < ctx.n := hlb (d + b) (by omega)
  intro i j hi hj
  rcases Decidable.em (lab[i]! = lab[d + a]!) with hiA | hiA
  · -- lab i is the first transposed member
    rw [hiA, hswap.1]
    rcases Decidable.em (lab[j]! = lab[d + a]!) with hjA | hjA
    · rw [hjA, hswap.1, hloop _ hBn, hloop _ hAn]
    · rcases Decidable.em (lab[j]! = lab[d + b]!) with hjB | hjB
      · rw [hjB, hswap.2, hsymm lab[d + a]! lab[d + b]! hAn hBn]
      · rw [hfix lab[j]! (hlb j hj) hjA hjB]
        exact triple_adj_aux hE hps hend hinj hlb hg hsymm hloop hT
          hsmall hb ha hj hjB hjA
  · rcases Decidable.em (lab[i]! = lab[d + b]!) with hiB | hiB
    · -- lab i is the second transposed member
      rw [hiB, hswap.2]
      rcases Decidable.em (lab[j]! = lab[d + a]!) with hjA | hjA
      · rw [hjA, hswap.1, hsymm lab[d + a]! lab[d + b]! hAn hBn]
      · rcases Decidable.em (lab[j]! = lab[d + b]!) with hjB | hjB
        · rw [hjB, hswap.2, hloop _ hAn, hloop _ hBn]
        · rw [hfix lab[j]! (hlb j hj) hjA hjB]
          exact triple_adj_aux hE hps hend hinj hlb hg hsymm hloop hT
            hsmall ha hb hj hjA hjB
    · -- lab i is fixed
      rw [hfix lab[i]! (hlb i hi) hiA hiB]
      rcases Decidable.em (lab[j]! = lab[d + a]!) with hjA | hjA
      · rw [hjA, hswap.1,
          hsymm lab[i]! lab[d + b]! (hlb i hi) hBn,
          hsymm lab[i]! lab[d + a]! (hlb i hi) hAn]
        exact triple_adj_aux hE hps hend hinj hlb hg hsymm hloop hT
          hsmall hb ha hi hiB hiA
      · rcases Decidable.em (lab[j]! = lab[d + b]!) with hjB | hjB
        · rw [hjB, hswap.2,
            hsymm lab[i]! lab[d + a]! (hlb i hi) hAn,
            hsymm lab[i]! lab[d + b]! (hlb i hi) hBn]
          exact triple_adj_aux hE hps hend hinj hlb hg hsymm hloop hT
            hsmall ha hb hi hiA hiB
        · rw [hfix lab[j]! (hlb j hj) hjA hjB]

/-- The triple flip theorem: the transposition of two triple members,
fixing every other vertex, preserves the adjacency rows. -/
theorem triple_flip_rows
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hsurj : ∀ v, v < ctx.n → ∃ i, i < ctx.n ∧ lab[i]! = v)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hfb : ∀ v, v < ctx.n → f v < ctx.n)
    (hinvol : ∀ v, v < ctx.n → f (f v) = v)
    (hT : (d, d + 2) ∈ cells ptn level ctx.n)
    (hsmall : ∀ q ∈ cells ptn level ctx.n, q ≠ (d, d + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3)
    (hswap : f lab[d + a]! = lab[d + b]! ∧ f lab[d + b]! = lab[d + a]!)
    (hfix : ∀ v, v < ctx.n → v ≠ lab[d + a]! → v ≠ lab[d + b]! →
      f v = v) :
    ∀ v, v < ctx.n → ctx.g[f v]! = image f ctx.n ctx.g[v]! := by
  intro v hv
  refine Nat.eq_of_testBit_eq fun z => ?_
  rcases Decidable.em (z < ctx.n) with hz | hz
  · rw [testBit_image_invol hfb hinvol hz]
    obtain ⟨i, hi, rfl⟩ := hsurj v hv
    obtain ⟨j, hj, hjz⟩ := hsurj (f z) (hfb z hz)
    rw [← hjz]
    have hkey := triple_flip_bit hE hps hend hinj hlb hg hsymm hloop
      hT hsmall ha hb hswap hfix i j hi hj
    rw [hjz, hinvol z hz] at hkey
    rw [← hjz] at hkey
    exact hkey
  · have h1 : (ctx.g[f v]!).testBit z = false :=
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (hg _ (hfb v hv))
        (Nat.pow_le_pow_right (by omega) (by omega)))
    rw [h1, testBit_image]
    refine (List.any_eq_false.mpr fun u hu hcontra => ?_).symm
    have hun := List.mem_range.mp hu
    rw [Bool.and_eq_true, beq_iff_eq] at hcontra
    have := hfb u hun
    omega

end TripleFlip

end Hex.GraphIso.Nauty
