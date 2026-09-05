/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCellIter
import all HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.EquitableStep
import all HexGraphIso.Nauty.EquitableStep
public import HexGraphIso.Nauty.EquitableFix
import all HexGraphIso.Nauty.EquitableFix

public section

/-!
The cheapautom triple analogues (SPEC § Verified search refinement,
the code-1 arm of the store-validity obligation).

The first guard branch (`defect ≤ nontrivial + 1`) forces every cell
of the partition to be a singleton, a pair, or one triple, and any two
size-three cells to coincide. On that shape this file
proves the triple analogues of the pair flip theory:

* `triple_const`: the triple's members have identical bits at every
  member of any other cell of size at most two -- the count into a
  singleton is the adjacency bit, and the count into a pair is twice
  it by `pair_odd_eq`'s both-or-neither;
* `triple_internal`: the induced graph on the triple is empty or
  complete -- the off-diagonal bits are all equal, by the three row-sum
  equalities of equitability (a one-regular graph on three vertices
  is impossible);
* `triple_flip_rows`: the transposition of any two triple members,
  fixing every other vertex, preserves the adjacency rows. Unlike the
  pair flip no matching closure is needed: every other cell is small,
  so the triple's relations to it are constant across the triple.

This file also proves the counting pigeonhole (`labInj_surj`: an
injective bounded labelling on `n` positions is surjective, the
surjectivity hypothesis the flip theorems consume), the transposition's
self-equivalence (`cellsPerm_self_tripleSwap`/`stPerm_self_tripleSwap`:
the mapped labelling is cell-contents equivalent to the original), the
generalized single-deviation theorem (`deviation_leafRows_self`: ANY
row-preserving self-symmetry of a node carrying one child's
individualized vertex to another's mirrors discrete descents with
equal leaf rows -- the uniform door both pair and triple deviations
enter), and its packaged triple instance (`triple_deviation_leafRows`,
which constructs the concrete transposition and discharges every
hypothesis from `IterOk` + equitability + the first-branch shape).
The pair-matching closure `PairReach` and its position toolkit
(start-determinacy, start-never-second, closure members are pairs,
distinct pairs disjoint) close the file.

Remaining on top of this file, in dependency order. (1) The
pair-closure involution: define the swap of every `PairReach`-closure
pair via `Classical.choose` on "some closure pair has this vertex as
its first/second member" -- the position toolkit makes the witness
unique (start-determinacy + `pair_start_ne_second` give the two
existentials' exclusivity, `pair_cells_disj` gives distinctness of
partners) -- then discharge the S-closure hypotheses of `flip_rows` and a
`cellsPerm_self_pairFlip` (mirror of the triple one: closure pairs
swap by `List.Perm.swap`, other cells are fixed because a member of a
closure pair would place its position inside that pair's window), and
package `pair_deviation_leafRows` through `deviation_leafRows_self`
exactly as the triple instance. (2) The node invariant for the
all-leaves induction: `IterOk` + `Equitable` + the first-branch shape
(every cell size ≤ 3, one triple -- descends because `refine_frozen`
keeps closed positions closed, so every child cell sits inside a
parent cell and child triples are parent triples positionally) +
`bcount` accuracy (`bcount_breakout_eq` + `refine_bcount`), with
equitability descending by `equitable_breakout`. (3) The all-leaves
induction: two descents with the same target-position path and
discrete ends have equal leaf rows -- induction on the path; equal
offsets recurse, distinct offsets glue a deviation (pair or triple by
the target's size) and recurse below the second child on the
transported path. (4) The `noncheaplevel` event lemma and the arm-2
assembly in `StoreValid.lean`. (5) The exotic defect-four
configurations outside the first branch, per the probe.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

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

/-! # The triple's internal structure

The induced graph on the triple is empty or complete: the three
off-diagonal bits are all equal, forced by the row-sum equalities of
equitability, symmetry, and looplessness (a one-regular graph on three
vertices would need an odd handshake). -/

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

/-- Bit invariance under the triple transposition. -/
private theorem triple_flip_bit
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
    (hswap : f lab[d + a]! = lab[d + b]! ∧ f lab[d + b]! = lab[d + a]!)
    (hfix : ∀ v, v < n → v ≠ lab[d + a]! → v ≠ lab[d + b]! →
      f v = v) :
    ∀ i j, i < n → j < n →
      (ctx.g[f lab[i]!]!).mem (f lab[j]!) =
        (ctx.g[lab[i]!]!).mem lab[j]! := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hAn : lab[d + a]! < n := hlb (d + a) (by omega)
  have hBn : lab[d + b]! < n := hlb (d + b) (by omega)
  intro i j hi hj
  rcases Decidable.em (lab[i]! = lab[d + a]!) with hiA | hiA
  · -- lab i is the first transposed member
    rw [hiA, hswap.1]
    rcases Decidable.em (lab[j]! = lab[d + a]!) with hjA | hjA
    · rw [hjA, hswap.1, hloop _ hBn, hloop _ hAn]
    · rcases Decidable.em (lab[j]! = lab[d + b]!) with hjB | hjB
      · rw [hjB, hswap.2, hsymm lab[d + a]! lab[d + b]! hAn hBn]
      · rw [hfix lab[j]! (hlb j hj) hjA hjB]
        exact triple_adj_aux hE hps hend hinj hlb hsymm hloop hT
          hsmall hb ha hj hjB hjA
  · rcases Decidable.em (lab[i]! = lab[d + b]!) with hiB | hiB
    · -- lab i is the second transposed member
      rw [hiB, hswap.2]
      rcases Decidable.em (lab[j]! = lab[d + a]!) with hjA | hjA
      · rw [hjA, hswap.1, hsymm lab[d + a]! lab[d + b]! hAn hBn]
      · rcases Decidable.em (lab[j]! = lab[d + b]!) with hjB | hjB
        · rw [hjB, hswap.2, hloop _ hAn, hloop _ hBn]
        · rw [hfix lab[j]! (hlb j hj) hjA hjB]
          exact triple_adj_aux hE hps hend hinj hlb hsymm hloop hT
            hsmall ha hb hj hjA hjB
    · -- lab i is fixed
      rw [hfix lab[i]! (hlb i hi) hiA hiB]
      rcases Decidable.em (lab[j]! = lab[d + a]!) with hjA | hjA
      · rw [hjA, hswap.1,
          hsymm lab[i]! lab[d + b]! (hlb i hi) hBn,
          hsymm lab[i]! lab[d + a]! (hlb i hi) hAn]
        exact triple_adj_aux hE hps hend hinj hlb hsymm hloop hT
          hsmall hb ha hi hiB hiA
      · rcases Decidable.em (lab[j]! = lab[d + b]!) with hjB | hjB
        · rw [hjB, hswap.2,
            hsymm lab[i]! lab[d + a]! (hlb i hi) hAn,
            hsymm lab[i]! lab[d + b]! (hlb i hi) hBn]
          exact triple_adj_aux hE hps hend hinj hlb hsymm hloop hT
            hsmall ha hb hi hiA hiB
        · rw [hfix lab[j]! (hlb j hj) hjA hjB]

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
  intro v hv
  refine VSet.ext fun z => ?_
  rcases Decidable.em (z < n) with hz | hz
  · rw [mem_image_invol hfb hinvol hz]
    obtain ⟨i, hi, rfl⟩ := hsurj v hv
    obtain ⟨j, hj, hjz⟩ := hsurj (f z) (hfb z hz)
    rw [← hjz]
    have hkey := triple_flip_bit hE hps hend hinj hlb hsymm hloop
      hT hsmall ha hb hswap hfix i j hi hj
    rw [hjz, hinvol z hz] at hkey
    rw [← hjz] at hkey
    exact hkey
  · rw [VSet.mem_of_ge (by omega), VSet.mem_of_ge (by omega)]

end TripleFlip

/-! # Injective labellings are surjective

The flip theorems consume a surjectivity hypothesis; at the search's
nodes the labelling is injective and bounded, and on `n` positions
that forces surjectivity by counting. -/

private theorem sum_ind_zero {x : Nat} :
    ∀ n, ¬ x < n →
      ((List.range n).map fun v => if x = v then 1 else 0).sum = 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [sum_range_succ, sum_ind_zero n (by omega),
      ite_eq_right (by omega)]

private theorem sum_ind_one {x : Nat} :
    ∀ n, x < n →
      ((List.range n).map fun v => if x = v then 1 else 0).sum = 1
  | 0, h => absurd h (by omega)
  | n + 1, hx => by
    rw [sum_range_succ]
    rcases Decidable.em (x = n) with rfl | hne
    · rw [sum_ind_zero x (by omega), ite_eq_left rfl]
    · rw [sum_ind_one n (by omega), ite_eq_right hne]

private theorem countP_zero_of_none {p : Nat → Bool} :
    ∀ (l : List Nat), (∀ i ∈ l, ¬ p i = true) → l.countP p = 0
  | [], _ => rfl
  | i :: l, h => by
    rw [List.countP_cons,
      ite_eq_right (h i List.mem_cons_self),
      countP_zero_of_none l fun i' hi' =>
        h i' (List.mem_cons_of_mem _ hi')]

private theorem sum_buckets {lab : Array Nat} {n : Nat} :
    ∀ (l : List Nat), (∀ i ∈ l, lab[i]! < n) →
      ((List.range n).map fun v =>
        l.countP fun i => decide (lab[i]! = v)).sum = l.length
  | [], _ => by
    have hz : ∀ v ∈ List.range n,
        ([] : List Nat).countP (fun i => decide (lab[i]! = v)) = 0 :=
      fun v _ => rfl
    rw [List.map_congr_left hz, sum_map_zero]
    rfl
  | i :: l, hb => by
    have hcong : ∀ v ∈ List.range n,
        ((i :: l).countP fun i' => decide (lab[i']! = v)) =
          (l.countP fun i' => decide (lab[i']! = v)) +
            (if lab[i]! = v then 1 else 0) := by
      intro v _
      rw [List.countP_cons]
      rcases Decidable.em (lab[i]! = v) with h | h
      · rw [ite_eq_left (decide_eq_true h), ite_eq_left h]
      · rw [ite_eq_right (by simpa using h), ite_eq_right h]
    rw [List.map_congr_left hcong,
      sum_map_add (fun v => l.countP fun i' => decide (lab[i']! = v))
        (fun v => if lab[i]! = v then 1 else 0),
      sum_buckets l fun i' hi' => hb i' (List.mem_cons_of_mem _ hi'),
      sum_ind_one n (hb i List.mem_cons_self), List.length_cons]

private theorem bucket_le_one {lab : Array Nat} {n v : Nat}
    (hinj : LabInj lab n) :
    ∀ m, m ≤ n →
      ((List.range m).countP fun i => decide (lab[i]! = v)) ≤ 1
  | 0, _ => by
    rw [List.range_zero, List.countP_nil]
    omega
  | m + 1, hm => by
    rw [List.range_succ, List.countP_append, List.countP_cons,
      List.countP_nil]
    rcases Decidable.em (lab[m]! = v) with h | h
    · rw [ite_eq_left (decide_eq_true h)]
      have hz : ((List.range m).countP fun i =>
          decide (lab[i]! = v)) = 0 := by
        refine countP_zero_of_none _ fun i hi hp => ?_
        have him := List.mem_range.mp hi
        have hval : lab[i]! = v := of_decide_eq_true hp
        have := hinj i m (by omega) (by omega) (hval.trans h.symm)
        omega
      omega
    · rw [ite_eq_right (by simpa using h)]
      have := bucket_le_one (v := v) hinj m (by omega)
      omega

private theorem sum_le_of_le_one {f : Nat → Nat} :
    ∀ n, (∀ u, u < n → f u ≤ 1) → ((List.range n).map f).sum ≤ n
  | 0, _ => by simp
  | n + 1, hf => by
    rw [sum_range_succ]
    have h1 := sum_le_of_le_one n fun u hu => hf u (by omega)
    have h2 := hf n (by omega)
    omega

private theorem sum_le_pred_of_zero_at {f : Nat → Nat} :
    ∀ n v, v < n → f v = 0 → (∀ u, u < n → f u ≤ 1) →
      ((List.range n).map f).sum ≤ n - 1
  | 0, _, hv, _, _ => absurd hv (by omega)
  | n + 1, v, hv, hz, hle => by
    rw [sum_range_succ]
    rcases Decidable.em (v = n) with heq | hne
    · have hz' : f n = 0 := by
        rw [← heq]
        exact hz
      have h1 := sum_le_of_le_one n fun u hu => hle u (by omega)
      omega
    · have h1 := sum_le_pred_of_zero_at n v (by omega) hz
        fun u hu => hle u (by omega)
      have h2 := hle n (by omega)
      omega

/-- An injective bounded labelling on `n` positions hits every
vertex. -/
theorem labInj_surj {lab : Array Nat} {n : Nat}
    (hsz : n ≤ lab.size) (hlab : LabOk lab n) (hinj : LabInj lab n) :
    ∀ v, v < n → ∃ i, i < n ∧ lab[i]! = v := by
  intro v hv
  rcases Classical.em (∃ i, i < n ∧ lab[i]! = v) with h | h
  · exact h
  · exfalso
    have htotal : ((List.range n).map fun u =>
        (List.range n).countP fun i => decide (lab[i]! = u)).sum = n := by
      rw [sum_buckets (List.range n) fun i hi =>
        hlab i (by
          have := List.mem_range.mp hi
          omega), List.length_range]
    have hzero : ((List.range n).countP fun i =>
        decide (lab[i]! = v)) = 0 := by
      refine countP_zero_of_none _ fun i hi hp => ?_
      exact h ⟨i, List.mem_range.mp hi, of_decide_eq_true hp⟩
    have hbound := sum_le_pred_of_zero_at
      (f := fun u => (List.range n).countP fun i =>
        decide (lab[i]! = u)) n v hv hzero
      fun u _ => bucket_le_one hinj n (Nat.le_refl _)
    omega

/-! # The self-equivalence of a triple transposition

A transposition of two triple members is a cell-contents permutation
of the labelling against itself: the triple's window is swapped in
place and every other cell is fixed pointwise. Packaged as `StPerm`
against the renamed copy, it feeds the bisimulation, giving the
single-deviation theorem at a triple target. -/

section TripleSelf

variable {lab ptn : Array Nat} {level d : Nat}

/-- The mapped labelling is cell-contents equivalent to the original
when the map transposes two members of one triple cell and fixes every
other vertex. -/
theorem cellsPerm_self_tripleSwap {σ : Renaming n}
    (hps : ptn.size = n) (hlsz : lab.size = n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : LabInj lab n) (hlb : LabOk lab n)
    (hT : (d, d + 2) ∈ cells ptn level n)
    {a b : Nat} (ha : a < 3) (hb : b < 3) (hab : a ≠ b)
    (hswap : σ.toFun lab[d + a]! = lab[d + b]! ∧
      σ.toFun lab[d + b]! = lab[d + a]!)
    (hfix : ∀ v, v < n → v ≠ lab[d + a]! → v ≠ lab[d + b]! →
      σ.toFun v = v) :
    cellsPerm ptn level lab (lab.map σ.toFun) := by
  have hd2 : d + 2 < n := by
    have := cells_bound (by omega) hend _ hT
    omega
  have hIsT : IsCell ptn level d 3 := by
    have h := cells_isCell (by omega) hend _ hT
    rw [show d + 2 + 1 - d = 3 by omega] at h
    exact h
  intro α len hIs
  rcases Decidable.em (α < n) with han | han
  · -- in range
    have hcross : α + len ≤ n := by
      have := isCell_no_cross hend hIs (by omega)
      omega
    have hmapAt : ∀ o, o < len →
        (lab.map σ.toFun)[α + o]! = σ.toFun lab[α + o]! := by
      intro o ho
      exact getElem!_map_of_lt _ _ (by rw [hlsz]; omega)
    rcases isCell_disj_or_eq hIs hIsT with ⟨heq1, heq2⟩ | hd1 | hd1
    · -- the triple's own run: the window is swapped in place
      subst heq2
      rw [← heq1] at hswap hfix
      have hα2 : α + 2 < n := by omega
      have hval : ∀ w, w < 3 → σ.toFun lab[α + w]! =
          if w = a then lab[α + b]!
          else if w = b then lab[α + a]! else lab[α + w]! := by
        intro w hw
        rcases Decidable.em (w = a) with rfl | hwa
        · rw [ite_eq_left rfl]
          exact hswap.1
        · rcases Decidable.em (w = b) with rfl | hwb
          · rw [ite_eq_right hwa, ite_eq_left rfl]
            exact hswap.2
          · rw [ite_eq_right hwa, ite_eq_right hwb]
            refine hfix _ (hlb _ (by rw [hlsz]; omega)) ?_ ?_
            · intro hcon
              have := hinj (α + w) (α + a) (by omega) (by omega) hcon
              omega
            · intro hcon
              have := hinj (α + w) (α + b) (by omega) (by omega) hcon
              omega
      have hseg : segN lab α 3 =
          lab[α]! :: lab[α + 1]! :: lab[α + 2]! :: [] := by
        rw [show (3 : Nat) = 2 + 1 from rfl, segN_cons,
          show (2 : Nat) = 1 + 1 from rfl, segN_cons,
          show (1 : Nat) = 0 + 1 from rfl, segN_cons, segN_zero]
      have hsegm : segN (lab.map σ.toFun) α 3 =
          σ.toFun lab[α]! :: σ.toFun lab[α + 1]! ::
            σ.toFun lab[α + 2]! :: [] := by
        rw [show (3 : Nat) = 2 + 1 from rfl, segN_cons,
          show (2 : Nat) = 1 + 1 from rfl, segN_cons,
          show (1 : Nat) = 0 + 1 from rfl, segN_cons, segN_zero,
          getElem!_map_of_lt σ.toFun lab (by rw [hlsz]; omega),
          getElem!_map_of_lt σ.toFun lab (by rw [hlsz]; omega),
          getElem!_map_of_lt σ.toFun lab (by rw [hlsz]; omega)]
      rw [hseg, hsegm]
      have hv0 := hval 0 (by omega)
      have hv1 := hval 1 (by omega)
      have hv2 := hval 2 (by omega)
      rw [Nat.add_zero] at hv0
      have ha3 : a = 0 ∨ a = 1 ∨ a = 2 := by omega
      have hb3 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
      rcases ha3 with rfl | rfl | rfl <;> rcases hb3 with rfl | rfl | rfl
      · omega
      · -- swap 0 1
        rw [hv0, hv1, hv2, ite_eq_left rfl,
          ite_eq_right (by omega), ite_eq_left rfl,
          ite_eq_right (by omega), ite_eq_right (by omega),
          Nat.add_zero]
        exact List.Perm.swap _ _ _
      · -- swap 0 2
        rw [hv0, hv1, hv2, ite_eq_left rfl,
          ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left rfl, Nat.add_zero]
        refine List.Perm.trans (List.Perm.cons _
          (List.Perm.swap _ _ _)) ?_
        refine List.Perm.trans (List.Perm.swap _ _ _) ?_
        exact List.Perm.cons _ (List.Perm.swap _ _ _)
      · -- swap 1 0
        rw [hv0, hv1, hv2, ite_eq_right (by omega),
          ite_eq_left rfl, ite_eq_left rfl,
          ite_eq_right (by omega), ite_eq_right (by omega),
          Nat.add_zero]
        exact List.Perm.swap _ _ _
      · omega
      · -- swap 1 2
        rw [hv0, hv1, hv2, ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left rfl,
          ite_eq_right (by omega), ite_eq_left rfl]
        exact List.Perm.cons _ (List.Perm.swap _ _ _)
      · -- swap 2 0
        rw [hv0, hv1, hv2, ite_eq_right (by omega),
          ite_eq_left rfl, ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left rfl, Nat.add_zero]
        refine List.Perm.trans (List.Perm.cons _
          (List.Perm.swap _ _ _)) ?_
        refine List.Perm.trans (List.Perm.swap _ _ _) ?_
        exact List.Perm.cons _ (List.Perm.swap _ _ _)
      · -- swap 2 1
        rw [hv0, hv1, hv2, ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left rfl,
          ite_eq_left rfl, ite_eq_right (by omega)]
        exact List.Perm.cons _ (List.Perm.swap _ _ _)
      · omega
    · -- a run left of the triple: every member is fixed
      have hfixseg : segN (lab.map σ.toFun) α len = segN lab α len := by
        refine segN_congr fun o ho => ?_
        rw [getElem!_map_of_lt σ.toFun lab (by rw [hlsz]; omega)]
        refine hfix _ (hlb _ (by rw [hlsz]; omega)) ?_ ?_
        · intro hcon
          have := hinj (α + o) (d + a) (by omega) (by omega) hcon
          omega
        · intro hcon
          have := hinj (α + o) (d + b) (by omega) (by omega) hcon
          omega
      rw [hfixseg]
    · -- a run right of the triple: every member is fixed
      have hfixseg : segN (lab.map σ.toFun) α len = segN lab α len := by
        refine segN_congr fun o ho => ?_
        rw [getElem!_map_of_lt σ.toFun lab (by rw [hlsz]; omega)]
        refine hfix _ (hlb _ (by rw [hlsz]; omega)) ?_ ?_
        · intro hcon
          have := hinj (α + o) (d + a) (by omega) (by omega) hcon
          omega
        · intro hcon
          have := hinj (α + o) (d + b) (by omega) (by omega) hcon
          omega
      rw [hfixseg]
  · -- beyond the bound: phantom singleton
    have hlen1 : len = 1 := isCell_oob hIs (by omega)
    rw [hlen1, segN_cons, segN_zero, segN_cons, segN_zero]
    rw [getElem!_oob (by omega : lab.size ≤ α),
      getElem!_oob (by rw [Array.size_map]; omega :
        (lab.map σ.toFun).size ≤ α)]

end TripleSelf

/-- The transposition packaged as a state self-equivalence. -/
theorem stPerm_self_tripleSwap {σ : Renaming n} {st : RefineSt n}
    {level d : Nat}
    (hok : StOk n level st) (hinj : LabInj st.lab n)
    (hT : (d, d + 2) ∈ cells st.ptn level n)
    {a b : Nat} (ha : a < 3) (hb : b < 3) (hab : a ≠ b)
    (hswap : σ.toFun st.lab[d + a]! = st.lab[d + b]! ∧
      σ.toFun st.lab[d + b]! = st.lab[d + a]!)
    (hfix : ∀ v, v < n → v ≠ st.lab[d + a]! →
      v ≠ st.lab[d + b]! → σ.toFun v = v) :
    StPerm level st (mapSt σ st) := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show (st.lab.map σ.toFun).size = st.lab.size
    rw [Array.size_map]
  · show cellsPerm st.ptn level st.lab (st.lab.map σ.toFun)
    exact cellsPerm_self_tripleSwap hok.ptnSize hok.labSize hok.ptnEnd
      hinj hok.labOk hT ha hb hab hswap hfix

/-- The generalized single-deviation theorem: a self-symmetry of the
node carrying one child's individualized vertex to another's mirrors
any discrete descent below the first child, with equal leaf rows. -/
theorem deviation_leafRows_self {σ : Renaming n} {st : RefineSt n}
    {level tc e oU oV level' : Nat} {U' : RefineSt n}
    (hIt : IterOk ctx level st) (hlvl : level < n)
    (hg : RowsMap σ ctx.g ctx.g)
    (hsp : StPerm level st (mapSt σ st))
    (hcell : (tc, e) ∈ cells st.ptn level n) (hne : tc < e)
    (hoU : oU ≤ e - tc) (hoV : oV ≤ e - tc)
    (hvv : st.lab[tc + oV]! = σ.toFun st.lab[tc + oU]!)
    (hdesc : Descends ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + oU]!) level' U')
    (hdisc : ∀ q, q < n → U'.ptn[q]! ≤ level') :
    ∃ V', Descends ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + oV]!) level' V' ∧
      leafRows ctx V'.lab = leafRows ctx U'.lab := by
  have hsp' := stPerm_child hg hsp hIt hcell hne hoV hoU hvv
  have hU0 := iterOk_child hIt hlvl hcell hne hoU
  exact descends_leafRows hg hdesc hU0 hsp' hdisc

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
  -- the concrete transposition
  refine ?_
  let f : Nat → Nat := fun v =>
    if v = st.lab[tc + a]! then st.lab[tc + b]!
    else if v = st.lab[tc + b]! then st.lab[tc + a]! else v
  have hswapf : f st.lab[tc + a]! = st.lab[tc + b]! ∧
      f st.lab[tc + b]! = st.lab[tc + a]! := by
    constructor
    · show (if st.lab[tc + a]! = st.lab[tc + a]! then _ else _) = _
      rw [ite_eq_left rfl]
    · show (if st.lab[tc + b]! = st.lab[tc + a]! then _ else _) = _
      rw [ite_eq_right (fun h => hABne h.symm), ite_eq_left rfl]
  have hfixf : ∀ v, v < n → v ≠ st.lab[tc + a]! →
      v ≠ st.lab[tc + b]! → f v = v := by
    intro v _ hvA hvB
    show (if v = st.lab[tc + a]! then _ else _) = _
    rw [ite_eq_right hvA, ite_eq_right hvB]
  have hfb : ∀ v, v < n → f v < n := by
    intro v hv
    rcases Decidable.em (v = st.lab[tc + a]!) with rfl | hvA
    · rw [hswapf.1]
      exact hBn
    · rcases Decidable.em (v = st.lab[tc + b]!) with rfl | hvB
      · rw [hswapf.2]
        exact hAn
      · rw [hfixf v hv hvA hvB]
        exact hv
  have hinvol : ∀ v, v < n → f (f v) = v := by
    intro v hv
    rcases Decidable.em (v = st.lab[tc + a]!) with rfl | hvA
    · rw [hswapf.1, hswapf.2]
    · rcases Decidable.em (v = st.lab[tc + b]!) with rfl | hvB
      · rw [hswapf.2, hswapf.1]
      · rw [hfixf v hv hvA hvB, hfixf v hv hvA hvB]
  have hsurj := labInj_surj
    (by rw [hIt.ok.labSize] ; exact Nat.le_refl _ : n ≤ _)
    hIt.ok.labOk hIt.inj
  have hrows := triple_flip_rows hE hIt.ok.ptnSize hIt.ok.ptnEnd
    hIt.inj hlb' hsurj hsymm hloop hfb hinvol hT hsmall ha hb
    hswapf hfixf
  have hgmap := rowsMap_of_flip_rows hgsz hfb hinvol hrows
  have hswapσ : (renamingOfFlip f n hfb hinvol).toFun
        st.lab[tc + a]! = st.lab[tc + b]! ∧
      (renamingOfFlip f n hfb hinvol).toFun
        st.lab[tc + b]! = st.lab[tc + a]! := by
    constructor
    · rw [show (renamingOfFlip f n hfb hinvol).toFun
          st.lab[tc + a]! = f st.lab[tc + a]! from
        renamingOfFlip_at hfb hinvol hAn]
      exact hswapf.1
    · rw [show (renamingOfFlip f n hfb hinvol).toFun
          st.lab[tc + b]! = f st.lab[tc + b]! from
        renamingOfFlip_at hfb hinvol hBn]
      exact hswapf.2
  have hfixσ : ∀ v, v < n → v ≠ st.lab[tc + a]! →
      v ≠ st.lab[tc + b]! →
      (renamingOfFlip f n hfb hinvol).toFun v = v := by
    intro v hv hvA hvB
    rw [show (renamingOfFlip f n hfb hinvol).toFun v = f v from
      renamingOfFlip_at hfb hinvol hv]
    exact hfixf v hv hvA hvB
  have hsp := stPerm_self_tripleSwap hIt.ok hIt.inj hT ha hb hab
    hswapσ hfixσ
  have hvv : st.lab[tc + b]! =
      (renamingOfFlip f n hfb hinvol).toFun st.lab[tc + a]! :=
    hswapσ.1.symm
  exact ⟨renamingOfFlip f n hfb hinvol, hgmap, hsp, hvv⟩

/-- A deviation at a triple target under the first-branch shape:
descents below any two of its children reach leaves with the same
rows. -/
theorem triple_deviation_leafRows {st : RefineSt n}
    {level tc level' : Nat} {U' : RefineSt n}
    (hIt : IterOk ctx level st) (hlvl : level < n)
    (hgsz : ctx.g.size = n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hE : Equitable ctx level st.lab st.ptn)
    (hT : (tc, tc + 2) ∈ cells st.ptn level n)
    (hsmall : ∀ q ∈ cells st.ptn level n, q ≠ (tc, tc + 2) →
      q.2 + 1 - q.1 ≤ 2)
    {a b : Nat} (ha : a < 3) (hb : b < 3) (hab : a ≠ b)
    (hdesc : Descends ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + a]!) level' U')
    (hdisc : ∀ q, q < n → U'.ptn[q]! ≤ level') :
    ∃ V', Descends ctx (level + 1)
      (childSt ctx level st tc st.lab[tc + b]!) level' V' ∧
      leafRows ctx V'.lab = leafRows ctx U'.lab := by
  obtain ⟨σ, hgmap, hsp, hvv⟩ := triple_flip_data hIt hgsz hsymm
    hloop hE hT hsmall ha hb hab
  exact deviation_leafRows_self hIt hlvl hgmap hsp hT (by omega)
    (show a ≤ tc + 2 - tc by omega) (show b ≤ tc + 2 - tc by omega)
    hvv hdesc hdisc

/-! # The pair-matching closure

The pair deviation needs the involution swapping every pair in the
`PairMatch`-reachability closure of the target pair. This section
defines the closure and proves the position facts its construction
consumes: a cell is determined by its start, a pair start is never
another pair's second position, and every closure member is a pair
cell. -/

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
