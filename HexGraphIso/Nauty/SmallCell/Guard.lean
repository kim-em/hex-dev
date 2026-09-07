/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.SmallCell.Count
public import HexGraphIso.Nauty.SmallCell.Flip
public import HexGraphIso.Nauty.Invariant.Store
import all HexGraphIso.Nauty.Equitable.Basic

public section

/-!
The cheapautom guard and the flip theorem at pair cells.

`cheapautom` is nauty's cheap sufficient condition for every leaf of
the subtree below a node to realize an automorphism with the first
leaf, so that the admitted scatter needs no `isautom` scan. This file
builds the theory justifying it on top of `refine_equitable`:

* the guard characterization: `cheapautom` holds exactly when the
  partition's defect (positions minus cells) is at most the number of
  nontrivial cells plus one, or at most four;
* the structure of an equitable partition at small cells: a pair cell
  meets any other cell in a constant-count pattern, which for another
  pair is empty, complete, or one of the two perfect matchings, for a
  singleton is both-or-neither, and for a cell of odd size is empty or
  complete (the double-counting parity argument);
* the flip theorem: an involution swapping the vertices of a
  matching-closed set of pair cells and fixing every other vertex
  preserves the adjacency rows, so any array realizing it passes
  `checkAutom`.

`SmallCell/Branch` carries these results down the search subtree and
`SmallCell/Transitive` assembles them into `stabilizer_transitive`.
This file states rows preservation only, with no per-flip `checkAutom`
wrapper: the admitted scatter passes `checkAutom` through
`checkAutom_scatter_of_leafRows_eq`.

The file ends with the cell-membership facts the descent
classification consumes.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-! # The guard characterization -/

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

/-- `cheapautom`'s scan aligned with the partition's cell list: the
first component counts down once per cell and the second counts the
nontrivial cells. -/
theorem cheapautom_go_cells {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel i k nnt : Nat), (i = 0 ∨ ptn[i - 1]! ≤ level) →
      cheapautom.go ptn level fuel i k nnt =
        (k - (cells.go ptn level nn fuel i).length,
          nnt + (cells.go ptn level nn fuel i).countP fun p =>
            decide (p.1 < p.2))
  | 0, i, k, nnt, _ => by
    rw [cheapautom.go, cells.go]
    simp
  | fuel + 1, i, k, nnt, hstart => by
    rw [cheapautom.go, cells.go, hps]
    rcases Decidable.em (i < nn) with hlt | hge
    · rw [ite_eq_left hlt, ite_eq_left hlt]
      rcases Decidable.em (ptn[i]! > level) with ho | hc
      · rw [ite_eq_left ho]
        have hi1 : i + 1 < ptn.size := by
          rcases Decidable.em (i = ptn.size - 1) with rfl | hne
          · omega
          · omega
        have hce : cellEnd ptn level i = cellEnd ptn level (i + 1) :=
          cellEnd_succ_of_open (by omega) ho
        have hnext : cellEnd ptn level (i + 1) + 1 = 0 ∨
            ptn[cellEnd ptn level (i + 1) + 1 - 1]! ≤ level := by
          right
          rw [show cellEnd ptn level (i + 1) + 1 - 1 =
            cellEnd ptn level (i + 1) by omega, cellEnd]
          exact cellEnd_go_end hend _ _ hi1 (by omega)
        rw [cheapautom_go_cells hps hend fuel _ (k - 1) (nnt + 1) hnext]
        have hnt : i < cellEnd ptn level (i + 1) := by
          have := cellEnd_ge (ptn := ptn) (level := level) (i := i + 1)
          omega
        rw [hce]
        simp only [List.length_cons, List.countP_cons]
        rw [ite_eq_left (decide_eq_true hnt)]
        simp only [Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
      · rw [ite_eq_right hc]
        have hce : cellEnd ptn level i = i :=
          cellEnd_of_closed (by omega) hc
        have hnext : i + 1 = 0 ∨ ptn[i + 1 - 1]! ≤ level := by
          right
          rw [show i + 1 - 1 = i by omega]
          omega
        rw [cheapautom_go_cells hps hend fuel _ (k - 1) nnt hnext]
        rw [hce]
        simp only [List.length_cons, List.countP_cons]
        rw [ite_eq_right (by simp : ¬ decide (i < i) = true)]
        simp only [Prod.mk.injEq]
        exact ⟨by omega, by omega⟩
    · rw [ite_eq_right hge, ite_eq_right hge]
      simp

/-- The cell sizes of the partition sum to the vertex count. -/
theorem cells_go_sizes_sum {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel i : Nat), nn ≤ fuel + i →
      ((cells.go ptn level nn fuel i).map fun p =>
        p.2 + 1 - p.1).sum = nn - i
  | 0, i, hf => by
    rw [cells.go]
    simp
    omega
  | fuel + 1, i, hf => by
    rw [cells.go]
    rcases Decidable.em (i < nn) with hlt | hge
    · rw [ite_eq_left hlt]
      have hlt' : cellEnd ptn level i < nn := by
        rw [← hps]
        exact cellEnd_lt (by omega) hend
      have hge' : i ≤ cellEnd ptn level i := cellEnd_ge
      rw [List.map_cons, List.sum_cons,
        cells_go_sizes_sum hps hend fuel (cellEnd ptn level i + 1)
          (by omega)]
      omega
    · rw [ite_eq_right hge]
      simp
      omega

/-- The guard characterized: `cheapautom` holds exactly when the
defect (vertices minus cells) is at most the nontrivial cell count
plus one, or at most four. -/
theorem cheapautom_iff {ptn : Array Nat} {level nn : Nat}
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level) :
    cheapautom ptn level nn = true ↔
      (nn - (cells ptn level nn).length ≤
        (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1 ∨
       nn - (cells ptn level nn).length ≤ 4) := by
  rw [cheapautom, cells,
    cheapautom_go_cells hps hend nn 0 nn 0 (Or.inl rfl)]
  simp

/-- Swapping both pairs preserves adjacency: the bits between two pair
cells of an equitable partition satisfy the two cross equalities, in
every configuration (empty, complete, or either matching). -/
theorem pair_swap_eq {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {c d : Nat} (hP : (c, c + 1) ∈ cells ptn level n)
    (hQ : (d, d + 1) ∈ cells ptn level n) :
    (ctx.g[lab[c]!]!).mem lab[d]! =
      (ctx.g[lab[c + 1]!]!).mem lab[d + 1]! ∧
    (ctx.g[lab[c]!]!).mem lab[d + 1]! =
      (ctx.g[lab[c + 1]!]!).mem lab[d]! := by
  have hc1 : c + 1 < n := by
    have := cells_bound (by omega) hend _ hP
    omega
  have hd1 : d + 1 < n := by
    have := cells_bound (by omega) hend _ hQ
    omega
  have h1 := hE _ hP _ hQ 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at h1
  rw [count_into_cell hps hend hinj hQ,
    count_into_cell hps hend hinj hQ,
    show d + 1 + 1 - d = 2 by omega, sum_range_two, sum_range_two] at h1
  simp only [Nat.add_zero] at h1
  have h2 := hE _ hQ _ hP 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at h2
  rw [count_into_cell hps hend hinj hP,
    count_into_cell hps hend hinj hP,
    show c + 1 + 1 - c = 2 by omega, sum_range_two, sum_range_two] at h2
  simp only [Nat.add_zero] at h2
  rw [bitCnt_symm hsymm (hlb d (by omega)) (hlb c (by omega)),
    bitCnt_symm hsymm (hlb d (by omega)) (hlb (c + 1) hc1),
    bitCnt_symm hsymm (hlb (d + 1) hd1) (hlb c (by omega)),
    bitCnt_symm hsymm (hlb (d + 1) hd1) (hlb (c + 1) hc1)] at h2
  exact ⟨bitCnt_inj.mp (by omega), bitCnt_inj.mp (by omega)⟩

/-- The matching configuration between two pair cells: each member of
one pair is adjacent to exactly one member of the other, in one of the
two consistent ways. -/
def PairMatch (g : Array (VSet n)) (x y z t : Nat) : Prop :=
  ((g[x]!).mem z = true ∧ (g[y]!).mem t = true ∧
    (g[x]!).mem t = false ∧ (g[y]!).mem z = false) ∨
  ((g[x]!).mem t = true ∧ (g[y]!).mem z = true ∧
    (g[x]!).mem z = false ∧ (g[y]!).mem t = false)

/-- Between two non-matching pair cells of an equitable partition the
bits are insensitive to swapping either pair alone. -/
theorem pair_eq_of_not_match {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {c d : Nat} (hP : (c, c + 1) ∈ cells ptn level n)
    (hQ : (d, d + 1) ∈ cells ptn level n)
    (hnm : ¬ PairMatch ctx.g lab[c]! lab[c + 1]! lab[d]! lab[d + 1]!) :
    (ctx.g[lab[c]!]!).mem lab[d]! =
      (ctx.g[lab[c + 1]!]!).mem lab[d]! ∧
    (ctx.g[lab[c]!]!).mem lab[d + 1]! =
      (ctx.g[lab[c + 1]!]!).mem lab[d + 1]! := by
  obtain ⟨h1, h2⟩ :=
    pair_swap_eq hE hps hend hinj hlb hsymm hP hQ
  rw [PairMatch] at hnm
  rcases hp : (ctx.g[lab[c]!]!).mem lab[d]! with _ | _ <;>
    rcases hq : (ctx.g[lab[c]!]!).mem lab[d + 1]! with _ | _ <;>
      rw [hp] at h1 <;> rw [hq] at h2 <;>
        rw [hp, hq] at hnm <;> simp_all

/-- The members of a pair cell have identical bits at every member of
a cell of odd size: parity forces the count between them to be empty
or complete. -/
theorem pair_odd_eq {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {c d e : Nat} (hP : (c, c + 1) ∈ cells ptn level n)
    (hD : (d, e) ∈ cells ptn level n)
    (hodd : (e + 1 - d) % 2 = 1) :
    ∀ o, o < e + 1 - d →
      (ctx.g[lab[c]!]!).mem lab[d + o]! =
        (ctx.g[lab[c + 1]!]!).mem lab[d + o]! := by
  have hc1 : c + 1 < n := by
    have := cells_bound (by omega) hend _ hP
    omega
  have hde : d ≤ e := cells_le _ hD
  have he : e < n := by
    have := cells_bound (by omega) hend _ hD
    omega
  have hxy := hE _ hP _ hD 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at hxy
  rw [count_into_cell hps hend hinj hD,
    count_into_cell hps hend hinj hD]
    at hxy
  have hB : ∀ o, o < e + 1 - d →
      bitCnt ctx.g[lab[c]!]! lab[d + o]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]! =
      bitCnt ctx.g[lab[c]!]! lab[d]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d]! := by
    intro o ho
    have h := hE _ hD _ hP o 0 (by omega) (by omega)
    simp only [Nat.add_zero] at h
    rw [count_into_cell hps hend hinj hP,
      count_into_cell hps hend hinj hP,
      show c + 1 + 1 - c = 2 by omega, sum_range_two, sum_range_two]
      at h
    simp only [Nat.add_zero] at h
    rw [bitCnt_symm hsymm (hlb (d + o) (by omega)) (hlb c (by omega)),
      bitCnt_symm hsymm (hlb (d + o) (by omega)) (hlb (c + 1) hc1),
      bitCnt_symm hsymm (hlb d (by omega)) (hlb c (by omega)),
      bitCnt_symm hsymm (hlb d (by omega)) (hlb (c + 1) hc1)] at h
    exact h
  have hsum : ((List.range (e + 1 - d)).map fun o =>
      bitCnt ctx.g[lab[c]!]! lab[d + o]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]!).sum =
      (e + 1 - d) * (bitCnt ctx.g[lab[c]!]! lab[d]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d]!) := by
    rw [List.map_congr_left fun o ho =>
      hB o (List.mem_range.mp ho), sum_range_const]
  rw [sum_map_add] at hsum
  have hcD : bitCnt ctx.g[lab[c]!]! lab[d]! +
      bitCnt ctx.g[lab[c + 1]!]! lab[d]! ≤ 2 := by
    have := bitCnt_le_one ctx.g[lab[c]!]! lab[d]!
    have := bitCnt_le_one ctx.g[lab[c + 1]!]! lab[d]!
    omega
  intro o ho
  have hcases : bitCnt ctx.g[lab[c]!]! lab[d]! +
      bitCnt ctx.g[lab[c + 1]!]! lab[d]! = 0 ∨
    bitCnt ctx.g[lab[c]!]! lab[d]! +
      bitCnt ctx.g[lab[c + 1]!]! lab[d]! = 1 ∨
    bitCnt ctx.g[lab[c]!]! lab[d]! +
      bitCnt ctx.g[lab[c + 1]!]! lab[d]! = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · rw [h0, Nat.mul_zero] at hsum
    have hx0 : ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[lab[c]!]! lab[d + o]!).sum = 0 := by omega
    have hy0 : ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]!).sum = 0 := by omega
    rw [bitCnt_eq_zero.mp (sum_range_eq_zero _ hx0 o ho),
      bitCnt_eq_zero.mp (sum_range_eq_zero _ hy0 o ho)]
  · rw [h1, Nat.mul_one] at hsum
    omega
  · rw [h2] at hsum
    have hx : ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[lab[c]!]! lab[d + o]!).sum = e + 1 - d := by
      have hlx := sum_range_le
        (fun o => bitCnt ctx.g[lab[c]!]! lab[d + o]!) (e + 1 - d)
        fun o _ => bitCnt_le_one ..
      have hly := sum_range_le
        (fun o => bitCnt ctx.g[lab[c + 1]!]! lab[d + o]!) (e + 1 - d)
        fun o _ => bitCnt_le_one ..
      omega
    have hy : ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]!).sum = e + 1 - d := by
      have hlx := sum_range_le
        (fun o => bitCnt ctx.g[lab[c]!]! lab[d + o]!) (e + 1 - d)
        fun o _ => bitCnt_le_one ..
      omega
    rw [bitCnt_eq_one.mp (sum_range_eq_len _
        (fun o _ => bitCnt_le_one ..) hx o ho),
      bitCnt_eq_one.mp (sum_range_eq_len _
        (fun o _ => bitCnt_le_one ..) hy o ho)]

/-! # The flip theorem -/

section Flip

variable {lab ptn : Array Nat} {level : Nat} {S : Nat → Prop}
  {f : Nat → Nat}

/-- The members of a flipped pair have identical bits at every member
of an unflipped cell, given matching closure and odd unflipped
sizes. -/
private theorem flip_bit_aux
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hSclosed : ∀ p ∈ cells ptn level n,
      ∀ q ∈ cells ptn level n, S p.1 → q.2 = q.1 + 1 →
        PairMatch ctx.g lab[p.1]! lab[p.1 + 1]! lab[q.1]! lab[q.1 + 1]! →
        S q.1)
    (hOdd : ∀ q ∈ cells ptn level n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1)
    {c : Nat} (hP : (c, c + 1) ∈ cells ptn level n) (hSc : S c)
    {q : Nat × Nat} (hq : q ∈ cells ptn level n) (hnq : ¬ S q.1)
    {j : Nat} (hj1 : q.1 ≤ j) (hj2 : j ≤ q.2) :
    (ctx.g[lab[c]!]!).mem lab[j]! =
      (ctx.g[lab[c + 1]!]!).mem lab[j]! := by
  rcases Classical.em (q.2 = q.1 + 1) with hqp | hqnp
  · have hq' : (q.1, q.1 + 1) ∈ cells ptn level n := by
      rw [← hqp]
      exact hq
    have hnm : ¬ PairMatch ctx.g lab[c]! lab[c + 1]!
        lab[q.1]! lab[q.1 + 1]! :=
      fun hm => hnq (hSclosed _ hP _ hq hSc hqp hm)
    obtain ⟨h1, h2⟩ :=
      pair_eq_of_not_match hE hps hend hinj hlb hsymm hP hq' hnm
    rcases Decidable.em (j = q.1) with rfl | hne
    · exact h1
    · have : j = q.1 + 1 := by omega
      rw [this]
      exact h2
  · have hodd := hOdd _ hq hqnp
    have h := pair_odd_eq hE hps hend hinj hlb hsymm hP hq hodd
      (j - q.1) (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at h
    exact h

/-- The flip theorem: an involution swapping the vertices of a
matching-closed set of pair cells and fixing every other vertex
preserves the adjacency rows. -/
theorem flip_rows
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsurj : ∀ v, v < n → ∃ i, i < n ∧ lab[i]! = v)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (_hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
    (hfb : ∀ v, v < n → f v < n)
    (hinvol : ∀ v, v < n → f (f v) = v)
    (hSpair : ∀ p ∈ cells ptn level n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells ptn level n, S p.1 →
      f lab[p.1]! = lab[p.1 + 1]! ∧ f lab[p.1 + 1]! = lab[p.1]!)
    (hSfix : ∀ p ∈ cells ptn level n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 → f lab[p.1 + o]! = lab[p.1 + o]!)
    (hSclosed : ∀ p ∈ cells ptn level n,
      ∀ q ∈ cells ptn level n, S p.1 → q.2 = q.1 + 1 →
        PairMatch ctx.g lab[p.1]! lab[p.1 + 1]! lab[q.1]! lab[q.1 + 1]! →
        S q.1)
    (hOdd : ∀ q ∈ cells ptn level n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1) :
    ∀ v, v < n → ctx.g[f v]! = (ctx.g[v]!).image f := by
  let P : Nat → Nat → Prop := fun u v => ∃ c,
    (c, c + 1) ∈ cells ptn level n ∧ S c ∧ u = lab[c]! ∧ v = lab[c + 1]!
  have hbound : ∀ c, (c, c + 1) ∈ cells ptn level n → c + 1 < n := by
    intro c hc
    have := cells_bound (by omega) hend _ hc
    omega
  apply rows_of_bits hfb hinvol
  apply flip_bits (P := P) hsymm hfb
  · rintro u v ⟨c, hc, hSc, rfl, rfl⟩
    exact hSswap _ hc hSc
  · intro z hz
    obtain ⟨i, hi, rfl⟩ := hsurj z hz
    obtain ⟨p, hp, hpi, hip⟩ := cells_cover (ptn := ptn) (level := level) i hi
    by_cases hs : S p.1
    · have hpe := hSpair p hp hs
      have hc : (p.1, p.1 + 1) ∈ cells ptn level n := by rw [← hpe]; exact hp
      have hcbd := hbound _ hc
      refine Or.inr ⟨lab[p.1]!, lab[p.1 + 1]!, hlb _ (by omega), hlb _ hcbd,
        ⟨p.1, hc, hs, rfl, rfl⟩, ?_⟩
      have hpos : i = p.1 ∨ i = p.1 + 1 := by omega
      exact hpos.elim (fun h => Or.inl (congrArg (fun j => lab[j]!) h))
        (fun h => Or.inr (congrArg (fun j => lab[j]!) h))
    · have h := hSfix p hp hs (i - p.1) (by omega)
      simpa only [Nat.add_sub_of_le hpi] using Or.inl h
  · rintro z hz hf u v ⟨c, hc, hSc, rfl, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hsurj z hz
    obtain ⟨q, hq, hqj, hjq⟩ := cells_cover (ptn := ptn) (level := level) j hj
    have hnot : ¬ S q.1 := by
      intro hSq
      have hqe := hSpair q hq hSq
      have hqc : (q.1, q.1 + 1) ∈ cells ptn level n := by rw [← hqe]; exact hq
      have hqb := hbound _ hqc
      have hne : lab[q.1]! ≠ lab[q.1 + 1]! := by
        intro he
        have := hinj _ _ (by omega) hqb he
        omega
      have hs := hSswap _ hqc hSq
      have hpos : j = q.1 ∨ j = q.1 + 1 := by omega
      rcases hpos with hpos | hpos
      · rw [hpos, hs.1] at hf
        exact hne hf.symm
      · rw [hpos, hs.2] at hf
        exact hne hf
    have hcb := hbound _ hc
    rw [hsymm _ _ (hlb j hj) (hlb c (by omega)),
      hsymm _ _ (hlb j hj) (hlb (c + 1) hcb)]
    exact flip_bit_aux hE hps hend hinj hlb hsymm hSclosed hOdd hc hSc hq hnot hqj hjq
  · rintro u v x y ⟨c, hc, _, rfl, rfl⟩ ⟨d, hd, _, rfl, rfl⟩
    exact pair_swap_eq hE hps hend hinj hlb hsymm hc hd

end Flip

/-! # Cell membership

The descent argument classifies the child partition's cells against
the parent's. Membership in `cells` is characterized by the start
condition and the cell-end computation, so the classification reduces
to arithmetic on partition entries. -/

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

end Hex.GraphIso.Nauty
