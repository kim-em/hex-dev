/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable.Basic
public import HexGraphIso.Nauty.Invariant.Store
import all HexGraphIso.Nauty.Equitable.Basic

public section

/-!
The cheapautom small-cell theory (SPEC § Verified search refinement,
the code-1 arm of the store-validity obligation).

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

Remaining layers on top of this file, in dependency order. (1) The
descent plumbing: re-establish `refine_equitable`'s entry hypotheses
at each subtree node (the certificate seed at descent is designed in
the equitability file's docstring; the labelling and count facts come
from the landed search invariants). (2) The branch step: at a cheap
equitable node whose target cell is a pair, the two children are
related by the flip of the target pair's matching component — `S` is
the `PairMatch`-reachability closure, `hSclosed` holds by
construction, `hOdd` follows from `cheapautom_iff` and
`cells_go_sizes_sum` in the all-pairs-and-one-triple branch, and the
flip carries one child's refined labelling to the other's positionwise
by refine equivariance. (3) Individualization inside non-pair cells
and the exotic defect-four configurations (a four-cell, a five-cell,
two triples), which `hOdd` excludes: triple analogues of `PairMatch`
and the flip. (4) The composition down the subtree: the current
leaf's `leafRows` equal the first leaf's by chaining branch steps, and
the admitted scatter then passes `checkAutom` through the landed
`checkAutom_scatter_of_leafRows_eq` — no per-flip `checkAutom` wrapper
is needed, which is why this file exports rows preservation only.
(5) The `noncheaplevel` bookkeeping event lemma (the three write
sites) and the arm-2 assembly in `Invariant/Store`.
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

/-! # Counting toolkit -/

/-- The adjacency bit as a count. -/
def bitCnt (r : VSet n) (v : Nat) : Nat := if r.mem v then 1 else 0

theorem bitCnt_le_one (r : VSet n) (v : Nat) : bitCnt r v ≤ 1 := by
  rw [bitCnt]
  split <;> omega

theorem bitCnt_eq_zero {r : VSet n} {v : Nat} :
    bitCnt r v = 0 ↔ r.mem v = false := by
  rw [bitCnt]
  rcases h : r.mem v with _ | _ <;> simp

theorem bitCnt_eq_one {r : VSet n} {v : Nat} :
    bitCnt r v = 1 ↔ r.mem v = true := by
  rw [bitCnt]
  rcases h : r.mem v with _ | _ <;> simp

theorem bitCnt_inj {r r' : VSet n} {v v' : Nat} :
    bitCnt r v = bitCnt r' v' ↔ r.mem v = r'.mem v' := by
  rw [bitCnt, bitCnt]
  rcases h : r.mem v with _ | _ <;>
    rcases h' : r'.mem v' with _ | _ <;> simp

/-- The count into a window's splitter set expands into the sum of the
adjacency bits at the window's members. -/
theorem cardInter_workset {lab : Array Nat} (r : VSet n) :
    ∀ (len lo : Nat),
      (∀ o o', o ≤ len → o' ≤ len → o ≠ o' →
        lab[lo + o]! ≠ lab[lo + o']!) →
      (worksetOf n lab lo (lo + len)).cardInter r =
        ((List.range (len + 1)).map fun o => bitCnt r lab[lo + o]!).sum
  | 0, lo, _ => by
    rw [Nat.add_zero, worksetOf_singleton, VSet.cardInter_singleton]
    simp [bitCnt]
  | len + 1, lo, hdist => by
    have hsplit : worksetOf n lab lo (lo + (len + 1)) =
        (worksetOf n lab lo (lo + len)).union
          (worksetOf n lab (lo + len + 1) (lo + len + 1)) :=
      worksetOf_split (by omega) (by omega)
    have hdisj : (worksetOf n lab lo (lo + len)).inter
        (worksetOf n lab (lo + len + 1) (lo + len + 1)) = VSet.empty := by
      refine worksetOf_disjoint fun v hv1 hv2 => ?_
      rw [segN] at hv1 hv2
      obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv1
      obtain ⟨o', ho', he⟩ := List.mem_map.mp hv2
      have ho2 := List.mem_range.mp ho
      have ho2' := List.mem_range.mp ho'
      have ho'0 : o' = 0 := by omega
      subst ho'0
      have he' : lab[lo + (len + 1)]! = lab[lo + o]! := he
      exact hdist o (len + 1) (by omega) (by omega) (by omega) he'.symm
    rw [hsplit, VSet.cardInter_union_disjoint hdisj,
      cardInter_workset r len lo
        (fun o o' h1 h2 h3 => hdist o o' (by omega) (by omega) h3),
      worksetOf_singleton, VSet.cardInter_singleton]
    conv => rhs; rw [sum_range_succ]
    have hidx : lo + len + 1 = lo + (len + 1) := by omega
    rw [hidx, bitCnt]

/-! # Small cells in an equitable partition -/

/-- Adjacency-bit counts are symmetric between vertices. -/
theorem bitCnt_symm
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    {u w : Nat} (hu : u < n) (hw : w < n) :
    bitCnt ctx.g[u]! w = bitCnt ctx.g[w]! u := by
  rw [bitCnt, bitCnt, hsymm u w hu hw]

/-- The count of a vertex into a cell's splitter set is the sum of its
adjacency bits at the cell's members. -/
theorem count_into_cell {lab ptn : Array Nat} {level : Nat}
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    {d e : Nat} (hD : (d, e) ∈ cells ptn level n)
    {u : Nat} :
    (worksetOf n lab d e).cardInter ctx.g[u]! =
      ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[u]! lab[d + o]!).sum := by
  have hde : d ≤ e := cells_le _ hD
  have he : e < n := by
    have := cells_bound (by omega) hend _ hD
    omega
  have h := cardInter_workset (lab := lab) (n := n) ctx.g[u]! (e - d) d
    (fun o o' h1 h2 h3 heq2 => h3 (by
      have := hinj (d + o) (d + o') (by omega) (by omega) heq2
      omega))
  rw [show d + (e - d) = e by omega] at h
  rw [show e + 1 - d = (e - d) + 1 by omega]
  exact h

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

/-- Image membership under a bounded involution reads off the preimage. -/
theorem mem_image_invol {f : Nat → Nat} {s : VSet n}
    (hfb : ∀ v, v < n → f v < n) (hinvol : ∀ v, v < n → f (f v) = v)
    {z : Nat} (hz : z < n) :
    (s.image f).mem z = s.mem (f z) := by
  rw [VSet.mem_image]
  rcases hb : s.mem (f z) with _ | _
  · refine List.any_eq_false.mpr fun u hu hcontra => ?_
    have hun := List.mem_range.mp hu
    rw [Bool.and_eq_true, Bool.and_eq_true, beq_iff_eq] at hcontra
    obtain ⟨⟨hb1, hb2⟩, _⟩ := hcontra
    have huz : u = f z := by rw [← hb2, hinvol u hun]
    rw [huz, hb] at hb1
    exact Bool.false_ne_true hb1
  · refine List.any_eq_true.mpr ⟨f z, List.mem_range.mpr (hfb z hz), ?_⟩
    rw [hb, hinvol z hz]
    simp [hz]

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

/-- Bit invariance under a matching-closed flip: mapping both vertex
arguments through the flip preserves every adjacency bit. -/
private theorem flip_bit
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < n → j < n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < n → lab[i]! < n)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
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
    ∀ i j, i < n → j < n →
      (ctx.g[f lab[i]!]!).mem (f lab[j]!) =
        (ctx.g[lab[i]!]!).mem lab[j]! := by
  intro i j hi hj
  obtain ⟨p, hp, hpi1, hpi2⟩ := cells_cover (ptn := ptn)
    (level := level) i hi
  obtain ⟨q, hq, hqj1, hqj2⟩ := cells_cover (ptn := ptn)
    (level := level) j hj
  rcases Classical.em (S p.1) with hSp | hSp <;>
    rcases Classical.em (S q.1) with hSq | hSq
  · -- both flipped
    have hpp := hSpair _ hp hSp
    have hqp := hSpair _ hq hSq
    have hp' : (p.1, p.1 + 1) ∈ cells ptn level n := by
      rw [← hpp]; exact hp
    have hq' : (q.1, q.1 + 1) ∈ cells ptn level n := by
      rw [← hqp]; exact hq
    obtain ⟨hswp1, hswp2⟩ := hSswap _ hp' hSp
    obtain ⟨hswq1, hswq2⟩ := hSswap _ hq' hSq
    have hp1n : p.1 + 1 < n := by
      have := cells_bound (by omega) hend _ hp'
      omega
    have hq1n : q.1 + 1 < n := by
      have := cells_bound (by omega) hend _ hq'
      omega
    rcases Classical.em (p.1 = q.1) with heq | hnepq
    · -- same pair
      have hiv : i = p.1 ∨ i = p.1 + 1 := by omega
      have hjv : j = p.1 ∨ j = p.1 + 1 := by omega
      rcases hiv with rfl | hiv <;> rcases hjv with rfl | hjv
      · rw [hswp1, hloop _ (hlb _ hp1n), hloop _ (hlb _ (by omega))]
      · rw [hjv, hswp1, hswp2,
          hsymm _ _ (hlb _ hp1n) (hlb _ (by omega))]
      · rw [hiv, hswp2, hswp1,
          hsymm _ _ (hlb _ (by omega)) (hlb _ hp1n)]
      · rw [hiv, hjv, hswp2, hloop _ (hlb _ (by omega)),
          hloop _ (hlb _ hp1n)]
    · -- distinct flipped pairs
      obtain ⟨hsw1, hsw2⟩ :=
        pair_swap_eq hE hps hend hinj hlb hsymm hp' hq'
      have hiv : i = p.1 ∨ i = p.1 + 1 := by omega
      have hjv : j = q.1 ∨ j = q.1 + 1 := by omega
      rcases hiv with rfl | hiv <;> rcases hjv with rfl | hjv
      · rw [hswp1, hswq1]
        exact hsw1.symm
      · rw [hjv, hswp1, hswq2]
        exact hsw2.symm
      · rw [hiv, hswp2, hswq1]
        exact hsw2
      · rw [hiv, hjv, hswp2, hswq2]
        exact hsw1
  · -- i flipped, j not
    have hpp := hSpair _ hp hSp
    have hp' : (p.1, p.1 + 1) ∈ cells ptn level n := by
      rw [← hpp]; exact hp
    obtain ⟨hswp1, hswp2⟩ := hSswap _ hp' hSp
    have hfix := hSfix _ hq hSq (j - q.1) (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at hfix
    have haux := flip_bit_aux hE hps hend hinj hlb hsymm
      hSclosed hOdd hp' hSp hq hSq hqj1 hqj2
    have hiv : i = p.1 ∨ i = p.1 + 1 := by omega
    rcases hiv with rfl | hiv
    · rw [hswp1, hfix]
      exact haux.symm
    · rw [hiv, hswp2, hfix]
      exact haux
  · -- j flipped, i not
    have hqp := hSpair _ hq hSq
    have hq' : (q.1, q.1 + 1) ∈ cells ptn level n := by
      rw [← hqp]; exact hq
    obtain ⟨hswq1, hswq2⟩ := hSswap _ hq' hSq
    have hfix := hSfix _ hp hSp (i - p.1) (by omega)
    rw [show p.1 + (i - p.1) = i by omega] at hfix
    have haux := flip_bit_aux hE hps hend hinj hlb hsymm
      hSclosed hOdd hq' hSq hp hSp hpi1 hpi2
    have hq1n : q.1 + 1 < n := by
      have := cells_bound (by omega) hend _ hq'
      omega
    have hjv : j = q.1 ∨ j = q.1 + 1 := by omega
    rcases hjv with rfl | hjv
    · rw [hswq1, hfix,
        hsymm lab[i]! lab[q.1 + 1]! (hlb i hi) (hlb _ hq1n),
        hsymm lab[i]! lab[q.1]! (hlb i hi) (hlb _ (by omega))]
      exact haux.symm
    · rw [hjv, hswq2, hfix,
        hsymm lab[i]! lab[q.1]! (hlb i hi) (hlb _ (by omega)),
        hsymm lab[i]! lab[q.1 + 1]! (hlb i hi) (hlb _ hq1n)]
      exact haux
  · -- neither flipped
    have hfixi := hSfix _ hp hSp (i - p.1) (by omega)
    rw [show p.1 + (i - p.1) = i by omega] at hfixi
    have hfixj := hSfix _ hq hSq (j - q.1) (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at hfixj
    rw [hfixi, hfixj]

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
    (hloop : ∀ v, v < n → (ctx.g[v]!).mem v = false)
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
  intro v hv
  refine VSet.ext fun z => ?_
  rcases Decidable.em (z < n) with hz | hz
  · rw [mem_image_invol hfb hinvol hz]
    obtain ⟨i, hi, rfl⟩ := hsurj v hv
    obtain ⟨j, hj, hjz⟩ := hsurj (f z) (hfb z hz)
    rw [← hjz]
    have hkey := flip_bit hE hps hend hinj hlb hsymm hloop
      hSpair hSswap hSfix hSclosed hOdd i j hi hj
    rw [hjz, hinvol z hz] at hkey
    rw [← hjz] at hkey
    exact hkey
  · rw [VSet.mem_of_ge (by omega), VSet.mem_of_ge (by omega)]

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
