/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.Equitable
public import HexGraphIso.Nauty.StoreValid
import all HexGraphIso.Nauty.Equitable

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
sites) and the arm-2 assembly in `StoreValid.lean`.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

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
def bitCnt (r v : Nat) : Nat := if r.testBit v then 1 else 0

theorem bitCnt_le_one (r v : Nat) : bitCnt r v ≤ 1 := by
  rw [bitCnt]
  split <;> omega

theorem bitCnt_eq_zero {r v : Nat} :
    bitCnt r v = 0 ↔ r.testBit v = false := by
  rw [bitCnt]
  rcases h : r.testBit v with _ | _ <;> simp

theorem bitCnt_eq_one {r v : Nat} :
    bitCnt r v = 1 ↔ r.testBit v = true := by
  rw [bitCnt]
  rcases h : r.testBit v with _ | _ <;> simp

theorem bitCnt_inj {r r' v v' : Nat} :
    bitCnt r v = bitCnt r' v' ↔ r.testBit v = r'.testBit v' := by
  rw [bitCnt, bitCnt]
  rcases h : r.testBit v with _ | _ <;>
    rcases h' : r'.testBit v' with _ | _ <;> simp

private theorem sum_range_succ (f : Nat → Nat) (m : Nat) :
    ((List.range (m + 1)).map f).sum = ((List.range m).map f).sum + f m := by
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

private theorem sum_range_const (c : Nat) :
    ∀ m, ((List.range m).map fun _ => c).sum = m * c
  | 0 => by simp
  | m + 1 => by
    rw [sum_range_succ, sum_range_const c m, Nat.succ_mul]

private theorem sum_range_le (f : Nat → Nat) :
    ∀ m, (∀ o, o < m → f o ≤ 1) → ((List.range m).map f).sum ≤ m
  | 0, _ => by simp
  | m + 1, hf => by
    rw [sum_range_succ]
    have h1 := sum_range_le f m fun o ho => hf o (by omega)
    have h2 := hf m (by omega)
    omega

private theorem sum_range_eq_zero {f : Nat → Nat} :
    ∀ m, ((List.range m).map f).sum = 0 → ∀ o, o < m → f o = 0
  | m + 1, hs, o, ho => by
    rw [sum_range_succ] at hs
    rcases Decidable.em (o = m) with rfl | hne
    · omega
    · exact sum_range_eq_zero m (by omega) o (by omega)

private theorem sum_range_eq_len {f : Nat → Nat} :
    ∀ m, (∀ o, o < m → f o ≤ 1) → ((List.range m).map f).sum = m →
      ∀ o, o < m → f o = 1
  | m + 1, hf, hs, o, ho => by
    rw [sum_range_succ] at hs
    have h1 := sum_range_le f m fun o ho => hf o (by omega)
    have h2 := hf m (by omega)
    rcases Decidable.em (o = m) with rfl | hne
    · omega
    · exact sum_range_eq_len m (fun o ho => hf o (by omega)) (by omega)
        o (by omega)

private theorem or_and_distrib (a b r : Nat) :
    (a ||| b) &&& r = (a &&& r) ||| (b &&& r) := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  simp only [Nat.testBit_and, Nat.testBit_or]
  cases a.testBit i <;> cases b.testBit i <;> cases r.testBit i <;> rfl

private theorem and_r_disjoint {a b : Nat} (r : Nat) (h : a &&& b = 0) :
    (a &&& r) &&& (b &&& r) = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  have hab := congrArg (fun t => t.testBit i) h
  simp only [Nat.testBit_and, Nat.zero_testBit] at hab ⊢
  cases ha : a.testBit i <;> cases hb : b.testBit i <;>
    cases r.testBit i <;> simp_all

/-- A window of bounded vertices has a bounded splitter set. -/
private theorem worksetOf_lt_of_bounds {lab : Array Nat} {lo hi n : Nat}
    (hb : ∀ o, o < hi + 1 - lo → lab[lo + o]! < n) :
    worksetOf lab lo hi < 2 ^ n := by
  refine lt_two_pow_of_bits fun i hi' => ?_
  rw [testBit_worksetOf]
  refine List.any_eq_false.mpr fun v hv => ?_
  rw [segN] at hv
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp hv
  have := hb o (List.mem_range.mp ho)
  simp
  omega

/-- The count into a window's splitter set expands into the sum of the
adjacency bits at the window's members. -/
theorem popCount_workset_and {lab : Array Nat} {n r : Nat}
    (hr : r < 2 ^ n) :
    ∀ (len lo : Nat),
      (∀ o o', o ≤ len → o' ≤ len → o ≠ o' →
        lab[lo + o]! ≠ lab[lo + o']!) →
      (∀ o, o ≤ len → lab[lo + o]! < n) →
      popCount (worksetOf lab lo (lo + len) &&& r) =
        ((List.range (len + 1)).map fun o => bitCnt r lab[lo + o]!).sum
  | 0, lo, _, hb => by
    rw [Nat.add_zero, worksetOf_singleton, popCount_and_single]
    simp [bitCnt]
  | len + 1, lo, hdist, hb => by
    have hsplit : worksetOf lab lo (lo + (len + 1)) =
        worksetOf lab lo (lo + len) |||
          worksetOf lab (lo + len + 1) (lo + len + 1) :=
      worksetOf_split (by omega) (by omega)
    have hdisj : worksetOf lab lo (lo + len) &&&
        worksetOf lab (lo + len + 1) (lo + len + 1) = 0 := by
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
    have hb1 : worksetOf lab lo (lo + len) < 2 ^ n :=
      worksetOf_lt_of_bounds fun o ho => hb o (by omega)
    have hb2 : worksetOf lab (lo + len + 1) (lo + len + 1) < 2 ^ n :=
      worksetOf_lt_of_bounds fun o ho => by
        have ho0 : o = 0 := by omega
        subst ho0
        exact hb (len + 1) (by omega)
    rw [hsplit, or_and_distrib,
      popCount_or_disjoint (and_r_disjoint r hdisj)
        (Nat.lt_of_le_of_lt (Nat.and_le_left ..) hb1)
        (Nat.lt_of_le_of_lt (Nat.and_le_left ..) hb2),
      popCount_workset_and hr len lo
        (fun o o' h1 h2 h3 => hdist o o' (by omega) (by omega) h3)
        (fun o ho => hb o (by omega)),
      worksetOf_singleton, popCount_and_single]
    conv => rhs; rw [sum_range_succ]
    have hidx : lo + len + 1 = lo + (len + 1) := by omega
    rw [hidx, bitCnt]

/-! # Small cells in an equitable partition -/

private theorem sum_range_two (f : Nat → Nat) :
    ((List.range 2).map f).sum = f 0 + f 1 := by
  rw [show (2 : Nat) = 1 + 1 from rfl, sum_range_succ,
    show (1 : Nat) = 0 + 1 from rfl, sum_range_succ]
  simp

/-- Adjacency-bit counts are symmetric between vertices. -/
theorem bitCnt_symm
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    {u w : Nat} (hu : u < ctx.n) (hw : w < ctx.n) :
    bitCnt ctx.g[u]! w = bitCnt ctx.g[w]! u := by
  rw [bitCnt, bitCnt, hsymm u w hu hw]

/-- The count of a vertex into a cell's splitter set is the sum of its
adjacency bits at the cell's members. -/
theorem count_into_cell {lab ptn : Array Nat} {level : Nat}
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    {d e : Nat} (hD : (d, e) ∈ cells ptn level ctx.n)
    {u : Nat} (hru : ctx.g[u]! < 2 ^ ctx.n) :
    popCount (worksetOf lab d e &&& ctx.g[u]!) =
      ((List.range (e + 1 - d)).map fun o =>
        bitCnt ctx.g[u]! lab[d + o]!).sum := by
  have hde : d ≤ e := cells_le _ hD
  have he : e < ctx.n := by
    have := cells_bound (by omega) hend _ hD
    omega
  have h := popCount_workset_and (lab := lab) (n := ctx.n) hru (e - d) d
    (fun o o' h1 h2 h3 heq2 => h3 (by
      have := hinj (d + o) (d + o') (by omega) (by omega) heq2
      omega))
    (fun o ho => hlb (d + o) (by omega))
  rw [show d + (e - d) = e by omega] at h
  rw [show e + 1 - d = (e - d) + 1 by omega]
  exact h

/-- Swapping both pairs preserves adjacency: the bits between two pair
cells of an equitable partition satisfy the two cross equalities, in
every configuration (empty, complete, or either matching). -/
theorem pair_swap_eq {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    {c d : Nat} (hP : (c, c + 1) ∈ cells ptn level ctx.n)
    (hQ : (d, d + 1) ∈ cells ptn level ctx.n) :
    (ctx.g[lab[c]!]!).testBit lab[d]! =
      (ctx.g[lab[c + 1]!]!).testBit lab[d + 1]! ∧
    (ctx.g[lab[c]!]!).testBit lab[d + 1]! =
      (ctx.g[lab[c + 1]!]!).testBit lab[d]! := by
  have hc1 : c + 1 < ctx.n := by
    have := cells_bound (by omega) hend _ hP
    omega
  have hd1 : d + 1 < ctx.n := by
    have := cells_bound (by omega) hend _ hQ
    omega
  have h1 := hE _ hP _ hQ 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at h1
  rw [count_into_cell hps hend hinj hlb hQ (hg _ (hlb c (by omega))),
    count_into_cell hps hend hinj hlb hQ (hg _ (hlb (c + 1) hc1)),
    show d + 1 + 1 - d = 2 by omega, sum_range_two, sum_range_two] at h1
  simp only [Nat.add_zero] at h1
  have h2 := hE _ hQ _ hP 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at h2
  rw [count_into_cell hps hend hinj hlb hP (hg _ (hlb d (by omega))),
    count_into_cell hps hend hinj hlb hP (hg _ (hlb (d + 1) hd1)),
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
def PairMatch (g : Array Nat) (x y z t : Nat) : Prop :=
  ((g[x]!).testBit z = true ∧ (g[y]!).testBit t = true ∧
    (g[x]!).testBit t = false ∧ (g[y]!).testBit z = false) ∨
  ((g[x]!).testBit t = true ∧ (g[y]!).testBit z = true ∧
    (g[x]!).testBit z = false ∧ (g[y]!).testBit t = false)

/-- Between two non-matching pair cells of an equitable partition the
bits are insensitive to swapping either pair alone. -/
theorem pair_eq_of_not_match {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    {c d : Nat} (hP : (c, c + 1) ∈ cells ptn level ctx.n)
    (hQ : (d, d + 1) ∈ cells ptn level ctx.n)
    (hnm : ¬ PairMatch ctx.g lab[c]! lab[c + 1]! lab[d]! lab[d + 1]!) :
    (ctx.g[lab[c]!]!).testBit lab[d]! =
      (ctx.g[lab[c + 1]!]!).testBit lab[d]! ∧
    (ctx.g[lab[c]!]!).testBit lab[d + 1]! =
      (ctx.g[lab[c + 1]!]!).testBit lab[d + 1]! := by
  obtain ⟨h1, h2⟩ :=
    pair_swap_eq hE hps hend hinj hlb hg hsymm hP hQ
  rw [PairMatch] at hnm
  rcases hp : (ctx.g[lab[c]!]!).testBit lab[d]! with _ | _ <;>
    rcases hq : (ctx.g[lab[c]!]!).testBit lab[d + 1]! with _ | _ <;>
      rw [hp] at h1 <;> rw [hq] at h2 <;>
        rw [hp, hq] at hnm <;> simp_all

/-- The members of a pair cell have identical bits at every member of
a cell of odd size: parity forces the count between them to be empty
or complete. -/
theorem pair_odd_eq {lab ptn : Array Nat} {level : Nat}
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    {c d e : Nat} (hP : (c, c + 1) ∈ cells ptn level ctx.n)
    (hD : (d, e) ∈ cells ptn level ctx.n)
    (hodd : (e + 1 - d) % 2 = 1) :
    ∀ o, o < e + 1 - d →
      (ctx.g[lab[c]!]!).testBit lab[d + o]! =
        (ctx.g[lab[c + 1]!]!).testBit lab[d + o]! := by
  have hc1 : c + 1 < ctx.n := by
    have := cells_bound (by omega) hend _ hP
    omega
  have hde : d ≤ e := cells_le _ hD
  have he : e < ctx.n := by
    have := cells_bound (by omega) hend _ hD
    omega
  have hxy := hE _ hP _ hD 0 1 (by omega) (by omega)
  simp only [Nat.add_zero] at hxy
  rw [count_into_cell hps hend hinj hlb hD (hg _ (hlb c (by omega))),
    count_into_cell hps hend hinj hlb hD (hg _ (hlb (c + 1) hc1))]
    at hxy
  have hB : ∀ o, o < e + 1 - d →
      bitCnt ctx.g[lab[c]!]! lab[d + o]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d + o]! =
      bitCnt ctx.g[lab[c]!]! lab[d]! +
        bitCnt ctx.g[lab[c + 1]!]! lab[d]! := by
    intro o ho
    have h := hE _ hD _ hP o 0 (by omega) (by omega)
    simp only [Nat.add_zero] at h
    rw [count_into_cell hps hend hinj hlb hP
        (hg _ (hlb (d + o) (by omega))),
      count_into_cell hps hend hinj hlb hP (hg _ (hlb d (by omega))),
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

/-- Image bits under a bounded involution read off the preimage bit. -/
theorem testBit_image_invol {f : Nat → Nat} {n s : Nat}
    (hfb : ∀ v, v < n → f v < n) (hinvol : ∀ v, v < n → f (f v) = v)
    {z : Nat} (hz : z < n) :
    (image f n s).testBit z = s.testBit (f z) := by
  rw [testBit_image]
  rcases hb : s.testBit (f z) with _ | _
  · refine List.any_eq_false.mpr fun u hu hcontra => ?_
    have hun := List.mem_range.mp hu
    rw [Bool.and_eq_true, beq_iff_eq] at hcontra
    obtain ⟨hb1, hb2⟩ := hcontra
    have huz : u = f z := by
      rw [← hb2, hinvol u hun]
    rw [huz, hb] at hb1
    exact absurd hb1 (by simp)
  · refine List.any_eq_true.mpr ⟨f z, List.mem_range.mpr (hfb z hz), ?_⟩
    rw [hb, hinvol z hz]
    simp

section Flip

variable {lab ptn : Array Nat} {level : Nat} {S : Nat → Prop}
  {f : Nat → Nat}

/-- The members of a flipped pair have identical bits at every member
of an unflipped cell, given matching closure and odd unflipped
sizes. -/
private theorem flip_bit_aux
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hSclosed : ∀ p ∈ cells ptn level ctx.n,
      ∀ q ∈ cells ptn level ctx.n, S p.1 → q.2 = q.1 + 1 →
        PairMatch ctx.g lab[p.1]! lab[p.1 + 1]! lab[q.1]! lab[q.1 + 1]! →
        S q.1)
    (hOdd : ∀ q ∈ cells ptn level ctx.n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1)
    {c : Nat} (hP : (c, c + 1) ∈ cells ptn level ctx.n) (hSc : S c)
    {q : Nat × Nat} (hq : q ∈ cells ptn level ctx.n) (hnq : ¬ S q.1)
    {j : Nat} (hj1 : q.1 ≤ j) (hj2 : j ≤ q.2) :
    (ctx.g[lab[c]!]!).testBit lab[j]! =
      (ctx.g[lab[c + 1]!]!).testBit lab[j]! := by
  rcases Classical.em (q.2 = q.1 + 1) with hqp | hqnp
  · have hq' : (q.1, q.1 + 1) ∈ cells ptn level ctx.n := by
      rw [← hqp]
      exact hq
    have hnm : ¬ PairMatch ctx.g lab[c]! lab[c + 1]!
        lab[q.1]! lab[q.1 + 1]! :=
      fun hm => hnq (hSclosed _ hP _ hq hSc hqp hm)
    obtain ⟨h1, h2⟩ :=
      pair_eq_of_not_match hE hps hend hinj hlb hg hsymm hP hq' hnm
    rcases Decidable.em (j = q.1) with rfl | hne
    · exact h1
    · have : j = q.1 + 1 := by omega
      rw [this]
      exact h2
  · have hodd := hOdd _ hq hqnp
    have h := pair_odd_eq hE hps hend hinj hlb hg hsymm hP hq hodd
      (j - q.1) (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at h
    exact h

/-- Bit invariance under a matching-closed flip: mapping both vertex
arguments through the flip preserves every adjacency bit. -/
private theorem flip_bit
    (hE : Equitable ctx level lab ptn)
    (hps : ptn.size = ctx.n) (hend : ptn[ptn.size - 1]! ≤ level)
    (hinj : ∀ i j, i < ctx.n → j < ctx.n → lab[i]! = lab[j]! → i = j)
    (hlb : ∀ i, i < ctx.n → lab[i]! < ctx.n)
    (hg : ∀ v, v < ctx.n → ctx.g[v]! < 2 ^ ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hloop : ∀ v, v < ctx.n → (ctx.g[v]!).testBit v = false)
    (hSpair : ∀ p ∈ cells ptn level ctx.n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells ptn level ctx.n, S p.1 →
      f lab[p.1]! = lab[p.1 + 1]! ∧ f lab[p.1 + 1]! = lab[p.1]!)
    (hSfix : ∀ p ∈ cells ptn level ctx.n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 → f lab[p.1 + o]! = lab[p.1 + o]!)
    (hSclosed : ∀ p ∈ cells ptn level ctx.n,
      ∀ q ∈ cells ptn level ctx.n, S p.1 → q.2 = q.1 + 1 →
        PairMatch ctx.g lab[p.1]! lab[p.1 + 1]! lab[q.1]! lab[q.1 + 1]! →
        S q.1)
    (hOdd : ∀ q ∈ cells ptn level ctx.n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1) :
    ∀ i j, i < ctx.n → j < ctx.n →
      (ctx.g[f lab[i]!]!).testBit (f lab[j]!) =
        (ctx.g[lab[i]!]!).testBit lab[j]! := by
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
    have hp' : (p.1, p.1 + 1) ∈ cells ptn level ctx.n := by
      rw [← hpp]; exact hp
    have hq' : (q.1, q.1 + 1) ∈ cells ptn level ctx.n := by
      rw [← hqp]; exact hq
    obtain ⟨hswp1, hswp2⟩ := hSswap _ hp' hSp
    obtain ⟨hswq1, hswq2⟩ := hSswap _ hq' hSq
    have hp1n : p.1 + 1 < ctx.n := by
      have := cells_bound (by omega) hend _ hp'
      omega
    have hq1n : q.1 + 1 < ctx.n := by
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
        pair_swap_eq hE hps hend hinj hlb hg hsymm hp' hq'
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
    have hp' : (p.1, p.1 + 1) ∈ cells ptn level ctx.n := by
      rw [← hpp]; exact hp
    obtain ⟨hswp1, hswp2⟩ := hSswap _ hp' hSp
    have hfix := hSfix _ hq hSq (j - q.1) (by omega)
    rw [show q.1 + (j - q.1) = j by omega] at hfix
    have haux := flip_bit_aux hE hps hend hinj hlb hg hsymm
      hSclosed hOdd hp' hSp hq hSq hqj1 hqj2
    have hiv : i = p.1 ∨ i = p.1 + 1 := by omega
    rcases hiv with rfl | hiv
    · rw [hswp1, hfix]
      exact haux.symm
    · rw [hiv, hswp2, hfix]
      exact haux
  · -- j flipped, i not
    have hqp := hSpair _ hq hSq
    have hq' : (q.1, q.1 + 1) ∈ cells ptn level ctx.n := by
      rw [← hqp]; exact hq
    obtain ⟨hswq1, hswq2⟩ := hSswap _ hq' hSq
    have hfix := hSfix _ hp hSp (i - p.1) (by omega)
    rw [show p.1 + (i - p.1) = i by omega] at hfix
    have haux := flip_bit_aux hE hps hend hinj hlb hg hsymm
      hSclosed hOdd hq' hSq hp hSp hpi1 hpi2
    have hq1n : q.1 + 1 < ctx.n := by
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
    (hSpair : ∀ p ∈ cells ptn level ctx.n, S p.1 → p.2 = p.1 + 1)
    (hSswap : ∀ p ∈ cells ptn level ctx.n, S p.1 →
      f lab[p.1]! = lab[p.1 + 1]! ∧ f lab[p.1 + 1]! = lab[p.1]!)
    (hSfix : ∀ p ∈ cells ptn level ctx.n, ¬ S p.1 →
      ∀ o, o < p.2 + 1 - p.1 → f lab[p.1 + o]! = lab[p.1 + o]!)
    (hSclosed : ∀ p ∈ cells ptn level ctx.n,
      ∀ q ∈ cells ptn level ctx.n, S p.1 → q.2 = q.1 + 1 →
        PairMatch ctx.g lab[p.1]! lab[p.1 + 1]! lab[q.1]! lab[q.1 + 1]! →
        S q.1)
    (hOdd : ∀ q ∈ cells ptn level ctx.n, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1) :
    ∀ v, v < ctx.n → ctx.g[f v]! = image f ctx.n ctx.g[v]! := by
  intro v hv
  refine Nat.eq_of_testBit_eq fun z => ?_
  rcases Decidable.em (z < ctx.n) with hz | hz
  · rw [testBit_image_invol hfb hinvol hz]
    obtain ⟨i, hi, rfl⟩ := hsurj v hv
    obtain ⟨j, hj, hjz⟩ := hsurj (f z) (hfb z hz)
    rw [← hjz]
    have hkey := flip_bit hE hps hend hinj hlb hg hsymm hloop
      hSpair hSswap hSfix hSclosed hOdd i j hi hj
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

/-! # The descent seed

Individualizing a vertex of an equitable partition and refining with
the singleton active produces an equitable partition again: the
certificate invariant's entry seed is the parent's equitability, with
the split-off singleton as the one active certificate cell. These are
the entry facts `refine_equitable` consumes at every node of a search
subtree. -/

section Descent

/-- The positional effect of individualization's rotation: the target
vertex moves to the front of its cell and the displaced prefix shifts
one place right. -/
theorem breakout_go_shift {tv : Nat} :
    ∀ (fuel : Nat) (lab : Array Nat) (i prev k : Nat),
      (∀ m, m < k → lab[i + m]! ≠ tv) → lab[i + k]! = tv →
      k < fuel → i + k < lab.size →
      ∀ q, (breakout.go tv fuel lab i prev)[q]! =
        if q < i then lab[q]!
        else if q = i then prev
        else if q ≤ i + k then lab[q - 1]!
        else lab[q]!
  | fuel + 1, lab, i, prev, k, hfirst, hk, hkf, hks, q => by
    rw [breakout.go]
    rcases Decidable.em (k = 0) with rfl | hkpos
    · rw [Nat.add_zero] at hk hks
      rw [ite_eq_left (by simp [hk])]
      rcases Decidable.em (q < i) with h1 | h1
      · rw [ite_eq_left h1, Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rcases Decidable.em (q = i) with rfl | h2
        · rw [ite_eq_right (by omega), ite_eq_left rfl,
            Array.getElem!_set!_self _ _ _ hks]
        · rw [ite_eq_right h1, ite_eq_right h2,
            ite_eq_right (by omega),
            Array.getElem!_set!_ne _ _ _ _ (by omega)]
    · have h0 : lab[i]! ≠ tv := by
        have := hfirst 0 (by omega)
        rwa [Nat.add_zero] at this
      rw [ite_eq_right (by simp [h0])]
      have hres := breakout_go_shift fuel (lab.set! i prev) (i + 1)
        lab[i]! (k - 1)
        (fun m hm => by
          rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
            show i + 1 + m = i + (m + 1) by omega]
          exact hfirst (m + 1) (by omega))
        (by
          rw [Array.getElem!_set!_ne _ _ _ _ (by omega),
            show i + 1 + (k - 1) = i + k by omega]
          exact hk)
        (by omega)
        (by rw [Array.size_set!]; omega) q
      rw [hres]
      rcases Decidable.em (q < i) with h1 | h1
      · rw [ite_eq_left (by omega), ite_eq_left h1,
          Array.getElem!_set!_ne _ _ _ _ (by omega)]
      · rcases Decidable.em (q = i) with rfl | h2
        · rw [ite_eq_left (by omega), ite_eq_right (by omega),
            ite_eq_left rfl, Array.getElem!_set!_self _ _ _ (by omega)]
        · rcases Decidable.em (q = i + 1) with rfl | h3
          · rw [ite_eq_right (by omega), ite_eq_left rfl,
              ite_eq_right (by omega), ite_eq_right (by omega),
              ite_eq_left (by omega : i + 1 ≤ i + k),
              show i + 1 - 1 = i by omega]
          · rw [ite_eq_right (by omega), ite_eq_right h3,
              ite_eq_right h1, ite_eq_right h2]
            rcases Decidable.em (q ≤ i + k) with h4 | h4
            · rw [ite_eq_left (by omega), ite_eq_left h4,
                Array.getElem!_set!_ne _ _ _ _ (by omega)]
            · rw [ite_eq_right (by omega), ite_eq_right h4,
                Array.getElem!_set!_ne _ _ _ _ (by omega)]

/-- Membership in a bit singleton. -/
theorem elem_single {tc v : Nat} :
    elem (insert 0 tc) v = decide (v = tc) := by
  rw [insert, elem, Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
  rcases Decidable.em (v = tc) with rfl | hne
  · rw [Nat.testBit_two_pow_self]
    simp
  · rw [Nat.testBit_two_pow_of_ne (fun h => hne h.symm)]
    simp
    omega

variable {lab ptn : Array Nat} {level tc e k : Nat}

/-- Cell-end computations agree between two partitions that agree in
openness along the walked run. -/
theorem cellEnd_congr_within {ptn' : Array Nat} {level' : Nat}
    (hsz : ptn'.size = ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) :
    ∀ (fuel j : Nat), ptn.size ≤ fuel + j → j < ptn.size →
      (∀ q, j ≤ q → q ≤ cellEnd ptn level j →
        ((ptn'[q]! > level') ↔ (ptn[q]! > level))) →
      cellEnd ptn' level' j = cellEnd ptn level j
  | 0, j, hf, hj, _ => by omega
  | fuel + 1, j, hf, hj, hagree => by
    rcases Decidable.em (ptn[j]! > level) with ho | hc
    · have ho' : ptn'[j]! > level' :=
        (hagree j (Nat.le_refl _) cellEnd_ge).mpr ho
      have hlt : cellEnd ptn level j < ptn.size := cellEnd_lt hj hend
      have hstep : cellEnd ptn level j = cellEnd ptn level (j + 1) :=
        cellEnd_succ_of_open hj ho
      have hj1 : j + 1 < ptn.size := by
        have := cellEnd_ge (ptn := ptn) (level := level) (i := j + 1)
        omega
      rw [cellEnd_succ_of_open (by omega) ho',
        cellEnd_succ_of_open hj ho]
      exact cellEnd_congr_within hsz hend fuel (j + 1) (by omega) hj1
        (fun q hq1 hq2 => hagree q (by omega) (by rw [hstep]; omega))
    · have hc' : ¬ ptn'[j]! > level' := fun h =>
        hc ((hagree j (Nat.le_refl _) cellEnd_ge).mp h)
      rw [cellEnd_of_closed (by omega) hc', cellEnd_of_closed hj hc]

/-- The end of a cell walk is closed. -/
theorem cellEnd_closed (hend : ptn[ptn.size - 1]! ≤ level)
    {i : Nat} (hi : i < ptn.size) :
    ptn[cellEnd ptn level i]! ≤ level := by
  rw [cellEnd]
  exact cellEnd_go_end hend _ _ hi (by omega)

/-- A start left of another start closes its cell before it. -/
theorem cellEnd_lt_start
    {c : Nat} (hc : c < tc) (htcs : ptn[tc - 1]! ≤ level) :
    cellEnd ptn level c < tc := by
  rcases Decidable.em (cellEnd ptn level c < tc) with h | h
  · exact h
  · exfalso
    rcases Decidable.em (tc - 1 < cellEnd ptn level c) with h2 | h2
    · have := cellEnd_interior (i := c) (j := tc - 1) (by omega) h2
      omega
    · have : cellEnd ptn level c = tc - 1 := by omega
      omega

section Split

variable (hpsz : ptn.size = ctx.n) (hn : 0 < ctx.n)
  (hend : ptn[ptn.size - 1]! ≤ level)
  (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
  (hcell : (tc, e) ∈ cells ptn level ctx.n) (hne : tc < e)

include hpsz hend hcell

/-- The target cell's interior is open. -/
theorem target_open : ∀ q, tc ≤ q → q < e → ptn[q]! > level := by
  intro q hq1 hq2
  obtain ⟨-, -, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  exact cellEnd_interior hq1 (by omega)

/-- The target cell's end is closed. -/
theorem target_end_closed : ptn[e]! ≤ level := by
  obtain ⟨h1, -, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  rw [he]
  exact cellEnd_closed hend (by omega)

/-- The target cell's end is in range. -/
theorem target_end_lt : e < ctx.n := by
  obtain ⟨h1, -, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  rw [he, ← hpsz]
  exact cellEnd_lt (by omega) hend

/-- The split-off singleton is a cell of the child partition. -/
theorem child_cells_singleton :
    (tc, tc) ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n := by
  obtain ⟨h1, h2, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  have hsz : (ptn.set! tc (level + 1)).size = ptn.size := Array.size_set! _ _ _
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  rw [mem_cells_iff (by omega) hend']
  refine ⟨h1, ?_, ?_⟩
  · rcases Decidable.em (tc = 0) with rfl | h0
    · exact Or.inl rfl
    · rcases h2 with h00 | hcl
      · exact Or.inl h00
      · refine Or.inr ?_
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
  · rw [cellEnd_of_closed (by rw [hsz]; omega) (by
      rw [Array.getElem!_set!_self _ _ _ (by rw [hpsz]; omega)]
      omega)]

include hvals hne

/-- The remainder is a cell of the child partition. -/
theorem child_cells_rest :
    (tc + 1, e) ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n := by
  obtain ⟨h1, h2, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  have hen := target_end_lt hpsz hend hcell
  have hsz : (ptn.set! tc (level + 1)).size = ptn.size := Array.size_set! _ _ _
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  rw [mem_cells_iff (by omega) hend']
  refine ⟨by omega, Or.inr ?_, ?_⟩
  · rw [show tc + 1 - 1 = tc by omega,
      Array.getElem!_set!_self _ _ _ (by rw [hpsz]; omega)]
    omega
  · have hopen : ptn[tc]! > level := target_open hpsz hend hcell tc
      (Nat.le_refl _) hne
    have he1 : cellEnd ptn level (tc + 1) = e := by
      rw [he]
      exact (cellEnd_succ_of_open (by omega) hopen).symm
    rw [← he1]
    refine (cellEnd_congr_within hsz hend ptn.size (tc + 1) (by omega)
      (by omega) ?_).symm
    intro q hq1 hq2
    rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
    rw [he1] at hq2
    rcases hvals q (by omega) with hlo | hhi
    · constructor <;> omega
    · constructor <;> omega

/-- A parent cell away from the target survives into the child
partition. -/
theorem child_cells_old {c ce : Nat}
    (hmem : (c, ce) ∈ cells ptn level ctx.n) (hcne : c ≠ tc) :
    (c, ce) ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n := by
  obtain ⟨h1, h2, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  obtain ⟨hc1, hc2, hce⟩ := (mem_cells_iff (by omega) hend).mp hmem
  have hen := target_end_lt hpsz hend hcell
  have hsz : (ptn.set! tc (level + 1)).size = ptn.size := Array.size_set! _ _ _
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  have hgt : c > tc → c > e := by
    intro hgt
    rcases Decidable.em (c ≤ e) with hle | hgt2
    · exfalso
      have hop := target_open hpsz hend hcell (c - 1) (by omega)
        (by omega)
      rcases hc2 with h0 | hcl
      · omega
      · omega
    · omega
  rw [mem_cells_iff (by omega) hend']
  refine ⟨hc1, ?_, ?_⟩
  · rcases hc2 with h0 | hcl
    · exact Or.inl h0
    · refine Or.inr ?_
      rcases Decidable.em (c < tc) with hlt | hge
      · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
      · have := hgt (by omega)
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
  · rcases Decidable.em (c < tc) with hlt | hge
    · have htcs : ptn[tc - 1]! ≤ level := by
        rcases h2 with h0 | hcl
        · omega
        · exact hcl
      have hlt2 : cellEnd ptn level c < tc :=
        cellEnd_lt_start hlt htcs
      rw [hce]
      refine (cellEnd_congr_within hsz hend ptn.size c (by omega)
        (by omega) ?_).symm
      intro q hq1 hq2
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      rcases hvals q (by omega) with hlo | hhi
      · constructor <;> omega
      · constructor <;> omega
    · have hgtc := hgt (by omega)
      have hlt3 : cellEnd ptn level c < ptn.size :=
        cellEnd_lt (by omega) hend
      rw [hce]
      refine (cellEnd_congr_within hsz hend ptn.size c (by omega)
        (by omega) ?_).symm
      intro q hq1 hq2
      rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
      rcases hvals q (by omega) with hlo | hhi
      · constructor <;> omega
      · constructor <;> omega

/-- Every cell of the child partition is the singleton, the remainder,
or a parent cell away from the target. -/
theorem child_cells_cases {p : Nat × Nat}
    (hp : p ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n) :
    p = (tc, tc) ∨ p = (tc + 1, e) ∨
      (p ∈ cells ptn level ctx.n ∧ p.1 ≠ tc) := by
  obtain ⟨h1, h2, he⟩ := (mem_cells_iff (by omega) hend).mp hcell
  have hen := target_end_lt hpsz hend hcell
  have hsz : (ptn.set! tc (level + 1)).size = ptn.size := Array.size_set! _ _ _
  have hend' : (ptn.set! tc (level + 1))[(ptn.set! tc
      (level + 1)).size - 1]! ≤ level + 1 := by
    rw [hsz]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  obtain ⟨hp1, hp2, hpe⟩ := (mem_cells_iff (by omega) hend').mp hp
  rcases Decidable.em (p.1 = tc) with heq | hne1
  · refine Or.inl ?_
    have hpe2 : p.2 = tc := by
      rw [hpe, heq]
      exact cellEnd_of_closed (by rw [hsz, hpsz]; omega) (by
        rw [Array.getElem!_set!_self _ _ _ (by rw [hpsz]; omega)]
        omega)
    obtain ⟨a, b⟩ := p
    simp_all
  · rcases Decidable.em (p.1 = tc + 1) with heq1 | hne2
    · refine Or.inr (Or.inl ?_)
      have hmem := child_cells_rest hpsz hend hvals hcell hne
      obtain ⟨-, -, he2⟩ := (mem_cells_iff (by omega) hend').mp hmem
      have hpe2 : p.2 = e := by
        rw [hpe, heq1, ← he2]
      obtain ⟨a, b⟩ := p
      simp_all
    · refine Or.inr (Or.inr ⟨?_, hne1⟩)
      have hstart : p.1 = 0 ∨ ptn[p.1 - 1]! ≤ level := by
        rcases hp2 with h0 | hcl
        · exact Or.inl h0
        · refine Or.inr ?_
          rcases Decidable.em (p.1 - 1 = tc) with heq2 | hne3
          · omega
          · rw [Array.getElem!_set!_ne _ _ _ _
              (fun h => hne3 h.symm)] at hcl
            rcases hvals (p.1 - 1) (by omega) with hlo | hhi
            · exact hlo
            · omega
      rw [mem_cells_iff (by omega) hend]
      refine ⟨hp1, hstart, ?_⟩
      have hgt : tc < p.1 → e < p.1 := by
        intro hgt
        rcases Decidable.em (p.1 ≤ e) with hle | hgt2
        · exfalso
          have hop := target_open hpsz hend hcell (p.1 - 1) (by omega)
            (by omega)
          rcases hstart with h0 | hcl
          · omega
          · omega
        · omega
      rcases Decidable.em (p.1 < tc) with hlt | hge
      · have htcs : ptn[tc - 1]! ≤ level := by
          rcases h2 with h0 | hcl
          · omega
          · exact hcl
        have hlt2 : cellEnd ptn level p.1 < tc :=
          cellEnd_lt_start hlt htcs
        rw [hpe]
        exact cellEnd_congr_within hsz hend ptn.size p.1 (by omega)
          (by omega) (by
            intro q hq1 hq2
            rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
            rcases hvals q (by omega) with hlo | hhi
            · constructor <;> omega
            · constructor <;> omega)
      · have hgtc := hgt (by omega)
        have hlt3 : cellEnd ptn level p.1 < ptn.size :=
          cellEnd_lt (by omega) hend
        rw [hpe]
        exact cellEnd_congr_within hsz hend ptn.size p.1 (by omega)
          (by omega) (by
            intro q hq1 hq2
            rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
            rcases hvals q (by omega) with hlo | hhi
            · constructor <;> omega
            · constructor <;> omega)

end Split

section Labelling

variable {lab ptn : Array Nat} {level tc e o : Nat}

/-- The rotated labelling positionally, at an injectively unique
target vertex. -/
theorem breakout_lab_at
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size) :
    ∀ q, (breakout lab ptn (level + 1) tc lab[tc + o]!).1[q]! =
      if q < tc then lab[q]!
      else if q = tc then lab[tc + o]!
      else if q ≤ tc + o then lab[q - 1]!
      else lab[q]! := by
  intro q
  show (breakout.go lab[tc + o]! (lab.size + 1) lab tc
    lab[tc + o]!)[q]! = _
  exact breakout_go_shift (lab.size + 1) lab tc lab[tc + o]! o
    (fun m hm heq => by
      have := hinj (tc + m) (tc + o) (by omega) (by omega) heq
      omega)
    rfl (by omega) hto q

/-- The rotated labelling stays injective. -/
theorem labInj_breakout
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size) :
    LabInj (breakout lab ptn (level + 1) tc lab[tc + o]!).1 lab.size := by
  intro i j hi hj hv
  rw [breakout_lab_at hinj hto i, breakout_lab_at hinj hto j] at hv
  rcases Decidable.em (i < tc) with hi1 | hi1 <;>
    rcases Decidable.em (j < tc) with hj1 | hj1
  · rw [ite_eq_left hi1, ite_eq_left hj1] at hv
    exact hinj i j hi hj hv
  · rw [ite_eq_left hi1] at hv
    rcases Decidable.em (j = tc) with heqj | hj2
    · rw [ite_eq_right hj1, ite_eq_left heqj] at hv
      have := hinj i (tc + o) hi (by omega) hv
      omega
    · rcases Decidable.em (j ≤ tc + o) with hj3 | hj3
      · rw [ite_eq_right hj1, ite_eq_right hj2, ite_eq_left hj3] at hv
        have := hinj i (j - 1) hi (by omega) hv
        omega
      · rw [ite_eq_right hj1, ite_eq_right hj2, ite_eq_right hj3] at hv
        have := hinj i j hi hj hv
        omega
  · rw [ite_eq_left hj1] at hv
    rcases Decidable.em (i = tc) with heqi | hi2
    · rw [ite_eq_right hi1, ite_eq_left heqi] at hv
      have := hinj (tc + o) j (by omega) hj hv
      omega
    · rcases Decidable.em (i ≤ tc + o) with hi3 | hi3
      · rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_left hi3] at hv
        have := hinj (i - 1) j (by omega) hj hv
        omega
      · rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_right hi3] at hv
        have := hinj i j hi hj hv
        omega
  · rcases Decidable.em (i = tc) with heqi | hi2 <;>
      rcases Decidable.em (j = tc) with heqj | hj2
    · omega
    · rw [ite_eq_right hi1, ite_eq_left heqi, ite_eq_right hj1,
        ite_eq_right hj2] at hv
      rcases Decidable.em (j ≤ tc + o) with hj3 | hj3
      · rw [ite_eq_left hj3] at hv
        have := hinj (tc + o) (j - 1) (by omega) (by omega) hv
        omega
      · rw [ite_eq_right hj3] at hv
        have := hinj (tc + o) j (by omega) hj hv
        omega
    · rw [ite_eq_right hj1, ite_eq_left heqj, ite_eq_right hi1,
        ite_eq_right hi2] at hv
      rcases Decidable.em (i ≤ tc + o) with hi3 | hi3
      · rw [ite_eq_left hi3] at hv
        have := hinj (i - 1) (tc + o) (by omega) (by omega) hv
        omega
      · rw [ite_eq_right hi3] at hv
        have := hinj i (tc + o) hi (by omega) hv
        omega
    · rw [ite_eq_right hi1, ite_eq_right hi2, ite_eq_right hj1,
        ite_eq_right hj2] at hv
      rcases Decidable.em (i ≤ tc + o) with hi3 | hi3 <;>
        rcases Decidable.em (j ≤ tc + o) with hj3 | hj3
      · rw [ite_eq_left hi3, ite_eq_left hj3] at hv
        have := hinj (i - 1) (j - 1) (by omega) (by omega) hv
        omega
      · rw [ite_eq_left hi3, ite_eq_right hj3] at hv
        have := hinj (i - 1) j (by omega) hj hv
        omega
      · rw [ite_eq_right hi3, ite_eq_left hj3] at hv
        have := hinj i (j - 1) hi (by omega) hv
        omega
      · rw [ite_eq_right hi3, ite_eq_right hj3] at hv
        exact hinj i j hi hj hv

/-- Any-membership transfers along a membership equivalence. -/
private theorem any_beq_congr {l1 l2 : List Nat}
    (h : ∀ v, v ∈ l1 ↔ v ∈ l2) (v : Nat) :
    l1.any (· == v) = l2.any (· == v) := by
  rcases hb : l2.any (· == v) with _ | _
  · refine List.any_eq_false.mpr fun x hx hxv => ?_
    exact List.any_eq_false.mp hb x ((h x).mp hx) hxv
  · obtain ⟨x, hx, hxv⟩ := List.any_eq_true.mp hb
    exact List.any_eq_true.mpr ⟨x, (h x).mpr hx, hxv⟩

/-- The rotated target window has the same members. -/
private theorem mem_segN_breakout_target {lab ptn : Array Nat}
    {level tc e o : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size)
    (hoe : o ≤ e - tc) (hte : tc ≤ e) :
    ∀ v, v ∈ segN (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1 tc (e + 1 - tc) ↔
      v ∈ segN lab tc (e + 1 - tc) := by
  intro v
  constructor
  · intro hv
    obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv
    rw [breakout_lab_at hinj hto (tc + w)] at hwv
    refine mem_segN_iff.mpr ?_
    rcases Decidable.em (w = 0) with rfl | hw0
    · rw [ite_eq_right (by omega), ite_eq_left (by omega)] at hwv
      exact ⟨o, by omega, hwv⟩
    · rcases Decidable.em (w ≤ o) with hwo | hwo
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left (by omega)] at hwv
        exact ⟨w - 1, by omega, by
          rw [show tc + (w - 1) = tc + w - 1 by omega]
          exact hwv⟩
      · rw [ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)] at hwv
        exact ⟨w, by omega, hwv⟩
  · intro hv
    obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv
    refine mem_segN_iff.mpr ?_
    rcases Decidable.em (w = o) with heqw | hwo
    · refine ⟨0, by omega, ?_⟩
      rw [breakout_lab_at hinj hto (tc + 0),
        ite_eq_right (by omega), ite_eq_left (by omega), ← heqw]
      exact hwv
    · rcases Decidable.em (w < o) with hlt | hgt
      · refine ⟨w + 1, by omega, ?_⟩
        rw [breakout_lab_at hinj hto (tc + (w + 1)),
          ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left (by omega),
          show tc + (w + 1) - 1 = tc + w by omega]
        exact hwv
      · refine ⟨w, by omega, ?_⟩
        rw [breakout_lab_at hinj hto (tc + w),
          ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega)]
        exact hwv

/-- The full target window's vertex set survives the rotation. -/
theorem worksetOf_breakout_full {lab ptn : Array Nat}
    {level tc e o : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size)
    (hoe : o ≤ e - tc) (hte : tc ≤ e) :
    worksetOf (breakout lab ptn (level + 1) tc lab[tc + o]!).1 tc e =
      worksetOf lab tc e := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  rw [testBit_worksetOf, testBit_worksetOf]
  exact any_beq_congr (mem_segN_breakout_target hinj hto hoe hte) v

/-- Vertex sets of windows away from the rotation are untouched. -/
theorem worksetOf_breakout_outside {a b : Nat}
    (hinj : LabInj lab lab.size) (hto : tc + o < lab.size)
    (hout : b < tc ∨ tc + o < a) :
    worksetOf (breakout lab ptn (level + 1) tc lab[tc + o]!).1 a b =
      worksetOf lab a b := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  rw [testBit_worksetOf, testBit_worksetOf]
  have hpt : ∀ w, w < b + 1 - a →
      (breakout lab ptn (level + 1) tc lab[tc + o]!).1[a + w]! =
        lab[a + w]! := by
    intro w hw
    rw [breakout_lab_at hinj hto (a + w)]
    rcases hout with h | h
    · rw [ite_eq_left (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right (by omega)]
  rcases hb : (segN lab a (b + 1 - a)).any (· == v) with _ | _
  · refine List.any_eq_false.mpr fun x hx hxv => ?_
    obtain ⟨w, hw, hwx⟩ := mem_segN_iff.mp hx
    rw [hpt w hw] at hwx
    exact List.any_eq_false.mp hb x
      (mem_segN_iff.mpr ⟨w, hw, hwx⟩) hxv
  · obtain ⟨x, hx, hxv⟩ := List.any_eq_true.mp hb
    obtain ⟨w, hw, hwx⟩ := mem_segN_iff.mp hx
    refine List.any_eq_true.mpr ⟨x, mem_segN_iff.mpr ⟨w, hw, ?_⟩, hxv⟩
    rw [hpt w hw, hwx]

end Labelling

section Seed

private theorem or_self_right (a w : Nat) : a ||| w ||| w = a ||| w := by
  rw [Nat.or_assoc, Nat.or_self]

private theorem foldl_union_none {act : Nat} {lab : Array Nat} :
    ∀ (l : List (Nat × Nat)) (A : Nat),
      (∀ p ∈ l, elem act p.1 = false) →
      l.foldl (fun A p => if elem act p.1 then
        A ||| worksetOf lab p.1 p.2 else A) A = A
  | [], A, _ => rfl
  | q :: l, A, h => by
    rw [List.foldl_cons, ite_eq_right (by
      rw [h q List.mem_cons_self]
      simp)]
    exact foldl_union_none l A fun p hp => h p (List.mem_cons_of_mem _ hp)

private theorem foldl_union_from {act W : Nat} {lab : Array Nat} :
    ∀ (l : List (Nat × Nat)) (A : Nat),
      (∀ p ∈ l, elem act p.1 = true → worksetOf lab p.1 p.2 = W) →
      l.foldl (fun A p => if elem act p.1 then
        A ||| worksetOf lab p.1 p.2 else A) (A ||| W) = A ||| W
  | [], A, _ => rfl
  | q :: l, A, h => by
    rw [List.foldl_cons]
    rcases hq : elem act q.1 with _ | _
    · rw [ite_eq_right (by simp [hq])]
      exact foldl_union_from l A
        fun p hp => h p (List.mem_cons_of_mem _ hp)
    · rw [ite_eq_left (by simp [hq]), h q List.mem_cons_self hq,
        or_self_right]
      exact foldl_union_from l A
        fun p hp => h p (List.mem_cons_of_mem _ hp)

private theorem foldl_union_single {act W : Nat} {lab : Array Nat} :
    ∀ (l : List (Nat × Nat)) (A : Nat),
      (∀ p ∈ l, elem act p.1 = true → worksetOf lab p.1 p.2 = W) →
      (∃ p ∈ l, elem act p.1 = true) →
      l.foldl (fun A p => if elem act p.1 then
        A ||| worksetOf lab p.1 p.2 else A) A = A ||| W
  | [], _, _, ⟨p, hp, _⟩ => absurd hp (by simp)
  | q :: l, A, h, ⟨p, hp, hpa⟩ => by
    rw [List.foldl_cons]
    rcases hq : elem act q.1 with _ | _
    · rw [ite_eq_right (by simp [hq])]
      have hpl : p ∈ l := by
        rcases List.mem_cons.mp hp with rfl | hmem
        · rw [hq] at hpa
          cases hpa
        · exact hmem
      exact foldl_union_single l A
        (fun p hp2 => h p (List.mem_cons_of_mem _ hp2)) ⟨p, hpl, hpa⟩
    · rw [ite_eq_left (by simp [hq]), h q List.mem_cons_self hq]
      exact foldl_union_from l A
        fun p hp2 => h p (List.mem_cons_of_mem _ hp2)

variable {lab ptn : Array Nat} {level tc e o numcells : Nat}

variable (hlsz : lab.size = ctx.n) (hpsz : ptn.size = ctx.n)
  (hend : ptn[ptn.size - 1]! ≤ level)
  (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
  (hinj : LabInj lab ctx.n)
  (hcell : (tc, e) ∈ cells ptn level ctx.n) (hne : tc < e)
  (ho : o ≤ e - tc)

include hlsz hpsz hend hvals hinj hcell hne ho

/-- The active union of the child entry state is the split-off
singleton's vertex. -/
theorem activeUnion_breakout :
    activeUnion ctx (level + 1)
      { lab := (breakout lab ptn (level + 1) tc lab[tc + o]!).1,
        ptn := ptn.set! tc (level + 1), active := insert 0 tc,
        numcells := numcells + 1, hint := 0, maxpos := 0,
        longcode := numcells + 1 } =
      worksetOf (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        tc tc := by
  have hen := target_end_lt hpsz hend hcell
  unfold activeUnion
  refine foldl_union_single _ 0 ?_ ?_ |>.trans (Nat.zero_or _)
  · intro p hp hpa
    rw [elem_single] at hpa
    have hptc : p.1 = tc := by
      have := of_decide_eq_true hpa
      exact this
    rcases child_cells_cases hpsz hend hvals hcell hne hp with
      rfl | rfl | ⟨-, hne2⟩
    · rfl
    · exact absurd hptc (by omega)
    · exact absurd hptc hne2
  · exact ⟨(tc, tc),
      child_cells_singleton hpsz hend hcell, by
        rw [elem_single]
        simp⟩

/-- The singleton's vertex saturates every child cell: it is the whole
splitter set of the singleton and misses every other cell. -/
theorem saturated_breakout :
    Saturated ctx (level + 1)
      { lab := (breakout lab ptn (level + 1) tc lab[tc + o]!).1,
        ptn := ptn.set! tc (level + 1), active := insert 0 tc,
        numcells := numcells + 1, hint := 0, maxpos := 0,
        longcode := numcells + 1 }
      (worksetOf (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        tc tc) := by
  have hen := target_end_lt hpsz hend hcell
  have hinj' := labInj_breakout (lab := lab) (ptn := ptn)
    (level := level) (tc := tc) (o := o)
    (by rw [hlsz]; exact hinj) (by omega)
  intro q hq
  rcases child_cells_cases hpsz hend hvals hcell hne hq with
    rfl | rfl | ⟨hqm, hne2⟩
  · exact Or.inr (Nat.and_self _)
  · refine Or.inl (worksetOf_disjoint fun v hv1 hv2 => ?_)
    obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv1
    obtain ⟨w', hw', hwv'⟩ := mem_segN_iff.mp hv2
    have hw0 : w' = 0 := by omega
    subst hw0
    have hwv2 : (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1[tc + 1 + w]! = v := hwv
    have hwv3 : (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1[tc + 0]! = v := hwv'
    have := hinj' (tc + 0) (tc + 1 + w) (by rw [hlsz]; omega)
      (by rw [hlsz]; omega) (hwv3.trans hwv2.symm)
    omega
  · obtain ⟨hq1, hq2, hqe⟩ := (mem_cells_iff (by omega) hend).mp hqm
    have hout : q.2 < tc ∨ e < q.1 := by
      rcases Decidable.em (q.1 < tc) with hlt | hge
      · obtain ⟨-, h2t, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
        have htcs : ptn[tc - 1]! ≤ level := by
          rcases h2t with h0 | hcl
          · omega
          · exact hcl
        refine Or.inl ?_
        rw [hqe]
        exact cellEnd_lt_start hlt htcs
      · refine Or.inr ?_
        rcases Decidable.em (q.1 ≤ e) with hle | hgt
        · exfalso
          have hop := target_open hpsz hend hcell (q.1 - 1) (by omega)
            (by omega)
          rcases hq2 with h0 | hcl
          · omega
          · omega
        · omega
    have hq2lt : q.2 < ctx.n := by
      rw [hqe, ← hpsz]
      exact cellEnd_lt (by omega) hend
    have hq12 : q.1 ≤ q.2 := by
      rw [hqe]
      exact cellEnd_ge
    refine Or.inl (worksetOf_disjoint fun v hv1 hv2 => ?_)
    obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv1
    obtain ⟨w', hw', hwv'⟩ := mem_segN_iff.mp hv2
    have hw0 : w' = 0 := by omega
    subst hw0
    have hwv2 : (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1[q.1 + w]! = v := hwv
    have hwv3 : (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1[tc + 0]! = v := hwv'
    have := hinj' (tc + 0) (q.1 + w) (by rw [hlsz]; omega)
      (by rw [hlsz]; omega) (hwv3.trans hwv2.symm)
    rcases hout with h | h <;> omega

/-- Unchanged windows keep their member lists. -/
private theorem segN_breakout_congr {a len : Nat}
    (hout : a + len ≤ tc ∨ tc + o < a) :
    segN (breakout lab ptn (level + 1) tc lab[tc + o]!).1 a len =
      segN lab a len := by
  rw [segN, segN]
  refine List.map_congr_left fun w hw => ?_
  have hwr := List.mem_range.mp hw
  rw [breakout_lab_at (by rw [hlsz]; exact hinj)
    (by have := target_end_lt hpsz hend hcell; rw [hlsz]; omega)]
  rcases hout with h | h
  · rw [ite_eq_left (by omega)]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega)]

/-- Members of the rotated target window sit inside the parent target
window. -/
private theorem segN_breakout_target_sub {a len : Nat}
    (hin : tc ≤ a) (hlen : a + len ≤ e + 1) :
    ∀ v ∈ segN (breakout lab ptn (level + 1) tc lab[tc + o]!).1 a len,
      v ∈ segN lab tc (e + 1 - tc) := by
  intro v hv
  obtain ⟨w, hw, hwv⟩ := mem_segN_iff.mp hv
  rw [breakout_lab_at (by rw [hlsz]; exact hinj)
    (by have := target_end_lt hpsz hend hcell; rw [hlsz]; omega)] at hwv
  refine mem_segN_iff.mpr ?_
  rcases Decidable.em (a + w < tc) with h1 | h1
  · omega
  · rcases Decidable.em (a + w = tc) with h2 | h2
    · rw [ite_eq_right h1, ite_eq_left h2] at hwv
      exact ⟨o, by omega, hwv⟩
    · rcases Decidable.em (a + w ≤ tc + o) with h3 | h3
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3] at hwv
        exact ⟨a + w - 1 - tc, by omega, by
          rw [show tc + (a + w - 1 - tc) = a + w - 1 by omega]
          exact hwv⟩
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3] at hwv
        exact ⟨a + w - tc, by omega, by
          rw [show tc + (a + w - tc) = a + w by omega]
          exact hwv⟩

variable (hE : Equitable ctx level lab ptn)

include hE

/-- A child cell's members are covered by a parent cell's constancy
into any parent-cell splitter set. -/
private theorem constOn_child {W : Nat} {c : Nat × Nat}
    (hc : c ∈ cells (ptn.set! tc (level + 1)) (level + 1) ctx.n)
    (hW : ∀ pc ∈ cells ptn level ctx.n,
      ConstOn ctx W (segN lab pc.1 (pc.2 + 1 - pc.1))) :
    ConstOn ctx W
      (segN (breakout lab ptn (level + 1) tc lab[tc + o]!).1 c.1
        (c.2 + 1 - c.1)) := by
  rcases child_cells_cases hpsz hend hvals hcell hne hc with
    rfl | rfl | ⟨hcm, hne2⟩
  · exact (hW _ hcell).mono
      (segN_breakout_target_sub hlsz hpsz hend hvals hinj hcell hne ho
        (Nat.le_refl _) (by omega))
  · exact (hW _ hcell).mono
      (segN_breakout_target_sub hlsz hpsz hend hvals hinj hcell hne ho
        (by omega) (by omega))
  · obtain ⟨hq1, hq2, hqe⟩ := (mem_cells_iff (by omega) hend).mp hcm
    have hout : c.2 < tc ∨ e < c.1 := by
      rcases Decidable.em (c.1 < tc) with hlt | hge
      · obtain ⟨-, h2t, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
        have htcs : ptn[tc - 1]! ≤ level := by
          rcases h2t with h0 | hcl
          · omega
          · exact hcl
        refine Or.inl ?_
        rw [hqe]
        exact cellEnd_lt_start hlt htcs
      · refine Or.inr ?_
        rcases Decidable.em (c.1 ≤ e) with hle | hgt
        · exfalso
          have hop := target_open hpsz hend hcell (c.1 - 1) (by omega)
            (by omega)
          rcases hq2 with h0 | hcl
          · omega
          · omega
        · omega
    have hc12 : c.1 ≤ c.2 := by
      rw [hqe]
      exact cellEnd_ge
    rw [segN_breakout_congr hlsz hpsz hend hvals hinj hcell hne ho (by
      rcases hout with h | h
      · exact Or.inl (by omega)
      · exact Or.inr (by omega))]
    exact hW _ hcm

/-- The certificate invariant of the child entry state: the parent's
equitability seeds every certificate, with the split-off singleton as
the one active cell. -/
theorem certInv_breakout :
    CertInv ctx (level + 1)
      { lab := (breakout lab ptn (level + 1) tc lab[tc + o]!).1,
        ptn := ptn.set! tc (level + 1), active := insert 0 tc,
        numcells := numcells + 1, hint := 0, maxpos := 0,
        longcode := numcells + 1 } := by
  intro p hp hpin c hc
  have hen := target_end_lt hpsz hend hcell
  rcases child_cells_cases hpsz hend hvals hcell hne hp with
    rfl | rfl | ⟨hpm, hne2⟩
  · rw [elem_single] at hpin
    simp at hpin
  · refine ⟨worksetOf (breakout lab ptn (level + 1) tc
      lab[tc + o]!).1 tc tc, ?_, ?_, ?_⟩
    · rw [activeUnion_breakout hlsz hpsz hend hvals hinj hcell hne ho]
      exact Nat.and_self _
    · exact saturated_breakout hlsz hpsz hend hvals hinj hcell hne ho
    · have hsplit : worksetOf (breakout lab ptn (level + 1) tc
          lab[tc + o]!).1 tc e =
          worksetOf (breakout lab ptn (level + 1) tc
            lab[tc + o]!).1 tc tc |||
          worksetOf (breakout lab ptn (level + 1) tc
            lab[tc + o]!).1 (tc + 1) e :=
        worksetOf_split (Nat.le_refl _) hne
      have hfull : worksetOf (breakout lab ptn (level + 1) tc
          lab[tc + o]!).1 tc e = worksetOf lab tc e :=
        worksetOf_breakout_full (by rw [hlsz]; exact hinj)
          (by rw [hlsz]; omega) ho (by omega)
      have hkey : worksetOf (breakout lab ptn (level + 1) tc
          lab[tc + o]!).1 (tc + 1) e |||
          worksetOf (breakout lab ptn (level + 1) tc
            lab[tc + o]!).1 tc tc = worksetOf lab tc e := by
        rw [Nat.or_comm, ← hsplit, hfull]
      rw [hkey]
      refine constOn_child hlsz hpsz hend hvals hinj hcell hne ho hE
        hc ?_
      intro pc hpc
      rw [← splitDone_iff_constOn]
      exact hE _ hpc _ hcell
  · refine ⟨0, Nat.zero_and _, fun q hq => Or.inl (Nat.and_zero _),
      ?_⟩
    rw [Nat.or_zero]
    obtain ⟨hq1, hq2, hqe⟩ := (mem_cells_iff (by omega) hend).mp hpm
    have hout : p.2 < tc ∨ e < p.1 := by
      rcases Decidable.em (p.1 < tc) with hlt | hge
      · obtain ⟨-, h2t, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
        have htcs : ptn[tc - 1]! ≤ level := by
          rcases h2t with h0 | hcl
          · omega
          · exact hcl
        refine Or.inl ?_
        rw [hqe]
        exact cellEnd_lt_start hlt htcs
      · refine Or.inr ?_
        rcases Decidable.em (p.1 ≤ e) with hle | hgt
        · exfalso
          have hop := target_open hpsz hend hcell (p.1 - 1) (by omega)
            (by omega)
          rcases hq2 with h0 | hcl
          · omega
          · omega
        · omega
    have hWp : worksetOf (breakout lab ptn (level + 1) tc
        lab[tc + o]!).1 p.1 p.2 = worksetOf lab p.1 p.2 :=
      worksetOf_breakout_outside (by rw [hlsz]; exact hinj)
        (by rw [hlsz]; omega)
        (by rcases hout with h | h
            · exact Or.inl h
            · exact Or.inr (by omega))
    rw [hWp]
    refine constOn_child hlsz hpsz hend hvals hinj hcell hne ho hE
      hc ?_
    intro pc hpc
    rw [← splitDone_iff_constOn]
    exact hE _ hpc _ hpm

end Seed

section Package

variable {lab ptn : Array Nat} {level tc e o numcells : Nat}

/-- Splitting one open position advances the boundary count by exactly
one at the next level. -/
theorem bcount_breakout_eq {nn : Nat}
    (hvals : ∀ q, q < nn → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (htc : ptn[tc]! > level) (htcs : tc < ptn.size) :
    ∀ m, m ≤ nn →
      bcount (ptn.set! tc (level + 1)) (level + 1) m =
        bcount ptn level m + (if tc < m then 1 else 0) := by
  intro m
  induction m with
  | zero =>
    intro _
    rw [ite_eq_right (by omega)]
    rw [bcount, bcount]
    simp
  | succ m ih =>
    intro hm
    rw [bcount_succ, bcount_succ, ih (by omega)]
    rcases Decidable.em (tc = m) with heq | hne
    · have hset : (ptn.set! tc (level + 1))[m]! = level + 1 := by
        rw [← heq]
        exact Array.getElem!_set!_self _ _ _ htcs
      have hm2 : ¬ ptn[m]! ≤ level := by
        rw [← heq]
        omega
      rw [hset,
        ite_eq_left (by omega : level + 1 ≤ level + 1),
        ite_eq_right (by omega : ¬ tc < m),
        ite_eq_right hm2,
        ite_eq_left (by omega : tc < m + 1)]
    · have hset : (ptn.set! tc (level + 1))[m]! = ptn[m]! :=
        Array.getElem!_set!_ne _ _ _ _ hne
      rw [hset]
      rcases hvals m (by omega) with hlo | hhi
      · rw [ite_eq_left (show ptn[m]! ≤ level + 1 by omega),
          ite_eq_left hlo]
        rcases Decidable.em (tc < m) with h | h
        · rw [ite_eq_left h, ite_eq_left (show tc < m + 1 by omega)]
        · rw [ite_eq_right h,
            ite_eq_right (show ¬ tc < m + 1 by omega)]
      · rw [ite_eq_right (show ¬ ptn[m]! ≤ level + 1 by omega),
          ite_eq_right (show ¬ ptn[m]! ≤ level by omega)]
        rcases Decidable.em (tc < m) with h | h
        · rw [ite_eq_left h, ite_eq_left (show tc < m + 1 by omega)]
        · rw [ite_eq_right h,
            ite_eq_right (show ¬ tc < m + 1 by omega)]

/-- The descent theorem: individualizing any vertex of a nontrivial
cell of an equitable partition and refining with the singleton active
yields an equitable partition at the next level. -/
theorem equitable_breakout
    (hlsz : lab.size = ctx.n) (hpsz : ptn.size = ctx.n)
    (hend : ptn[ptn.size - 1]! ≤ level)
    (hvals : ∀ q, q < ctx.n → ptn[q]! ≤ level ∨ level + 1 < ptn[q]!)
    (hlab : LabOk lab ctx.n) (hinj : LabInj lab ctx.n)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hE : Equitable ctx level lab ptn)
    (hcell : (tc, e) ∈ cells ptn level ctx.n) (hne : tc < e)
    (ho : o ≤ e - tc)
    (hacc : bcount ptn level ctx.n = numcells) :
    Equitable ctx (level + 1)
      (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        (ptn.set! tc (level + 1)) (insert 0 tc) (numcells + 1)).lab
      (refine ctx (level + 1)
        (breakout lab ptn (level + 1) tc lab[tc + o]!).1
        (ptn.set! tc (level + 1)) (insert 0 tc) (numcells + 1)).ptn := by
  have hen := target_end_lt hpsz hend hcell
  have htcn : tc < ctx.n := by omega
  have hto : tc + o < lab.size := by rw [hlsz]; omega
  obtain ⟨-, hstart, -⟩ := (mem_cells_iff (by omega) hend).mp hcell
  have hopen : ptn[tc]! > level :=
    target_open hpsz hend hcell tc (Nat.le_refl _) hne
  refine refine_equitable ?_ ?_ ?_ ?_ ?_ ?_ ?_ hsymm ?_ ?_
  · rw [breakout_lab_size, hlsz]
  · intro i hi
    rw [breakout_lab_size] at hi
    rw [breakout_lab_at (by rw [hlsz]; exact hinj) hto i]
    rcases Decidable.em (i < tc) with h1 | h1
    · rw [ite_eq_left h1]
      exact hlab i hi
    · rcases Decidable.em (i = tc) with heq2 | h2
      · rw [ite_eq_right h1, ite_eq_left heq2]
        exact hlab _ (by omega)
      · rcases Decidable.em (i ≤ tc + o) with h3 | h3
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3]
          exact hlab _ (by omega)
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
          exact hlab i hi
  · rw [Array.size_set! _ _ _, hpsz]
  · rw [insert, Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
    exact Nat.pow_lt_pow_right (by omega) htcn
  · rw [Array.size_set! _ _ _]
    rcases Decidable.em (tc = ptn.size - 1) with rfl | hx
    · rw [Array.getElem!_set!_self _ _ _ (by omega)]
      omega
    · rw [Array.getElem!_set!_ne _ _ _ _ hx]
      omega
  · have h := labInj_breakout (lab := lab) (ptn := ptn)
      (level := level) (tc := tc) (o := o)
      (by rw [hlsz]; exact hinj) hto
    rw [hlsz] at h
    exact h
  · intro v hv
    rw [elem_single] at hv
    have hvtc : v = tc := of_decide_eq_true hv
    rw [hvtc]
    rcases Decidable.em (tc = 0) with h00 | h00
    · exact Or.inl h00
    · rcases hstart with h0 | hcl
      · exact Or.inl h0
      · refine Or.inr ?_
        rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
        omega
  · rw [bcount_breakout_eq hvals hopen (by omega) ctx.n
      (Nat.le_refl _), ite_eq_left htcn, hacc]
  · exact certInv_breakout hlsz hpsz hend hvals hinj hcell hne ho hE

end Package

/-! # The guard's cell-size consequences

In the first branch of `cheapautom`'s guard the defect is at most the
nontrivial cell count plus one, which forces every nontrivial cell to
a pair except at most one triple; in particular every non-pair cell
has odd size, the `hOdd` hypothesis of the flip theorem. -/

section Sizes

variable {ptn : Array Nat} {level nn : Nat}

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

/-- The first guard branch forces non-pair cells to odd size: every
nontrivial cell is a pair except at most one triple. -/
theorem hOdd_of_defect_le
    (hps : ptn.size = nn) (hend : ptn[ptn.size - 1]! ≤ level)
    (hguard : nn - (cells ptn level nn).length ≤
      (cells ptn level nn).countP (fun p => decide (p.1 < p.2)) + 1) :
    ∀ q ∈ cells ptn level nn, q.2 ≠ q.1 + 1 →
      (q.2 + 1 - q.1) % 2 = 1 := by
  intro q hq hnp
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
  rcases Decidable.em (q.2 = q.1) with heq | hne2
  · rw [heq]
    omega
  · have hge3 : q.1 + 2 ≤ q.2 := by omega
    have hle3 : q.2 ≤ q.1 + 2 := by omega
    rw [show q.2 + 1 - q.1 = 3 by omega]

end Sizes

end Descent

end Hex.GraphIso.Nauty
