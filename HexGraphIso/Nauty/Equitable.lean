/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CellPerm
public import HexGraphIso.Nauty.Achieved
public import HexGraphIso.Nauty.SearchInv

public section

/-!
Equitable partitions (SPEC § Verified search refinement, the
cheapautom clause of the store-validity obligation).

`refine` makes the partition at `level` equitable with respect to the
exhausted active set. The manual chapter states this as prose; this
file begins its formalization. The target theorem is: when
`refineLoop` exits because `pickSplit` finds no active cell, the
partition is `Equitable`. Discrete exits are covered separately by
`equitable_of_singletons`.

The intended loop invariant, recorded here for the follow-up work:
for every cell `C` of the current partition and every cell `D` not in
the active set, there is a set `U` of current cells with `D ∈ U` and
every other member of `U` active, such that `C` has constant
neighbour counts into the union of `U` (`SplitDone` on the union).
At exit the certificate `U` collapses to `{D}`, giving equitability.
The invariant survives a splitting pass because a pass leaves every
current cell with constant counts into the captured splitter set
(each processed cell is rearranged into constant-count groups, and a
cell that does not split already had constant counts), and because
`SplitDone` only strengthens under refinement of either cell. The
fragment that the activation rule leaves inactive is covered by the
certificate consisting of its active sibling fragments together with
the parent's certificate, since counts into the parent are the sum of
counts into the fragments. Exit by fuel is excluded by a potential
argument: `popCount active + 2 * (n - numcells)` drops by at least
one per pass, and starts at most `3 * n`, below the supplied
`4 * n + 8`.

This file proves the predicate layer and the per-cell postcondition
of the trivial-splitter pass. The pass level, the loop invariant, the
nontrivial-splitter pass, the fuel bound, and the cheapautom
small-cell lemma remain.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx}

/-- The window of `len` positions from `lo` has constant neighbour
counts into the vertex set `workset`. -/
def SplitDone (ctx : Ctx) (lab : Array Nat) (workset lo len : Nat) : Prop :=
  ∀ o o', o < len → o' < len →
    popCount (workset &&& ctx.g[lab[lo + o]!]!) =
      popCount (workset &&& ctx.g[lab[lo + o']!]!)

/-- The partition at `level` is equitable: every cell has constant
neighbour counts into every cell's vertex set. -/
def Equitable (ctx : Ctx) (level : Nat) (lab ptn : Array Nat) : Prop :=
  ∀ cd ∈ cells ptn level ctx.n, ∀ de ∈ cells ptn level ctx.n,
    SplitDone ctx lab (worksetOf lab de.1 de.2) cd.1 (cd.2 + 1 - cd.1)

/-- Constant counts restrict to any sub-window. -/
theorem SplitDone.sub {lab : Array Nat} {workset lo len lo' len' : Nat}
    (h : SplitDone ctx lab workset lo len) (hlo : lo ≤ lo')
    (hhi : lo' + len' ≤ lo + len) : SplitDone ctx lab workset lo' len' := by
  intro o o' ho ho'
  have h1 := h (lo' - lo + o) (lo' - lo + o') (by omega) (by omega)
  have e1 : lo + (lo' - lo + o) = lo' + o := by omega
  have e2 : lo + (lo' - lo + o') = lo' + o' := by omega
  rwa [e1, e2] at h1

/-- Windows with at most one position have constant counts. -/
theorem splitDone_of_le_one {lab : Array Nat} {workset lo len : Nat}
    (h : len ≤ 1) : SplitDone ctx lab workset lo len := by
  intro o o' ho ho'
  have : o = o' := by omega
  rw [this]

/-- Constant counts transfer between labellings agreeing on the
window. -/
theorem SplitDone.congr {lab lab' : Array Nat} {workset lo len : Nat}
    (h : SplitDone ctx lab workset lo len)
    (hagree : ∀ o, o < len → lab'[lo + o]! = lab[lo + o]!) :
    SplitDone ctx lab' workset lo len := by
  intro o o' ho ho'
  rw [hagree o ho, hagree o' ho']
  exact h o o' ho ho'

/-- A discrete partition is equitable. -/
theorem equitable_of_singletons {level : Nat} {lab ptn : Array Nat}
    (h : ∀ cd ∈ cells ptn level ctx.n, cd.2 = cd.1) :
    Equitable ctx level lab ptn := by
  intro cd hcd de _
  exact splitDone_of_le_one (by rw [h cd hcd]; omega)

/-- A power of two has one set bit. -/
private theorem popCount_two_pow : ∀ u : Nat, popCount (2 ^ u) = 1
  | 0 => by rw [Nat.pow_zero, popCount_eq, popCount_eq]; simp
  | u + 1 => by
    have h2 : 2 ^ (u + 1) = 2 * 2 ^ u := by
      rw [Nat.pow_succ, Nat.mul_comm]
    rw [h2, popCount_eq, Nat.mul_mod_right,
      Nat.mul_div_cancel_left _ (by omega : 0 < 2), Nat.zero_add]
    exact popCount_two_pow u

/-- The count into a single-vertex set is the adjacency bit. -/
theorem popCount_and_single (u x : Nat) :
    popCount (insert 0 u &&& x) = if x.testBit u then 1 else 0 := by
  rcases hbit : x.testBit u with _ | _
  · have hz : insert 0 u &&& x = 0 := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_and, testBit_insert, Nat.zero_testBit,
        Bool.false_or]
      rcases Decidable.em (u = i) with rfl | hne
      · simp [hbit]
      · simp [hne]
    rw [hz, popCount_zero]
    rfl
  · have hs : insert 0 u &&& x = insert 0 u := by
      refine Nat.eq_of_testBit_eq fun i => ?_
      simp only [Nat.testBit_and, testBit_insert, Nat.zero_testBit,
        Bool.false_or]
      rcases Decidable.em (u = i) with rfl | hne
      · simp [hbit]
      · simp [hne]
    have hval : insert 0 u = 2 ^ u := by
      show 0 ||| 1 <<< u = 2 ^ u
      rw [Nat.zero_or, Nat.shiftLeft_eq, Nat.one_mul]
    rw [hs, hval, popCount_two_pow]
    rfl

/-- Constant adjacency to a vertex on a window gives constant counts
into its singleton set. -/
theorem splitDone_single_of_const {lab : Array Nat} {u lo len : Nat}
    {b : Bool}
    (hconst : ∀ o, o < len → (ctx.g[lab[lo + o]!]!).testBit u = b) :
    SplitDone ctx lab (insert 0 u) lo len := by
  intro o o' ho ho'
  rw [popCount_and_single, popCount_and_single, hconst o ho, hconst o' ho']

/-- The two-pointer pass separates a window: the first `cnt` positions
hold splitter-adjacent vertices and the remainder non-adjacent ones,
where `cnt` is the window's adjacency count. -/
theorem splitCellLoop_memConst {gRow : Nat} {lab : Array Nat}
    {cell1 cell2 : Nat} (h12 : cell1 ≤ cell2) (hsz : cell2 < lab.size) :
    (∀ o, o < (segN lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·) →
      elem gRow (splitCellLoop gRow (cell2 - cell1 + 2) lab
        (Int.ofNat cell1) (Int.ofNat cell2)).1[cell1 + o]! = true) ∧
    (∀ o, (segN lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·) ≤ o →
      o < cell2 + 1 - cell1 →
      elem gRow (splitCellLoop gRow (cell2 - cell1 + 2) lab
        (Int.ofNat cell1) (Int.ofNat cell2)).1[cell1 + o]! = false) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := splitCellLoop_spec
    (gRow := gRow) (cell2 + 1 - cell1) (cell2 - cell1 + 2) lab
    (Int.ofNat cell1) (Int.ofNat cell2)
    (by simp only [Int.ofNat_eq_natCast]; omega)
    (by
      have : (cell2 : Int) < (lab.size : Int) := by
        exact_mod_cast hsz
      simpa using this)
    (by
      rw [show (Int.ofNat cell2 + 1 - Int.ofNat cell1) =
        ((cell2 + 1 - cell1 : Nat) : Int) from by
          simp only [Int.ofNat_eq_natCast]
          omega])
    (by omega)
  have htn : (Int.ofNat cell1).toNat = cell1 := rfl
  rw [htn] at h5 h6
  refine ⟨fun o ho => ?_, fun o hcnt ho => ?_⟩
  · have hmem : (splitCellLoop gRow (cell2 - cell1 + 2) lab
        (Int.ofNat cell1) (Int.ofNat cell2)).1[cell1 + o]! ∈
        segN (splitCellLoop gRow (cell2 - cell1 + 2) lab
          (Int.ofNat cell1) (Int.ofNat cell2)).1 cell1
          ((segN lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·)) :=
      mem_segN_iff.mpr ⟨o, ho, rfl⟩
    have hfil := h5.mem_iff.mp hmem
    exact (List.mem_filter.mp hfil).2
  · have hmem : (splitCellLoop gRow (cell2 - cell1 + 2) lab
        (Int.ofNat cell1) (Int.ofNat cell2)).1[cell1 + o]! ∈
        segN (splitCellLoop gRow (cell2 - cell1 + 2) lab
          (Int.ofNat cell1) (Int.ofNat cell2)).1
          (cell1 + (segN lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·))
          ((cell2 + 1 - cell1) -
            (segN lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·)) := by
      refine mem_segN_iff.mpr
        ⟨o - (segN lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·),
          by omega, ?_⟩
      congr 1
      omega
    have hfil := h6.mem_iff.mp hmem
    have := (List.mem_filter.mp hfil).2
    rcases hval : elem gRow (splitCellLoop gRow (cell2 - cell1 + 2) lab
        (Int.ofNat cell1) (Int.ofNat cell2)).1[cell1 + o]! with _ | _
    · rfl
    · rw [hval] at this
      cases this

/-- A processed cell of the trivial-splitter pass: the labelling
outside the cell is untouched, the cell keeps its contents as a
multiset, and it is rearranged into the splitter-adjacent block
followed by the non-adjacent block. -/
theorem trivialCell_memConst {level gRow cell1 cell2 : Nat} {st : RefineSt}
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size) :
    (trivialCell level gRow cell1 cell2 st).lab.size = st.lab.size ∧
    (∀ j, j < cell1 ∨ cell2 < j →
      (trivialCell level gRow cell1 cell2 st).lab[j]! = st.lab[j]!) ∧
    ((segN (trivialCell level gRow cell1 cell2 st).lab cell1
      (cell2 + 1 - cell1)).Perm
      (segN st.lab cell1 (cell2 + 1 - cell1))) ∧
    (∀ o, o < (segN st.lab cell1 (cell2 + 1 - cell1)).countP
        (elem gRow ·) →
      elem gRow (trivialCell level gRow cell1 cell2 st).lab[cell1 + o]! =
        true) ∧
    (∀ o, (segN st.lab cell1 (cell2 + 1 - cell1)).countP
        (elem gRow ·) ≤ o →
      o < cell2 + 1 - cell1 →
      elem gRow (trivialCell level gRow cell1 cell2 st).lab[cell1 + o]! =
        false) := by
  rcases Decidable.em (cell1 = cell2) with rfl | hne
  · have heq : trivialCell level gRow cell1 cell1 st = st := by
      rw [trivialCell]
      simp
    rw [heq]
    have hw : cell1 + 1 - cell1 = 1 := by omega
    have hseg : segN st.lab cell1 (cell1 + 1 - cell1) =
        [st.lab[cell1]!] := by
      rw [hw, segN_cons, segN_zero]
    refine ⟨rfl, fun j _ => rfl, List.Perm.refl _, fun o ho => ?_,
      fun o hcnt ho => ?_⟩
    · rw [hseg] at ho
      rcases hval : elem gRow st.lab[cell1]! with _ | _
      · simp [hval] at ho
      · have ho0 : o = 0 := by
          simp [hval] at ho
          omega
        rw [ho0, Nat.add_zero]
        exact hval
    · rw [hw] at ho
      have ho0 : o = 0 := by omega
      rw [hseg] at hcnt
      rcases hval : elem gRow st.lab[cell1]! with _ | _
      · rw [ho0, Nat.add_zero]
        exact hval
      · simp [hval] at hcnt
        exact absurd ho (by omega)
  · have heq : trivialCell level gRow cell1 cell2 st =
        trivialSplit level cell1 cell2
          (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
            (Int.ofNat cell1) (Int.ofNat cell2)).2.1
          (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
            (Int.ofNat cell1) (Int.ofNat cell2)).2.2
          { st with lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
              (Int.ofNat cell1) (Int.ofNat cell2)).1 } := by
      rw [trivialCell]
      simp [hne]
    obtain ⟨hs1, hs2, hs3, hs4, hs5, hs6⟩ := splitCellLoop_spec
      (gRow := gRow) (cell2 + 1 - cell1) (cell2 - cell1 + 2) st.lab
      (Int.ofNat cell1) (Int.ofNat cell2)
      (by simp only [Int.ofNat_eq_natCast]; omega)
      (by
        have : (cell2 : Int) < (st.lab.size : Int) := by
          exact_mod_cast hsz
        simpa using this)
      (by
        rw [show (Int.ofNat cell2 + 1 - Int.ofNat cell1) =
          ((cell2 + 1 - cell1 : Nat) : Int) from by
            simp only [Int.ofNat_eq_natCast]
            omega])
      (by omega)
    obtain ⟨hm1, hm2⟩ := splitCellLoop_memConst (gRow := gRow) h12 hsz
    rw [heq, trivialSplit_lab]
    refine ⟨hs3, fun j hj => ?_, splitCellLoop_region_perm h12 hsz,
      hm1, hm2⟩
    refine hs4 j ?_
    simp only [Int.ofNat_eq_natCast]
    omega

/-! # Member-level constancy

`ConstOn` restates `SplitDone` on the member list itself, which makes
the transport lemmas the loop invariant needs (restriction to a
subset, union and difference of splitter sets) one-line membership
arguments instead of window index shuffles. -/

/-- Constant neighbour counts into `W` over a member list. -/
def ConstOn (ctx : Ctx) (W : Nat) (ms : List Nat) : Prop :=
  ∀ x ∈ ms, ∀ y ∈ ms,
    popCount (W &&& ctx.g[x]!) = popCount (W &&& ctx.g[y]!)

theorem ConstOn.mono {W : Nat} {ms ms' : List Nat}
    (h : ConstOn ctx W ms) (hsub : ∀ x ∈ ms', x ∈ ms) :
    ConstOn ctx W ms' :=
  fun x hx y hy => h x (hsub x hx) y (hsub y hy)

theorem ConstOn.perm {W : Nat} {ms ms' : List Nat}
    (h : ConstOn ctx W ms) (hp : ms'.Perm ms) : ConstOn ctx W ms' :=
  h.mono fun _ hx => hp.mem_iff.mp hx

theorem splitDone_iff_constOn {lab : Array Nat} {W lo len : Nat} :
    SplitDone ctx lab W lo len ↔ ConstOn ctx W (segN lab lo len) := by
  constructor
  · intro h x hx y hy
    obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hx
    obtain ⟨o', ho', rfl⟩ := mem_segN_iff.mp hy
    exact h o o' ho ho'
  · intro h o o' ho ho'
    exact h _ (mem_segN_iff.mpr ⟨o, ho, rfl⟩)
      _ (mem_segN_iff.mpr ⟨o', ho', rfl⟩)

/-! # Counts into disjoint unions -/

private theorem countP_or_disjoint {p q : Nat → Bool} :
    ∀ l : List Nat, (∀ i ∈ l, ¬(p i = true ∧ q i = true)) →
      l.countP (fun i => p i || q i) = l.countP p + l.countP q
  | [], _ => rfl
  | x :: l, h => by
    rw [List.countP_cons, List.countP_cons, List.countP_cons,
      countP_or_disjoint l fun i hi => h i (List.mem_cons_of_mem x hi)]
    rcases hp : p x with _ | _ <;> rcases hq : q x with _ | _
    · simp
    · simp; omega
    · simp; omega
    · exact absurd ⟨hp, hq⟩ (h x (List.mem_cons_self ..))

/-- Populations add over a disjoint union. -/
theorem popCount_or_disjoint {a b n : Nat} (hd : a &&& b = 0)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) :
    popCount (a ||| b) = popCount a + popCount b := by
  have hor : a ||| b < 2 ^ n := by
    have := Nat.or_lt_two_pow ha hb
    exact this
  rw [popCount_eq_bitCount n _ hor, popCount_eq_bitCount n a ha,
    popCount_eq_bitCount n b hb]
  unfold bitCount
  rw [show (a ||| b).testBit = fun i => a.testBit i || b.testBit i from
    funext fun i => Nat.testBit_or a b i]
  refine countP_or_disjoint _ fun i _ hpq => ?_
  have := congrArg (fun s => s.testBit i) hd
  simp only [Nat.testBit_and, Nat.zero_testBit, hpq.1, hpq.2] at this
  cases this

/-- The intersection with any set keeps the submask relation on the
left component. -/
private theorem and_left_submask (a x : Nat) : (a &&& x) &&& a = a &&& x := by
  rw [Nat.and_assoc, Nat.and_comm x a, ← Nat.and_assoc, Nat.and_self]

private theorem and_lt_two_pow {a n : Nat} (ha : a < 2 ^ n) (x : Nat) :
    a &&& x < 2 ^ n :=
  Nat.lt_of_le_of_lt (Nat.and_le_left) ha

/-- Neighbour counts add over a disjoint union of vertex sets. -/
theorem count_or_disjoint {a b n : Nat} (hd : a &&& b = 0)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n) (x : Nat) :
    popCount ((a ||| b) &&& x) =
      popCount (a &&& x) + popCount (b &&& x) := by
  have hdist : (a ||| b) &&& x = (a &&& x) ||| (b &&& x) := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    simp only [Nat.testBit_and, Nat.testBit_or]
    rcases a.testBit i <;> rcases b.testBit i <;> rcases x.testBit i <;> rfl
  have hd' : (a &&& x) &&& (b &&& x) = 0 := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    have := congrArg (fun s => s.testBit i) hd
    simp only [Nat.testBit_and, Nat.zero_testBit] at this ⊢
    rcases hax : a.testBit i with _ | _ <;>
      rcases hbx : b.testBit i with _ | _ <;> simp_all
  rw [hdist,
    popCount_or_disjoint hd' (and_lt_two_pow ha x) (and_lt_two_pow hb x)]

/-- Constancy into two disjoint sets gives constancy into the union. -/
theorem ConstOn.or {a b n : Nat} {ms : List Nat} (hd : a &&& b = 0)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h1 : ConstOn ctx a ms) (h2 : ConstOn ctx b ms) :
    ConstOn ctx (a ||| b) ms := by
  intro x hx y hy
  rw [count_or_disjoint hd ha hb, count_or_disjoint hd ha hb,
    h1 x hx y hy, h2 x hx y hy]

/-- Constancy into a disjoint union and into the right part gives
constancy into the left part. -/
theorem ConstOn.of_or {a b n : Nat} {ms : List Nat} (hd : a &&& b = 0)
    (ha : a < 2 ^ n) (hb : b < 2 ^ n)
    (h1 : ConstOn ctx (a ||| b) ms) (h2 : ConstOn ctx b ms) :
    ConstOn ctx a ms := by
  intro x hx y hy
  have hx1 := h1 x hx y hy
  have hx2 := h2 x hx y hy
  rw [count_or_disjoint hd ha hb, count_or_disjoint hd ha hb] at hx1
  omega

/-! # Splitter sets of cells -/

/-- Splitter sets of member-disjoint segments are disjoint. -/
theorem worksetOf_disjoint {lab lab' : Array Nat} {lo hi lo' hi' : Nat}
    (h : ∀ v, v ∈ segN lab lo (hi + 1 - lo) →
      v ∈ segN lab' lo' (hi' + 1 - lo') → False) :
    worksetOf lab lo hi &&& worksetOf lab' lo' hi' = 0 := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  rw [Nat.testBit_and, Nat.zero_testBit, testBit_worksetOf,
    testBit_worksetOf]
  rcases h1 : (segN lab lo (hi + 1 - lo)).any (· == v) with _ | _
  · rfl
  · rcases h2 : (segN lab' lo' (hi' + 1 - lo')).any (· == v) with _ | _
    · rfl
    · obtain ⟨x, hx, hxv⟩ := List.any_eq_true.mp h1
      obtain ⟨y, hy, hyv⟩ := List.any_eq_true.mp h2
      simp only [beq_iff_eq] at hxv hyv
      subst hxv
      exact absurd (hyv ▸ hy) fun hm => h x hx hm

/-- A splitter set splits at any interior junction of its window. -/
theorem worksetOf_split {lab : Array Nat} {lo j hi : Nat}
    (hlo : lo ≤ j) (hj : j < hi) :
    worksetOf lab lo hi =
      worksetOf lab lo j ||| worksetOf lab (j + 1) hi := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  rw [Nat.testBit_or, testBit_worksetOf, testBit_worksetOf,
    testBit_worksetOf,
    show hi + 1 - lo = (j + 1 - lo) + (hi + 1 - (j + 1)) from by omega,
    segN_append, List.any_append,
    show lo + (j + 1 - lo) = j + 1 from by omega]

/-- Membership in a splitter set is membership of the segment. -/
theorem elem_worksetOf {lab : Array Nat} {lo hi v : Nat} :
    elem (worksetOf lab lo hi) v = true ↔
      v ∈ segN lab lo (hi + 1 - lo) := by
  rw [elem, testBit_worksetOf, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, hxv⟩
    simp only [beq_iff_eq] at hxv
    exact hxv ▸ hx
  · intro hv
    exact ⟨v, hv, by simp⟩

/-- Adjacency to a vertex constant over a member list gives constant
counts into its singleton set, through row symmetry. -/
theorem constOn_single_of_adj {v : Nat} {ms : List Nat} {b : Bool}
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hv : v < ctx.n) (hms : ∀ x ∈ ms, x < ctx.n)
    (hconst : ∀ x ∈ ms, (ctx.g[v]!).testBit x = b) :
    ConstOn ctx (insert 0 v) ms := by
  intro x hx y hy
  rw [popCount_and_single, popCount_and_single,
    hsymm x v (hms x hx) hv, hsymm y v (hms y hy) hv,
    hconst x hx, hconst y hy]

/-! # The trivial-splitter pass: block postconditions

Each processed cell leaves its window as an adjacent block followed by
a non-adjacent block, with the junction boundary written exactly when
both blocks are nonempty. The pass-level induction then shows every
final cell sits inside one block of its window. -/

/-- The split bookkeeping's partition effect: one boundary at the
final `c2` when the split is nontrivial, nothing otherwise. -/
theorem trivialSplit_ptn_eq (level cell1 cell2 : Nat) (c1 c2 : Int)
    (st : RefineSt) :
    (trivialSplit level cell1 cell2 c1 c2 st).ptn =
      if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
        st.ptn.set! c2.toNat level
      else
        st.ptn := by
  rw [trivialSplit]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with
    hA | hA
  · rw [ite_eq_left hA, ite_eq_left hA]
    rcases Decidable.em
        (elem st.active cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hB | hB
    · rw [ite_eq_left hB]
      rcases (c1.toNat == cell2) with _ | _ <;> rfl
    · rw [ite_eq_right hB]
      rcases (c2.toNat == cell1) with _ | _ <;> rfl
  · rw [ite_eq_right hA, ite_eq_right hA]

/-- One processed cell of the trivial pass: sizes and the outside
kept, and the window left as constant block(s) with the junction
boundary written exactly in the two-block case. -/
theorem trivialCell_effect {level gRow cell1 cell2 : Nat} {st : RefineSt}
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size) :
    (trivialCell level gRow cell1 cell2 st).lab.size = st.lab.size ∧
    (∀ j, j < cell1 ∨ cell2 < j →
      (trivialCell level gRow cell1 cell2 st).lab[j]! = st.lab[j]!) ∧
    (((trivialCell level gRow cell1 cell2 st).ptn = st.ptn ∧
        ∃ b : Bool, ∀ p, cell1 ≤ p → p ≤ cell2 →
          elem gRow (trivialCell level gRow cell1 cell2 st).lab[p]! = b) ∨
      (∃ j, cell1 ≤ j ∧ j < cell2 ∧
        (trivialCell level gRow cell1 cell2 st).ptn = st.ptn.set! j level ∧
        (∀ p, cell1 ≤ p → p ≤ j →
          elem gRow (trivialCell level gRow cell1 cell2 st).lab[p]! =
            true) ∧
        (∀ p, j < p → p ≤ cell2 →
          elem gRow (trivialCell level gRow cell1 cell2 st).lab[p]! =
            false))) := by
  obtain ⟨hsize, houtside, hperm, htrue, hfalse⟩ :=
    trivialCell_memConst (level := level) (gRow := gRow) (st := st)
      h12 hsz
  refine ⟨hsize, houtside, ?_⟩
  obtain ⟨cnt, hcnt⟩ : ∃ c,
      (segN st.lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·) = c :=
    ⟨_, rfl⟩
  rw [hcnt] at htrue hfalse
  have hcntle : cnt ≤ cell2 + 1 - cell1 := by
    have := List.countP_le_length (l := segN st.lab cell1 (cell2 + 1 - cell1))
      (p := (elem gRow ·))
    rw [segN_length, hcnt] at this
    exact this
  have hptn : (trivialCell level gRow cell1 cell2 st).ptn =
      if 1 ≤ cnt ∧ cnt ≤ cell2 - cell1 then
        st.ptn.set! (cell1 + cnt - 1) level
      else
        st.ptn := by
    rcases Decidable.em (cell1 = cell2) with rfl | hne
    · have heq : trivialCell level gRow cell1 cell1 st = st := by
        rw [trivialCell]
        simp
      rw [heq, ite_eq_right (by omega)]
    · have heq : trivialCell level gRow cell1 cell2 st =
          trivialSplit level cell1 cell2
            (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
              (Int.ofNat cell1) (Int.ofNat cell2)).2.1
            (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
              (Int.ofNat cell1) (Int.ofNat cell2)).2.2
            { st with lab := (splitCellLoop gRow (cell2 - cell1 + 2) st.lab
                (Int.ofNat cell1) (Int.ofNat cell2)).1 } := by
        rw [trivialCell]
        simp [hne]
      obtain ⟨hp1, hp2, _, _, _, _⟩ := splitCellLoop_spec
        (gRow := gRow) (cell2 + 1 - cell1) (cell2 - cell1 + 2) st.lab
        (Int.ofNat cell1) (Int.ofNat cell2)
        (by simp only [Int.ofNat_eq_natCast]; omega)
        (by
          have : (cell2 : Int) < (st.lab.size : Int) := by
            exact_mod_cast hsz
          simpa using this)
        (by
          rw [show (Int.ofNat cell2 + 1 - Int.ofNat cell1) =
            ((cell2 + 1 - cell1 : Nat) : Int) from by
              simp only [Int.ofNat_eq_natCast]
              omega])
        (by omega)
      have htn : (Int.ofNat cell1).toNat = cell1 := rfl
      rw [htn] at hp1 hp2
      rw [heq, trivialSplit_ptn_eq]
      dsimp only
      rw [hp1, hp2, hcnt]
      rcases Decidable.em (1 ≤ cnt ∧ cnt ≤ cell2 - cell1) with hc | hc
      · rw [ite_eq_left hc, ite_eq_left (by
          constructor
          · simp only [Int.ofNat_eq_natCast]
            omega
          · simp only [Int.ofNat_eq_natCast]
            omega)]
        congr 1
        simp only [Int.ofNat_eq_natCast]
        omega
      · rw [ite_eq_right hc, ite_eq_right (by
          intro ⟨hg1, hg2⟩
          simp only [Int.ofNat_eq_natCast] at hg1 hg2
          exact hc ⟨by omega, by omega⟩)]
  rcases Decidable.em (1 ≤ cnt ∧ cnt ≤ cell2 - cell1) with hc | hc
  · refine Or.inr ⟨cell1 + cnt - 1, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hptn, ite_eq_left hc]
    · intro p hp1 hp2
      have := htrue (p - cell1) (by omega)
      rwa [show cell1 + (p - cell1) = p from by omega] at this
    · intro p hp1 hp2
      have := hfalse (p - cell1) (by omega) (by omega)
      rwa [show cell1 + (p - cell1) = p from by omega] at this
  · refine Or.inl ⟨by rw [hptn, ite_eq_right hc], ?_⟩
    rcases Nat.eq_or_lt_of_le (Nat.zero_le cnt) with hz | hpos
    · refine ⟨false, fun p hp1 hp2 => ?_⟩
      have := hfalse (p - cell1) (by omega) (by omega)
      rwa [show cell1 + (p - cell1) = p from by omega] at this
    · have hfull : cnt = cell2 + 1 - cell1 := by omega
      refine ⟨true, fun p hp1 hp2 => ?_⟩
      have := htrue (p - cell1) (by omega)
      rwa [show cell1 + (p - cell1) = p from by omega] at this

/-- The trivial pass over a window list: sizes kept, everything
outside the windows kept, and every window left as constant block(s)
with a surviving junction boundary in the two-block case. -/
theorem refineTrivial_go_blocks {level gRow : Nat} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt),
      (∀ p ∈ cs, p.1 ≤ p.2 ∧ p.2 < st.lab.size) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      st.ptn.size = st.lab.size →
      (refineTrivial.go level gRow cs st).lab.size = st.lab.size ∧
      (∀ j, (∀ p ∈ cs, j < p.1 ∨ p.2 < j) →
        (refineTrivial.go level gRow cs st).lab[j]! = st.lab[j]!) ∧
      (∀ q, (∀ p ∈ cs, q < p.1 ∨ p.2 ≤ q) →
        (refineTrivial.go level gRow cs st).ptn[q]! = st.ptn[q]!) ∧
      (refineTrivial.go level gRow cs st).ptn.size = st.ptn.size ∧
      (∀ p ∈ cs,
        (∃ b : Bool, ∀ q, p.1 ≤ q → q ≤ p.2 →
          elem gRow (refineTrivial.go level gRow cs st).lab[q]! = b) ∨
        (∃ j, p.1 ≤ j ∧ j < p.2 ∧
          (refineTrivial.go level gRow cs st).ptn[j]! = level ∧
          (∀ q, p.1 ≤ q → q ≤ j →
            elem gRow (refineTrivial.go level gRow cs st).lab[q]! =
              true) ∧
          (∀ q, j < q → q ≤ p.2 →
            elem gRow (refineTrivial.go level gRow cs st).lab[q]! =
              false)))
  | [], st, _, _, _ => by
    rw [refineTrivial.go]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, fun p hp =>
      absurd hp (by simp)⟩
  | (c1, c2) :: rest, st, hw, hpw, hlp => by
    rw [refineTrivial.go]
    obtain ⟨h12, hsz⟩ := hw (c1, c2) (List.mem_cons_self ..)
    dsimp only at h12 hsz
    obtain ⟨hsize, houtside, hblocks⟩ :=
      trivialCell_effect (level := level) (gRow := gRow) (st := st)
        h12 hsz
    have hps1 : (trivialCell level gRow c1 c2 st).ptn.size =
        st.ptn.size := by
      rcases hblocks with ⟨he, _⟩ | ⟨j, _, _, he, _, _⟩
      · rw [he]
      · rw [he, Array.size_set!]
    have hpout : ∀ q, q < c1 ∨ c2 ≤ q →
        (trivialCell level gRow c1 c2 st).ptn[q]! = st.ptn[q]! := by
      intro q hq
      rcases hblocks with ⟨he, _⟩ | ⟨j, hj1, hj2, he, _, _⟩
      · rw [he]
      · rw [he, Array.getElem!_set!_ne _ _ _ _ (by omega)]
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ :=
      refineTrivial_go_blocks rest (trivialCell level gRow c1 c2 st)
        (fun p hp => by
          obtain ⟨hp1, hp2⟩ := hw p (List.mem_cons_of_mem _ hp)
          exact ⟨hp1, by rw [hsize]; exact hp2⟩)
        (List.pairwise_cons.mp hpw).2
        (by rw [hps1, hsize]; exact hlp)
    have hhead := (List.pairwise_cons.mp hpw).1
    refine ⟨by rw [ih1, hsize], ?_, ?_, by rw [ih4, hps1], ?_⟩
    · intro j hj
      rw [ih2 j (fun p hp => hj p (List.mem_cons_of_mem _ hp)),
        houtside j (by
          have := hj (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · intro q hq
      rw [ih3 q (fun p hp => hq p (List.mem_cons_of_mem _ hp)),
        hpout q (by
          have := hq (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · have hlabkeep : ∀ q, c1 ≤ q → q ≤ c2 →
            (refineTrivial.go level gRow rest
              (trivialCell level gRow c1 c2 st)).lab[q]! =
              (trivialCell level gRow c1 c2 st).lab[q]! := by
          intro q hq1 hq2
          exact ih2 q fun pr hpr => Or.inl (by
            have := hhead pr hpr
            simp only at this
            omega)
        rcases hblocks with ⟨_, b, hb⟩ | ⟨j, hj1, hj2, he, ht, hf⟩
        · exact Or.inl ⟨b, fun q hq1 hq2 => by
            rw [hlabkeep q hq1 hq2]
            exact hb q hq1 hq2⟩
        · refine Or.inr ⟨j, hj1, hj2, ?_, ?_, ?_⟩
          · rw [ih3 j fun pr hpr => Or.inl (by
              have := hhead pr hpr
              simp only at this
              omega),
              he, Array.getElem!_set!_self _ _ _ (by
                rw [hlp]
                omega)]
          · intro q hq1 hq2
            rw [hlabkeep q hq1 (by omega)]
            exact ht q hq1 hq2
          · intro q hq1 hq2
            rw [hlabkeep q (by omega) hq2]
            exact hf q hq1 hq2
      · exact ih5 p hmem

/-- With the last in-range position closed, cell ends stay in
range. -/
theorem cells_end_lt_of_end {ptn : Array Nat} {level nn : Nat}
    (hnn : nn ≤ ptn.size) (hend : ptn[ptn.size - 1]! ≤ level)
    (hendn : ptn[nn - 1]! ≤ level) :
    ∀ p ∈ cells ptn level nn, p.2 < nn := by
  intro p hp
  have hc := cells_isCell hnn hend p hp
  have hle := cells_le p hp
  have hstart := cells_go_ge (ptn := ptn) (level := level) (nn := nn)
    nn 0 p (by rw [cells] at hp; exact hp)
  rcases Nat.lt_or_ge p.2 nn with h | h
  · exact h
  · exfalso
    have hn0 : 0 < nn := by
      rcases Nat.eq_or_lt_of_le (Nat.zero_le nn) with hz | hp0
      · rw [cells] at hp
        rw [← hz] at hp
        rw [cells.go] at hp
        exact absurd hp (by simp)
      · exact hp0
    have hp1lt : p.1 < nn := by
      rcases Nat.lt_or_ge p.1 nn with h1 | h1
      · exact h1
      · exfalso
        rw [cells] at hp
        have := cells_go_lt_aux hp h1
        exact this
    have hint := hc.2.2.1 (nn - 1) (by omega) (by omega)
    omega
where
  cells_go_lt_aux {ptn : Array Nat} {level nn : Nat} {p : Nat × Nat} :
    ∀ {fuel c1 : Nat}, p ∈ cells.go ptn level nn fuel c1 →
      nn ≤ p.1 → False
  | 0, _, hp, _ => absurd hp (by simp [cells.go])
  | fuel + 1, c1, hp, hge => by
    rw [cells.go] at hp
    split at hp
    · next h =>
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hmem
      · simp only at hge
        omega
      · have := cells_go_ge (ptn := ptn) (level := level) (nn := nn)
          fuel _ p hmem
        have hge2 := cellEnd_ge (ptn := ptn) (level := level) (i := c1)
        exact cells_go_lt_aux hmem hge
    · exact absurd hp (by simp)

/-- After the trivial pass, every cell of the result within range is
adjacency-constant to the captured splitter row. -/
theorem refineTrivial_cell_adj {ctx : Ctx} {level split1 : Nat}
    {st : RefineSt} (hpsz : st.ptn.size = ctx.n)
    (hlp : st.lab.size = st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    ∀ a len, IsCell (refineTrivial ctx level split1 st).ptn level a len →
      a + len ≤ ctx.n →
      ∃ b : Bool, ∀ q, a ≤ q → q < a + len →
        elem (ctx.g[st.lab[split1]!]!)
          (refineTrivial ctx level split1 st).lab[q]! = b := by
  intro a len hcell halen
  have hnn : ctx.n ≤ st.ptn.size := Nat.le_of_eq hpsz.symm
  have hendn : st.ptn[ctx.n - 1]! ≤ level := by
    have h := hend
    rw [hpsz] at h
    exact h
  have hwind : ∀ p ∈ cells st.ptn level ctx.n,
      p.1 ≤ p.2 ∧ p.2 < st.lab.size := fun p hp =>
    ⟨cells_le p hp, by
      have := cells_end_lt_of_end hnn hend hendn p hp
      omega⟩
  obtain ⟨g1, g2, g3, g4, g5⟩ := refineTrivial_go_blocks
    (level := level) (gRow := ctx.g[st.lab[split1]!]!)
    (cells st.ptn level ctx.n) st hwind cells_pairwise hlp.symm
  rw [refineTrivial] at hcell ⊢
  have hpres : ∀ q : Nat, st.ptn[q]! ≤ level →
      (refineTrivial.go level (ctx.g[st.lab[split1]!]!)
        (cells st.ptn level ctx.n) st).ptn[q]! = st.ptn[q]! := by
    intro q hq
    refine g3 q fun p hp => ?_
    rcases Nat.lt_or_ge q ctx.n with hqn | hqn
    · obtain ⟨pc, hpcm, hpc1, hpc2⟩ := cells_cover q hqn
      have hqend : q = pc.2 := by
        have hic := cells_isCell hnn hend pc hpcm
        rcases Nat.eq_or_lt_of_le hpc2 with he | hlt
        · exact he
        · exfalso
          have := hic.2.2.1 q (by omega) (by
            have := cells_le pc hpcm
            omega)
          omega
      have hicp := cells_isCell hnn hend p hp
      have hicpc := cells_isCell hnn hend pc hpcm
      have hle_p := cells_le p hp
      have hle_pc := cells_le pc hpcm
      rcases isCell_disjoint_or_eq hicp hicpc with hd | hd | hd
      · left
        omega
      · right
        omega
      · right
        omega
    · right
      have := cells_end_lt_of_end hnn hend hendn p hp
      omega
  have hgrow : ∀ q : Nat, st.ptn[q]! ≤ level →
      (refineTrivial.go level (ctx.g[st.lab[split1]!]!)
        (cells st.ptn level ctx.n) st).ptn[q]! ≤ level := by
    intro q hq
    rw [hpres q hq]
    exact hq
  have hl0 : 0 < len := hcell.1
  obtain ⟨c, lenC, hcC, hca, hcb⟩ := subcell_of_grow (ptn0 := st.ptn)
    g4.symm hcell hend hgrow (by omega) (by omega)
  have hmem : (c, c + lenC - 1) ∈ cells st.ptn level ctx.n :=
    isCell_mem_cells hcC hnn hend (by omega)
  have hlen0 := hcC.1
  rcases g5 (c, c + lenC - 1) hmem with ⟨b, hb⟩ | ⟨j, hj1, hj2, hjlev, ht, hf⟩
  · dsimp only at hb
    exact ⟨b, fun q hq1 hq2 => hb q (by omega) (by omega)⟩
  · dsimp only at hj1 hj2 hjlev ht hf
    rcases Nat.lt_or_ge j a with hja | hja
    · exact ⟨false, fun q hq1 hq2 => hf q (by omega) (by omega)⟩
    · rcases Nat.lt_or_ge j (a + len - 1) with hjl | hjl
      · exfalso
        have := hcell.2.2.1 j (by omega) (by omega)
        omega
      · exact ⟨true, fun q hq1 hq2 => ht q (by omega) (by omega)⟩

end Hex.GraphIso.Nauty
