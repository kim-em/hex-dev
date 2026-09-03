/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexGraphIso.Nauty.CellPerm
public import HexGraphIso.Nauty.Achieved
public import HexGraphIso.Nauty.SearchInv
public import HexGraphIso.Nauty.PopCount

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

Proven so far: the predicate layer; the member-level `ConstOn`
toolkit (disjoint-union count additivity, union and difference
transport, splitter-set disjointness and window splitting); both
splitting passes' postconditions, culminating in
`refineStep_cell_const` — after one `refineStep`, every cell of the
result has constant counts into the retired splitter's captured
vertex set, uniformly across trivial and nontrivial splitters; and
the certificate interface `CertInv`/`activeUnion`/`Saturated` with
its collapse at exit (`equitable_of_certInv_exit`,
`active_eq_zero_of_pickSplit_none`).

Remaining for the fixpoint theorem: the preservation of `CertInv`
across `refineStep` (consuming `refineStep_cell_const` for the
retired splitter's subtraction, per-old-cell member permutations from
the `RefInv` machinery for workset stability, and a characterization
of the active set's evolution through the passes — the one piece with
no existing machinery); the fuel potential
`popCount active + 2 * (n - numcells)`; and on top of the fixpoint
theorem the cheapautom small-cell lemma and the arm-2 assembly.
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

/-! # The nontrivial-splitter pass: group postconditions

The window scan writes a boundary at the end of every nonempty count
group whose end stays inside the cell, and the counting-sort
redistribution lays the members out in ascending count-group order, so
positions of the result connected by an open run carry equal counts
into the captured splitter set. -/

/-- The scan closes the junction after each nonempty group that ends
inside the cell. -/
theorem windowScan_junction {level cell1 cell2 : Nat} {counts : List Nat} :
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt),
      cell1 ≤ c1 →
      c1 + (vs.map (multOf counts)).sum = cell2 + 1 →
      cell2 < st.ptn.size →
      (∀ p, c1 ≤ p → p < cell2 → st.ptn[p]! > level) →
      ∀ k, k < vs.length → 0 < multOf counts vs[k]! →
        c1 + ((vs.take (k + 1)).map (multOf counts)).sum ≤ cell2 →
        (windowScan level cell1 cell2 counts vs c1 maxcell st).ptn[
          c1 + ((vs.take (k + 1)).map (multOf counts)).sum - 1]! = level
  | [], _, _, _, _, _, _, _, k, hk, _, _ => absurd hk (by simp)
  | v :: vs', c1, maxcell, st, hc1, htot, hsz, hfresh, k, hk, hmk, hend => by
    rw [windowScan]
    rw [List.map_cons, List.sum_cons] at htot
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · rw [ite_eq_left hm]
      have hp1 := ptn_windowStep_eq level cell1 cell2 v c1
        (c1 + multOf counts v) maxcell st
      cases k with
      | zero =>
        rw [List.take_succ_cons, List.take_zero, List.map_cons,
          List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
          at hend ⊢
        rw [List.getElem!_cons_zero] at hmk
        have hwrite : (windowStep level cell1 cell2 v c1
            (c1 + multOf counts v) maxcell st).ptn =
            st.ptn.set! (c1 + multOf counts v - 1) level := by
          rw [hp1, ite_eq_left (by omega)]
        obtain ⟨_, _, hout, hsizes, _⟩ := windowScan_payload
          (nn := cell2 + 1) (counts := counts)
          (show cell2 < cell2 + 1 by omega) vs'
          (c1 + multOf counts v)
          (if Int.ofNat (multOf counts v) > maxcell then
            Int.ofNat (multOf counts v) else maxcell)
          (windowStep level cell1 cell2 v c1
            (c1 + multOf counts v) maxcell st)
          (show cell1 ≤ c1 + multOf counts v by omega)
          (show c1 + multOf counts v +
            (vs'.map (multOf counts)).sum = cell2 + 1 by omega)
          (by rw [hwrite, Array.size_set!]; omega)
          (by
            intro p hp1' hp2'
            rw [hwrite, Array.getElem!_set!_ne _ _ _ _ (by omega)]
            exact hfresh p (by omega) hp2')
        rw [hout (c1 + multOf counts v - 1) (Or.inl (by omega)), hwrite,
          Array.getElem!_set!_self _ _ _ (by omega)]
      | succ j =>
        rw [List.take_succ_cons, List.map_cons, List.sum_cons] at hend ⊢
        rw [List.getElem!_cons_succ] at hmk
        have hidx : c1 + (multOf counts v +
            ((vs'.take (j + 1)).map (multOf counts)).sum) =
            (c1 + multOf counts v) +
              ((vs'.take (j + 1)).map (multOf counts)).sum := by
          omega
        rw [hidx] at hend ⊢
        refine windowScan_junction vs' (c1 + multOf counts v) _ _
          (by omega) (by omega)
          (by
            rw [ptn_windowStep_eq]
            split
            · rw [Array.size_set!]
              omega
            · omega)
          (by
            intro p hp1' hp2'
            rw [ptn_windowStep_eq]
            split
            · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)]
              exact hfresh p (by omega) hp2'
            · exact hfresh p (by omega) hp2')
          j (by simpa using hk) hmk hend
    · rw [ite_eq_right hm]
      cases k with
      | zero =>
        rw [List.getElem!_cons_zero] at hmk
        omega
      | succ j =>
        rw [List.take_succ_cons, List.map_cons, List.sum_cons] at hend ⊢
        rw [List.getElem!_cons_succ] at hmk
        have hm0 : multOf counts v = 0 := by omega
        rw [hm0] at hend ⊢
        simp only [Nat.zero_add] at hend ⊢
        exact windowScan_junction vs' c1 maxcell st hc1 (by omega) hsz
          hfresh j (by simpa using hk) hmk hend

/-! ## The counting-sort layout, block by block -/

private theorem zipIdx_countP_fst' (w : Nat) :
    ∀ (cs : List Nat) (s : Nat),
      ((cs.zipIdx s).countP fun p => p.1 == w) = cs.countP (· == w)
  | [], _ => rfl
  | x :: xs, s => by
    rw [List.zipIdx_cons, List.countP_cons, List.countP_cons,
      zipIdx_countP_fst' w xs (s + 1)]

/-- One value's chunk of the counting-sort layout. -/
private def chunkOf (lab : Array Nat) (cell1 : Nat) (counts : List Nat)
    (v : Nat) : List Nat :=
  (counts.zipIdx.filter fun p => p.1 == v).map fun p => lab[cell1 + p.2]!

private theorem chunkOf_length (lab : Array Nat) (cell1 : Nat)
    (counts : List Nat) (v : Nat) :
    (chunkOf lab cell1 counts v).length = multOf counts v := by
  rw [chunkOf, List.length_map, ← List.countP_eq_length_filter,
    zipIdx_countP_fst', multOf]

theorem countsOf_getElem! {ctx : Ctx} {lab : Array Nat}
    {workset cell1 cell2 j : Nat} (hj : j < cell2 + 1 - cell1) :
    (countsOf ctx lab workset cell1 cell2)[j]! =
      popCount (workset &&& ctx.g[lab[cell1 + j]!]!) := by
  rw [countsOf_eq_map,
    getElem!_pos _ j (by rw [List.length_map, segN_length]; exact hj),
    List.getElem_map,
    ← getElem!_pos (segN lab cell1 (cell2 + 1 - cell1)) j
      (by rw [segN_length]; exact hj),
    segN_getElem! lab cell1 (cell2 + 1 - cell1) j hj]

/-- Every element of a chunk carries the chunk's count value. -/
private theorem chunkOf_count {ctx : Ctx} {lab : Array Nat}
    {workset cell1 cell2 : Nat} {v x : Nat}
    (hx : x ∈ chunkOf lab cell1 (countsOf ctx lab workset cell1 cell2) v) :
    popCount (workset &&& ctx.g[x]!) = v := by
  rw [chunkOf] at hx
  obtain ⟨p, hpf, rfl⟩ := List.mem_map.mp hx
  have hpm := List.mem_filter.mp hpf
  obtain ⟨c, j⟩ := p
  obtain ⟨_, hjlt, hcv⟩ := List.mem_zipIdx hpm.1
  rw [Nat.zero_add, countsOf_length] at hjlt
  have hcv' : c = (countsOf ctx lab workset cell1 cell2)[j]! := by
    rw [getElem!_pos _ j (by rw [countsOf_length]; exact hjlt), hcv]
    rfl
  have hbeq : c = v := by
    have := hpm.2
    simpa using this
  dsimp only
  rw [← countsOf_getElem! hjlt, ← hcv', hbeq]

private theorem getElem!_append_left'' {β : Type} [Inhabited β]
    {as bs : List β} {i : Nat} (h : i < as.length) :
    (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [List.length_append]; omega),
    getElem!_pos as i h, List.getElem_append_left h]

private theorem getElem!_append_right'' {β : Type} [Inhabited β]
    {as bs : List β} {i : Nat} (h : as.length ≤ i)
    (hi : i - as.length < bs.length) :
    (as ++ bs)[i]! = bs[i - as.length]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [List.length_append]; omega),
    getElem!_pos bs (i - as.length) hi, List.getElem_append_right h]

/-- Reading inside block `k` of a flat concatenation. -/
private theorem flatMap_getElem!_chunk {α β : Type} [Inhabited α]
    [Inhabited β] (g : α → List β) :
    ∀ (vs : List α) (k o : Nat), k < vs.length → o < (g vs[k]!).length →
      (vs.flatMap g)[((vs.take k).flatMap g).length + o]! = (g vs[k]!)[o]!
  | [], k, _, hk, _ => absurd hk (by simp)
  | x :: xs, 0, o, _, ho => by
    rw [List.getElem!_cons_zero] at ho ⊢
    rw [List.take_zero, List.flatMap_nil, List.length_nil, Nat.zero_add,
      List.flatMap_cons, getElem!_append_left'' ho]
  | x :: xs, k + 1, o, hk, ho => by
    rw [List.getElem!_cons_succ] at ho ⊢
    have hk' : k < xs.length := by
      simp only [List.length_cons] at hk
      omega
    rw [List.take_succ_cons, List.flatMap_cons, List.flatMap_cons,
      List.length_append]
    have hbound : ((xs.take k).flatMap g).length + o <
        (xs.flatMap g).length := by
      have h1 : ((xs.take (k + 1)).flatMap g).length ≤
          (xs.flatMap g).length := by
        rw [List.length_flatMap, List.length_flatMap]
        conv =>
          rhs
          rw [← List.take_append_drop (k + 1) xs]
        rw [List.map_append, List.sum_append]
        omega
      have h2 : ((xs.take (k + 1)).flatMap g).length =
          ((xs.take k).flatMap g).length + (g xs[k]!).length := by
        rw [List.take_add_one, List.getElem?_eq_getElem hk',
          Option.toList_some, List.flatMap_append, List.length_append,
          List.flatMap_cons, List.flatMap_nil, List.append_nil,
          getElem!_pos xs k hk']
      omega
    have hstep := getElem!_append_right'' (as := g x) (bs := xs.flatMap g)
      (i := (g x).length + (((xs.take k).flatMap g).length + o))
      (by omega) (by omega)
    have harr1 : (g x).length + ((xs.take k).flatMap g).length + o =
        (g x).length + (((xs.take k).flatMap g).length + o) := by omega
    have harr2 : (g x).length + (((xs.take k).flatMap g).length + o) -
        (g x).length = ((xs.take k).flatMap g).length + o := by omega
    rw [harr1, hstep, harr2]
    exact flatMap_getElem!_chunk g xs k o hk' ho

/-- Every offset of a flat concatenation lies in a nonempty block. -/
private theorem chunk_of_offset {α β : Type} [Inhabited α] (g : α → List β) :
    ∀ (vs : List α) (o : Nat), o < (vs.flatMap g).length →
      ∃ k, k < vs.length ∧ 0 < (g vs[k]!).length ∧
        ((vs.take k).flatMap g).length ≤ o ∧
        o < ((vs.take (k + 1)).flatMap g).length
  | [], o, ho => absurd ho (by simp)
  | x :: xs, o, ho => by
    rw [List.flatMap_cons, List.length_append] at ho
    rcases Nat.lt_or_ge o (g x).length with hlt | hge
    · refine ⟨0, by simp, ?_, ?_, ?_⟩
      · rw [List.getElem!_cons_zero]
        omega
      · rw [List.take_zero, List.flatMap_nil, List.length_nil]
        omega
      · rw [List.take_succ_cons, List.take_zero, List.flatMap_cons,
          List.flatMap_nil, List.append_nil]
        omega
    · obtain ⟨k, hk, hne, hlo, hhi⟩ := chunk_of_offset g xs
        (o - (g x).length) (by omega)
      refine ⟨k + 1, by simp only [List.length_cons]; omega, ?_, ?_, ?_⟩
      · rw [List.getElem!_cons_succ]
        exact hne
      · rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
        omega
      · rw [List.take_succ_cons, List.flatMap_cons, List.length_append]
        omega

private theorem take_chunk_length {lab : Array Nat} {cell1 : Nat}
    (counts : List Nat) (vs : List Nat) (k : Nat) :
    ((vs.take k).flatMap (chunkOf lab cell1 counts)).length =
      ((vs.take k).map (multOf counts)).sum := by
  rw [List.length_flatMap]
  congr 1
  exact List.map_congr_left fun v _ => chunkOf_length lab cell1 counts v

private theorem take_map_sum_mono (f : Nat → Nat) :
    ∀ (vs : List Nat) (a b : Nat), a ≤ b →
      ((vs.take a).map f).sum ≤ ((vs.take b).map f).sum
  | [], _, _, _ => by simp
  | v :: vs, 0, b, _ => by
    rw [List.take_zero]
    exact Nat.zero_le _
  | v :: vs, a + 1, 0, hab => absurd hab (by omega)
  | v :: vs, a + 1, b + 1, hab => by
    rw [List.take_succ_cons, List.take_succ_cons, List.map_cons,
      List.map_cons, List.sum_cons, List.sum_cons]
    have := take_map_sum_mono f vs a b (by omega)
    omega

private theorem segmentOf_chunks (lab : Array Nat) (cell1 : Nat)
    (counts values : List Nat) :
    segmentOf lab cell1 counts values =
      values.flatMap (chunkOf lab cell1 counts) := rfl

private theorem take_flatMap_succ_length {α β : Type} [Inhabited α]
    (g : α → List β) (vs : List α) (k : Nat) (hk : k < vs.length) :
    ((vs.take (k + 1)).flatMap g).length =
      ((vs.take k).flatMap g).length + (g vs[k]!).length := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk,
    Option.toList_some, List.flatMap_append, List.length_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil,
    getElem!_pos vs k hk]

/-- One processed cell of the nontrivial pass: sizes and the outside
kept, and positions of the window connected by an open run of the
result carry equal counts into the captured splitter set. -/
theorem nontrivialCell_effect {ctx : Ctx} {level workset cell1 cell2 : Nat}
    {st : RefineSt} (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size)
    (hlp : st.ptn.size = st.lab.size)
    (hfresh : ∀ p, cell1 ≤ p → p < cell2 → st.ptn[p]! > level) :
    (nontrivialCell ctx level workset cell1 cell2 st).lab.size =
      st.lab.size ∧
    (∀ j, j < cell1 ∨ cell2 < j →
      (nontrivialCell ctx level workset cell1 cell2 st).lab[j]! =
        st.lab[j]!) ∧
    (∀ q, q < cell1 ∨ cell2 ≤ q →
      (nontrivialCell ctx level workset cell1 cell2 st).ptn[q]! =
        st.ptn[q]!) ∧
    (nontrivialCell ctx level workset cell1 cell2 st).ptn.size =
      st.ptn.size ∧
    (∀ q q', cell1 ≤ q → q ≤ q' → q' ≤ cell2 →
      (∀ i, q ≤ i → i < q' →
        (nontrivialCell ctx level workset cell1 cell2 st).ptn[i]! >
          level) →
      popCount (workset &&&
        ctx.g[(nontrivialCell ctx level workset cell1 cell2 st).lab[q]!]!) =
      popCount (workset &&&
        ctx.g[(nontrivialCell ctx level workset cell1 cell2 st).lab[q']!]!)) := by
  rcases hbeq : (cell1 == cell2) with _ | _
  · rcases hmm : ((countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
        ((countsOf ctx st.lab workset cell1 cell2).headD 0) ==
        (countsOf ctx st.lab workset cell1 cell2).foldl Nat.max
          ((countsOf ctx st.lab workset cell1 cell2).headD 0)) with _ | _
    · -- the counting-sort branch
      have hr : nontrivialCell ctx level workset cell1 cell2 st =
          nontrivialFix cell1
            { windowScan level cell1 cell2
                (countsOf ctx st.lab workset cell1 cell2)
                (countValues (countsOf ctx st.lab workset cell1 cell2))
                cell1 (-1) st with
              lab := writeSegment
                  (windowScan level cell1 cell2
                    (countsOf ctx st.lab workset cell1 cell2)
                    (countValues (countsOf ctx st.lab workset cell1 cell2))
                    cell1 (-1) st).lab cell1
                  (segmentOf
                    (windowScan level cell1 cell2
                      (countsOf ctx st.lab workset cell1 cell2)
                      (countValues (countsOf ctx st.lab workset cell1 cell2))
                      cell1 (-1) st).lab cell1
                    (countsOf ctx st.lab workset cell1 cell2)
                    (countValues (countsOf ctx st.lab workset cell1
                      cell2))) } := by
        rw [nontrivialCell, ite_eq_right (by simp [hbeq]),
          ite_eq_right (by simpa using hmm)]
      have hne : cell1 < cell2 := by
        have hnb : ¬(cell1 = cell2) := by simpa using hbeq
        omega
      have hlabscan : (windowScan level cell1 cell2
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st).lab = st.lab :=
        windowScan_lab level cell1 cell2 _ _ _ _ _
      rw [hr, nontrivialFix_lab, nontrivialFix_ptn]
      dsimp only
      rw [hlabscan]
      obtain ⟨_, _, hout, hsizes, _⟩ := windowScan_payload
        (nn := cell2 + 1)
        (counts := countsOf ctx st.lab workset cell1 cell2)
        (show cell2 < cell2 + 1 by omega)
        (countValues (countsOf ctx st.lab workset cell1 cell2))
        cell1 (-1) st (Nat.le_refl cell1)
        (by rw [sum_multOf_countValues, countsOf_length]; omega)
        (by omega) hfresh
      have hseglen : (segmentOf st.lab cell1
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))).length =
          cell2 + 1 - cell1 := by
        rw [segmentOf_chunks, List.length_flatMap,
          List.map_congr_left fun v _ =>
            chunkOf_length st.lab cell1
              (countsOf ctx st.lab workset cell1 cell2) v,
          sum_multOf_countValues, countsOf_length]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [writeSegment_size]
      · intro j hj
        rw [writeSegment_outside _ _ _ j (by
          rw [hseglen]
          omega)]
      · intro q hq
        exact hout q (by omega)
      · exact hsizes
      · intro q q' hq hqq hq' hopen
        have hwr : segN (writeSegment st.lab cell1
            (segmentOf st.lab cell1
              (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1 cell2))))
            cell1
            (segmentOf st.lab cell1
              (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1
                cell2))).length =
            segmentOf st.lab cell1
              (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1 cell2)) :=
          segN_writeSegment _ _ _ (by rw [hseglen]; omega)
        have hpos : ∀ p : Nat, cell1 ≤ p → p ≤ cell2 →
            (writeSegment st.lab cell1
              (segmentOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2)
                (countValues (countsOf ctx st.lab workset cell1
                  cell2))))[p]! =
            ((countValues (countsOf ctx st.lab workset cell1
              cell2)).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2)))[p - cell1]! := by
          intro p hp1 hp2
          rw [← segmentOf_chunks]
          have hsg := segN_getElem! (writeSegment st.lab cell1
            (segmentOf st.lab cell1
              (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1 cell2))))
            cell1
            (segmentOf st.lab cell1
              (countsOf ctx st.lab workset cell1 cell2)
              (countValues (countsOf ctx st.lab workset cell1
                cell2))).length
            (p - cell1) (by rw [hseglen]; omega)
          rw [hwr] at hsg
          have hpe : p = cell1 + (p - cell1) := by omega
          conv =>
            lhs
            rw [hpe]
          rw [← hsg]
        have hval : ∀ (o k : Nat),
            k < (countValues (countsOf ctx st.lab workset cell1
              cell2)).length →
            (((countValues (countsOf ctx st.lab workset cell1
              cell2)).take k).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length ≤ o →
            o < (((countValues (countsOf ctx st.lab workset cell1
              cell2)).take (k + 1)).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length →
            popCount (workset &&&
              ctx.g[((countValues (countsOf ctx st.lab workset cell1
                cell2)).flatMap
                (chunkOf st.lab cell1
                  (countsOf ctx st.lab workset cell1 cell2)))[o]!]!) =
              (countValues (countsOf ctx st.lab workset cell1
                cell2))[k]! := by
          intro o k hk hlo hhi
          have hsucc := take_flatMap_succ_length
            (chunkOf st.lab cell1
              (countsOf ctx st.lab workset cell1 cell2))
            (countValues (countsOf ctx st.lab workset cell1 cell2)) k hk
          have hoeq : o = (((countValues (countsOf ctx st.lab workset
              cell1 cell2)).take k).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length +
              (o - (((countValues (countsOf ctx st.lab workset cell1
                cell2)).take k).flatMap
                (chunkOf st.lab cell1
                  (countsOf ctx st.lab workset cell1
                    cell2))).length) := by
            omega
          rw [hoeq, flatMap_getElem!_chunk _ _ k _ hk (by omega)]
          refine chunkOf_count (lab := st.lab) (cell1 := cell1)
            (cell2 := cell2)
            (x := (chunkOf st.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            ((countValues (countsOf ctx st.lab workset cell1
              cell2))[k]!))[o - (((countValues (countsOf ctx st.lab
                workset cell1 cell2)).take k).flatMap
                (chunkOf st.lab cell1
                  (countsOf ctx st.lab workset cell1 cell2))).length]!)
            ?_
          rw [getElem!_pos (chunkOf st.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            ((countValues (countsOf ctx st.lab workset cell1
              cell2))[k]!))
            (o - (((countValues (countsOf ctx st.lab workset cell1
              cell2)).take k).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length)
            (by omega)]
          exact List.getElem_mem _
        have hoq : q - cell1 <
            ((countValues (countsOf ctx st.lab workset cell1
              cell2)).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length := by
          rw [← segmentOf_chunks, hseglen]
          omega
        have hoq' : q' - cell1 <
            ((countValues (countsOf ctx st.lab workset cell1
              cell2)).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length := by
          rw [← segmentOf_chunks, hseglen]
          omega
        obtain ⟨k, hk, hkne, hklo, hkhi⟩ := chunk_of_offset _ _ _ hoq
        obtain ⟨k', hk', hkne', hklo', hkhi'⟩ := chunk_of_offset _ _ _ hoq'
        rw [hpos q hq (by omega), hpos q' (by omega) hq',
          hval (q - cell1) k hk hklo hkhi,
          hval (q' - cell1) k' hk' hklo' hkhi']
        have hmono : ∀ a b : Nat, a ≤ b →
            (((countValues (countsOf ctx st.lab workset cell1
              cell2)).take a).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length ≤
            (((countValues (countsOf ctx st.lab workset cell1
              cell2)).take b).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length := by
          intro a b hab
          rw [take_chunk_length, take_chunk_length]
          exact take_map_sum_mono _ _ a b hab
        have hkk : k ≤ k' := by
          rcases Nat.lt_or_ge k' k with h | h
          · exfalso
            have := hmono (k' + 1) k h
            omega
          · exact h
        rcases Nat.eq_or_lt_of_le hkk with rfl | hklt
        · rfl
        · exfalso
          have hjunc := windowScan_junction
            (level := level) (cell1 := cell1) (cell2 := cell2)
            (counts := countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1 cell2))
            cell1 (-1) st (Nat.le_refl cell1)
            (by rw [sum_multOf_countValues, countsOf_length]; omega)
            (by omega) hfresh k hk
            (by
              rw [← chunkOf_length st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2)]
              exact hkne)
            (by
              have h1 : (((countValues (countsOf ctx st.lab workset
                  cell1 cell2)).take (k + 1)).flatMap
                  (chunkOf st.lab cell1
                    (countsOf ctx st.lab workset cell1 cell2))).length ≤
                  q' - cell1 :=
                Nat.le_trans (hmono (k + 1) k' hklt) hklo'
              rw [take_chunk_length] at h1
              omega)
          have hmulteq := take_chunk_length (lab := st.lab)
            (cell1 := cell1)
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1 cell2))
            (k + 1)
          have h1 : (((countValues (countsOf ctx st.lab workset
              cell1 cell2)).take (k + 1)).flatMap
              (chunkOf st.lab cell1
                (countsOf ctx st.lab workset cell1 cell2))).length ≤
              q' - cell1 :=
            Nat.le_trans (hmono (k + 1) k' hklt) hklo'
          have h2 := hopen (cell1 + (((countValues (countsOf ctx st.lab
              workset cell1 cell2)).take (k + 1)).map
              (multOf (countsOf ctx st.lab workset cell1
                cell2))).sum - 1)
            (by rw [← hmulteq]; omega)
            (by rw [← hmulteq]; omega)
          rw [hjunc] at h2
          omega
    · -- all counts equal: the window does not move
      have hr : nontrivialCell ctx level workset cell1 cell2 st =
          { st with
            longcode := mash st.longcode
              ((countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
                ((countsOf ctx st.lab workset cell1 cell2).headD 0) +
                cell1) } := by
        rw [nontrivialCell, ite_eq_right (by simp [hbeq]),
          ite_eq_left hmm]
      rw [hr]
      dsimp only
      refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, ?_⟩
      intro q q' hq hqq hq' _
      have hcnt : ∀ p : Nat, cell1 ≤ p → p ≤ cell2 →
          popCount (workset &&& ctx.g[st.lab[p]!]!) ∈
            countsOf ctx st.lab workset cell1 cell2 := by
        intro p hp1 hp2
        have hj : p - cell1 < cell2 + 1 - cell1 := by omega
        have hcg := countsOf_getElem! (ctx := ctx) (lab := st.lab)
          (workset := workset) (cell1 := cell1) (cell2 := cell2) hj
        have heqp : cell1 + (p - cell1) = p := by omega
        rw [heqp] at hcg
        rw [← hcg, getElem!_pos _ _ (by rw [countsOf_length]; omega)]
        exact List.getElem_mem _
      have hminmax := (beq_iff_eq).mp hmm
      have h1 := hcnt q hq (by omega)
      have h2 := hcnt q' (by omega) hq'
      have hle1 := foldl_min_le_mem _
        ((countsOf ctx st.lab workset cell1 cell2).headD 0) _ h1
      have hge1 := foldl_max_ge_mem _
        ((countsOf ctx st.lab workset cell1 cell2).headD 0) _ h1
      have hle2 := foldl_min_le_mem _
        ((countsOf ctx st.lab workset cell1 cell2).headD 0) _ h2
      have hge2 := foldl_max_ge_mem _
        ((countsOf ctx st.lab workset cell1 cell2).headD 0) _ h2
      omega
  · -- singleton window
    have hr : nontrivialCell ctx level workset cell1 cell2 st = st := by
      rw [nontrivialCell, ite_eq_left hbeq]
    have hc12 : cell1 = cell2 := beq_iff_eq.mp hbeq
    rw [hr]
    refine ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, ?_⟩
    intro q q' hq hqq hq' _
    have : q = q' := by omega
    rw [this]

/-- The nontrivial pass over a window list: sizes and the outside
kept, and within every window, positions connected by an open run of
the result carry equal counts into the captured splitter set. -/
theorem refineNontrivial_go_blocks {ctx : Ctx} {level workset : Nat} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt),
      (∀ p ∈ cs, p.1 ≤ p.2 ∧ p.2 < st.lab.size) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      st.ptn.size = st.lab.size →
      (∀ p ∈ cs, ∀ i, p.1 ≤ i → i < p.2 → st.ptn[i]! > level) →
      (refineNontrivial.go ctx level workset cs st).lab.size =
        st.lab.size ∧
      (∀ j, (∀ p ∈ cs, j < p.1 ∨ p.2 < j) →
        (refineNontrivial.go ctx level workset cs st).lab[j]! =
          st.lab[j]!) ∧
      (∀ q, (∀ p ∈ cs, q < p.1 ∨ p.2 ≤ q) →
        (refineNontrivial.go ctx level workset cs st).ptn[q]! =
          st.ptn[q]!) ∧
      (refineNontrivial.go ctx level workset cs st).ptn.size =
        st.ptn.size ∧
      (∀ p ∈ cs, ∀ q q', p.1 ≤ q → q ≤ q' → q' ≤ p.2 →
        (∀ i, q ≤ i → i < q' →
          (refineNontrivial.go ctx level workset cs st).ptn[i]! >
            level) →
        popCount (workset &&&
          ctx.g[(refineNontrivial.go ctx level workset cs st).lab[q]!]!) =
        popCount (workset &&&
          ctx.g[(refineNontrivial.go ctx level workset cs
            st).lab[q']!]!))
  | [], st, _, _, _, _ => by
    rw [refineNontrivial.go]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, rfl, fun p hp =>
      absurd hp (by simp)⟩
  | (c1, c2) :: rest, st, hw, hpw, hlp, hfr => by
    rw [refineNontrivial.go]
    obtain ⟨h12, hsz⟩ := hw (c1, c2) (List.mem_cons_self ..)
    dsimp only at h12 hsz
    have hfr0 : ∀ i, c1 ≤ i → i < c2 → st.ptn[i]! > level := by
      intro i hi1 hi2
      exact hfr (c1, c2) (List.mem_cons_self ..) i hi1 hi2
    obtain ⟨e1, e2, e3, e4, e5⟩ :=
      nontrivialCell_effect (ctx := ctx) (level := level)
        (workset := workset) (st := st) h12 hsz hlp hfr0
    obtain ⟨ih1, ih2, ih3, ih4, ih5⟩ :=
      refineNontrivial_go_blocks rest
        (nontrivialCell ctx level workset c1 c2 st)
        (fun p hp => by
          obtain ⟨hp1, hp2⟩ := hw p (List.mem_cons_of_mem _ hp)
          exact ⟨hp1, by rw [e1]; exact hp2⟩)
        (List.pairwise_cons.mp hpw).2
        (by rw [e4, e1]; exact hlp)
        (fun p hp i hi1 hi2 => by
          have hord := (List.pairwise_cons.mp hpw).1 p hp
          simp only at hord
          rw [e3 i (Or.inr (by omega))]
          exact hfr p (List.mem_cons_of_mem _ hp) i hi1 hi2)
    have hhead := (List.pairwise_cons.mp hpw).1
    refine ⟨by rw [ih1, e1], ?_, ?_, by rw [ih4, e4], ?_⟩
    · intro j hj
      rw [ih2 j (fun p hp => hj p (List.mem_cons_of_mem _ hp)),
        e2 j (by
          have := hj (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · intro q hq
      rw [ih3 q (fun p hp => hq p (List.mem_cons_of_mem _ hp)),
        e3 q (by
          have := hq (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · intro p hp q q' hq hqq hq' hopen
      rcases List.mem_cons.mp hp with rfl | hmem
      · dsimp only at hq hq' ⊢
        have hlabkeep : ∀ r, c1 ≤ r → r ≤ c2 →
            (refineNontrivial.go ctx level workset rest
              (nontrivialCell ctx level workset c1 c2 st)).lab[r]! =
              (nontrivialCell ctx level workset c1 c2 st).lab[r]! := by
          intro r hr1 hr2
          exact ih2 r fun pr hpr => Or.inl (by
            have := hhead pr hpr
            simp only at this
            omega)
        have hptnkeep : ∀ i, c1 ≤ i → i < c2 →
            (refineNontrivial.go ctx level workset rest
              (nontrivialCell ctx level workset c1 c2 st)).ptn[i]! =
              (nontrivialCell ctx level workset c1 c2 st).ptn[i]! := by
          intro i hi1 hi2
          exact ih3 i fun pr hpr => Or.inl (by
            have := hhead pr hpr
            simp only at this
            omega)
        rw [hlabkeep q hq (by omega), hlabkeep q' (by omega) hq']
        refine e5 q q' hq hqq hq' ?_
        intro i hi1 hi2
        rw [← hptnkeep i (by omega) (by omega)]
        exact hopen i hi1 hi2
      · refine ih5 p hmem q q' hq hqq hq' hopen

/-- After the nontrivial pass, every cell of the result within range
has constant counts into the captured splitter set. -/
theorem refineNontrivial_cell_const {ctx : Ctx}
    {level split1 split2 : Nat} {st : RefineSt}
    (hpsz : st.ptn.size = ctx.n) (hlp : st.lab.size = st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    ∀ a len,
      IsCell (refineNontrivial ctx level split1 split2 st).ptn level
        a len →
      a + len ≤ ctx.n →
      ConstOn ctx (worksetOf st.lab split1 split2)
        (segN (refineNontrivial ctx level split1 split2 st).lab a len) := by
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
  have hfrw : ∀ p ∈ cells st.ptn level ctx.n, ∀ i, p.1 ≤ i → i < p.2 →
      st.ptn[i]! > level := by
    intro p hp i hi1 hi2
    have hic := cells_isCell hnn hend p hp
    have hle := cells_le p hp
    have := hic.2.2.1 i hi1 (by omega)
    exact this
  obtain ⟨g1, g2, g3, g4, g5⟩ := refineNontrivial_go_blocks
    (ctx := ctx) (level := level)
    (workset := worksetOf st.lab split1 split2)
    (cells st.ptn level ctx.n)
    { st with
      longcode := mash st.longcode (split2 - split1 + 1) }
    hwind cells_pairwise hlp.symm hfrw
  rw [refineNontrivial] at hcell ⊢
  dsimp only at hcell g1 g2 g3 g4 g5 ⊢
  have hpres : ∀ q : Nat, st.ptn[q]! ≤ level →
      (refineNontrivial.go ctx level (worksetOf st.lab split1 split2)
        (cells st.ptn level ctx.n)
        { st with
          longcode := mash st.longcode (split2 - split1 + 1) }).ptn[q]! =
        st.ptn[q]! := by
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
      (refineNontrivial.go ctx level (worksetOf st.lab split1 split2)
        (cells st.ptn level ctx.n)
        { st with
          longcode := mash st.longcode
            (split2 - split1 + 1) }).ptn[q]! ≤ level := by
    intro q hq
    rw [hpres q hq]
    exact hq
  have hl0 : 0 < len := hcell.1
  obtain ⟨c, lenC, hcC, hca, hcb⟩ := subcell_of_grow (ptn0 := st.ptn)
    g4.symm hcell hend hgrow (by omega) (by omega)
  have hmem : (c, c + lenC - 1) ∈ cells st.ptn level ctx.n :=
    isCell_mem_cells hcC hnn hend (by omega)
  have hlen0 := hcC.1
  intro x hx y hy
  obtain ⟨ox, hox, rfl⟩ := mem_segN_iff.mp hx
  obtain ⟨oy, hoy, rfl⟩ := mem_segN_iff.mp hy
  have hrun : ∀ u u', a ≤ u → u ≤ u' → u' < a + len →
      ∀ i, u ≤ i → i < u' →
      (refineNontrivial.go ctx level (worksetOf st.lab split1 split2)
        (cells st.ptn level ctx.n)
        { st with
          longcode := mash st.longcode
            (split2 - split1 + 1) }).ptn[i]! > level := by
    intro u u' hu huu hu' i hi1 hi2
    exact hcell.2.2.1 i (by omega) (by omega)
  rcases Nat.le_total (a + ox) (a + oy) with hxy | hxy
  · exact g5 (c, c + lenC - 1) hmem (a + ox) (a + oy) (by
      dsimp only
      omega) hxy (by
      dsimp only
      omega)
      (hrun (a + ox) (a + oy) (by omega) hxy (by omega))
  · exact (g5 (c, c + lenC - 1) hmem (a + oy) (a + ox) (by
      dsimp only
      omega) hxy (by
      dsimp only
      omega)
      (hrun (a + oy) (a + ox) (by omega) hxy (by omega))).symm

/-! # One refinement step leaves every cell constant into the
retired splitter -/

theorem worksetOf_singleton (lab : Array Nat) (lo : Nat) :
    worksetOf lab lo lo = insert 0 lab[lo]! := by
  have h1 : lo + 1 - lo = 1 := by omega
  rw [worksetOf, h1]
  have h2 : List.range 1 = [0] := rfl
  rw [h2, List.foldl_cons, List.foldl_nil, Nat.add_zero]

/-- After one `refineStep`, every cell of the result within range has
constant counts into the retired splitter's captured vertex set. -/
theorem refineStep_cell_const {ctx : Ctx} {level split1 : Nat}
    {st : RefineSt} (hok : StOk ctx.n level st)
    (hsymm : ∀ u w, u < ctx.n → w < ctx.n →
      (ctx.g[u]!).testBit w = (ctx.g[w]!).testBit u)
    (hs1 : split1 < ctx.n) :
    ∀ a len, IsCell (refineStep ctx level split1 st).ptn level a len →
      a + len ≤ ctx.n →
      ConstOn ctx (worksetOf st.lab split1 (cellEnd st.ptn level split1))
        (segN (refineStep ctx level split1 st).lab a len) := by
  intro a len hcell halen
  have hps : st.ptn.size = ctx.n := hok.ptnSize
  have hls : st.lab.size = ctx.n := hok.labSize
  have hend : st.ptn[st.ptn.size - 1]! ≤ level := hok.ptnEnd
  rw [refineStep] at hcell ⊢
  dsimp only at hcell ⊢
  rcases hb : (split1 == cellEnd st.ptn level split1) with _ | _
  · -- nontrivial splitter
    rw [ite_eq_right (by simp [hb])] at hcell ⊢
    have hconst := refineNontrivial_cell_const
      (ctx := ctx) (level := level) (split1 := split1)
      (split2 := cellEnd st.ptn level split1)
      (st := { st with
        active := erase st.active split1,
        longcode := mash st.longcode
          (split1 + cellEnd st.ptn level split1) })
      (by dsimp only; omega)
      (by dsimp only; omega)
      (by dsimp only; exact hend)
      a len hcell halen
    exact hconst
  · -- trivial splitter
    rw [ite_eq_left hb] at hcell
    rw [ite_eq_left (rfl : true = true)]
    have hsp : cellEnd st.ptn level split1 = split1 :=
      (beq_iff_eq.mp hb).symm
    rw [hsp] at hcell ⊢
    obtain ⟨bval, hbval⟩ := refineTrivial_cell_adj
      (ctx := ctx) (level := level) (split1 := split1)
      (st := { st with
        active := erase st.active split1,
        longcode := mash st.longcode (split1 + split1) })
      (by dsimp only; omega)
      (by dsimp only; omega)
      (by dsimp only; exact hend)
      a len hcell halen
    have hok' : StOk ctx.n level { st with
        active := erase st.active split1,
        longcode := mash st.longcode (split1 + split1) } :=
      ⟨hok.labSize, hok.labOk, hok.ptnSize,
        erase_lt hok.activeLt, hok.ptnEnd⟩
    have hendn : st.ptn[ctx.n - 1]! ≤ level := by
      have h := hend
      rw [hps] at h
      exact h
    have hcs : ∀ p ∈ cells st.ptn level ctx.n,
        p.1 < ctx.n ∧ p.2 < ctx.n := by
      intro p hp
      have h2 := cells_end_lt_of_end (Nat.le_of_eq hps.symm) hend hendn
        p hp
      have h1 := cells_le p hp
      exact ⟨by omega, h2⟩
    have hokR := refineTrivial_go_stOk (n := ctx.n)
      (level := level)
      (gRow := ctx.g[st.lab[split1]!]!)
      (cells st.ptn level ctx.n)
      { st with
        active := erase st.active split1,
        longcode := mash st.longcode (split1 + split1) }
      hok' hcs
    have hokR' : StOk ctx.n level (refineTrivial ctx level split1
        { st with
          active := erase st.active split1,
          longcode := mash st.longcode (split1 + split1) }) := hokR
    rw [worksetOf_singleton]
    refine constOn_single_of_adj (b := bval) hsymm
      (hok.labOk split1 (by omega)) ?_ ?_
    · intro x hx
      obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hx
      exact hokR'.labOk (a + o) (by rw [hokR'.labSize]; omega)
    · intro x hx
      obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hx
      exact hbval (a + o) (by omega) (by omega)

/-! # The certificate invariant and its collapse at exit

The loop invariant carries, for every inactive cell `D` and every
cell `C`, a certificate set `V`: a union of active cells' splitter
sets such that `C` has constant counts into `W_D ||| V`. The
certificate is semantic (a bitset constrained to lie under the active
union, saturated cell by cell) rather than a list of cells, which
frees the preservation argument from fragment bookkeeping. When
`pickSplit` finds nothing the active set is empty, `V` collapses to
zero, and the invariant is exactly equitability. -/

/-- The union of the active cells' splitter sets. -/
def activeUnion (ctx : Ctx) (level : Nat) (st : RefineSt) : Nat :=
  (cells st.ptn level ctx.n).foldl
    (fun A p =>
      if elem st.active p.1 then A ||| worksetOf st.lab p.1 p.2 else A) 0

/-- Every cell's splitter set lies inside `V` or misses it. -/
def Saturated (ctx : Ctx) (level : Nat) (st : RefineSt) (V : Nat) : Prop :=
  ∀ p ∈ cells st.ptn level ctx.n,
    worksetOf st.lab p.1 p.2 &&& V = 0 ∨
    worksetOf st.lab p.1 p.2 &&& V = worksetOf st.lab p.1 p.2

/-- The refinement loop's certificate invariant. -/
def CertInv (ctx : Ctx) (level : Nat) (st : RefineSt) : Prop :=
  ∀ p ∈ cells st.ptn level ctx.n, elem st.active p.1 = false →
  ∀ c ∈ cells st.ptn level ctx.n,
  ∃ V : Nat, V &&& activeUnion ctx level st = V ∧
    Saturated ctx level st V ∧
    ConstOn ctx (worksetOf st.lab p.1 p.2 ||| V)
      (segN st.lab c.1 (c.2 + 1 - c.1))

/-- An exhausted `pickSplit` means an empty active set. -/
theorem active_eq_zero_of_pickSplit_none {active hint : Nat}
    (h : pickSplit active hint = none) : active = 0 := by
  rw [pickSplit] at h
  rcases hmem : elem active hint with _ | _
  · rw [ite_eq_right (by simp [hmem])] at h
    rcases hn : nextElem active (some hint) with _ | v
    · rw [hn] at h
      dsimp only at h
      rw [nextElem] at h
      rcases Decidable.em (active = 0) with hz | hz
      · exact hz
      · rw [ite_eq_right hz] at h
        cases h
    · rw [hn] at h
      dsimp only at h
      cases h
  · rw [ite_eq_left hmem] at h
    cases h

/-- With no active cells the active union vanishes. -/
theorem activeUnion_eq_zero {ctx : Ctx} {level : Nat} {st : RefineSt}
    (h : st.active = 0) : activeUnion ctx level st = 0 := by
  rw [activeUnion]
  have hgen : ∀ (l : List (Nat × Nat)),
      l.foldl (fun A p =>
        if elem st.active p.1 then A ||| worksetOf st.lab p.1 p.2
        else A) 0 = 0 := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      rw [List.foldl_cons, ite_eq_right (by
        rw [h, elem, Nat.zero_testBit]
        simp)]
      exact ih
  exact hgen _

/-- At exit the certificate collapses and the invariant is
equitability. -/
theorem equitable_of_certInv_exit {ctx : Ctx} {level : Nat}
    {st : RefineSt} (hinv : CertInv ctx level st)
    (hact : st.active = 0) :
    Equitable ctx level st.lab st.ptn := by
  intro cd hcd de hde
  have hde0 : elem st.active de.1 = false := by
    rw [hact, elem, Nat.zero_testBit]
  obtain ⟨V, hVau, _, hconst⟩ := hinv de hde hde0 cd hcd
  rw [activeUnion_eq_zero hact, Nat.and_zero] at hVau
  rw [← hVau, Nat.or_zero] at hconst
  rw [splitDone_iff_constOn]
  exact hconst

/-! # Active-set bookkeeping

The preservation proof tracks the active bitset through a splitting
pass: membership under `insert`/`erase`, the splitter's membership
from `pickSplit`, and the bit-count bookkeeping the fuel potential
consumes. -/

theorem elem_insert (w v u : Nat) :
    elem (insert w v) u = (elem w u || v == u) := by
  rw [elem, elem, testBit_insert]

theorem elem_erase (w v u : Nat) :
    elem (erase w v) u = (elem w u && !(v == u)) := by
  rw [elem, elem, testBit_erase]

theorem insert_of_elem {w v : Nat} (h : elem w v = true) :
    insert w v = w := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [testBit_insert]
  rcases Decidable.em (v = i) with rfl | hne
  · rw [elem] at h
    simp [h]
  · simp [show (v == i) = false from by simp [hne]]

private theorem bitCount_succ (n s : Nat) :
    bitCount (n + 1) s = bitCount n s + (if s.testBit n then 1 else 0) := by
  rw [bitCount, bitCount, List.range_succ, List.countP_append,
    List.countP_cons, List.countP_nil]
  rcases h : s.testBit n with _ | _ <;> simp

private theorem bitCount_congr {n a b : Nat}
    (h : ∀ i, i < n → a.testBit i = b.testBit i) :
    bitCount n a = bitCount n b := by
  induction n with
  | zero => rfl
  | succ m ih =>
    rw [bitCount_succ, bitCount_succ, ih fun i hi => h i (by omega),
      h m (by omega)]

theorem bitCount_insert_le (n w v : Nat) :
    bitCount n (insert w v) ≤ bitCount n w + 1 := by
  induction n with
  | zero => rw [bitCount, bitCount]; simp
  | succ m ih =>
    rw [bitCount_succ, bitCount_succ, testBit_insert]
    rcases hv : (v == m) with _ | _
    · rcases h : w.testBit m with _ | _ <;>
        simp only [Bool.or_false, Bool.false_eq_true, ite_true,
          ite_false] <;>
        omega
    · have hvm : v = m := by simpa using hv
      rw [bitCount_congr (n := m) (b := w) fun i hi => by
        rw [testBit_insert,
          show (v == i) = false from by simp [show v ≠ i from by omega],
          Bool.or_false]]
      rcases h : w.testBit m with _ | _ <;>
        simp only [Bool.or_true, Bool.false_eq_true, ite_true,
          ite_false] <;>
        omega

theorem bitCount_erase_of_elem {n w v : Nat} (hv : v < n)
    (h : elem w v = true) :
    bitCount n (erase w v) + 1 = bitCount n w := by
  rw [elem] at h
  induction n with
  | zero => omega
  | succ m ih =>
    rcases Decidable.em (v = m) with heq | hne
    · rw [bitCount_succ, bitCount_succ, testBit_erase,
        show (v == m) = true from by simp [heq], Bool.not_true,
        Bool.and_false,
        bitCount_congr (n := m) (b := w) fun i hi => by
          rw [testBit_erase,
            show (v == i) = false from by simp [show v ≠ i from by omega],
            Bool.not_false, Bool.and_true],
        show w.testBit m = true from heq ▸ h]
      simp
    · rw [bitCount_succ, bitCount_succ, testBit_erase,
        show (v == m) = false from by simp [hne], Bool.not_false,
        Bool.and_true]
      have := ih (by omega)
      omega

theorem bitCount_erase_le (n w v : Nat) :
    bitCount n (erase w v) ≤ bitCount n w := by
  rcases hb : elem w v with _ | _
  · rw [erase, show w.testBit v = false from hb]
    simp
  · rcases Nat.lt_or_ge v n with hv | hv
    · have := bitCount_erase_of_elem hv hb
      omega
    · rw [bitCount_congr (b := w) fun i hi => by
        rw [testBit_erase,
          show (v == i) = false from by simp [show v ≠ i from by omega],
          Bool.not_false, Bool.and_true]]
      exact Nat.le_refl _

/-! # Splitter-set stability across a pass

The pass permutes members within each processed cell, so every cell's
splitter set survives as a bitset. -/

theorem worksetOf_congr_perm {lab lab' : Array Nat} {lo hi : Nat}
    (hp : (segN lab lo (hi + 1 - lo)).Perm (segN lab' lo (hi + 1 - lo))) :
    worksetOf lab lo hi = worksetOf lab' lo hi := by
  refine Nat.eq_of_testBit_eq fun v => ?_
  show elem (worksetOf lab lo hi) v = elem (worksetOf lab' lo hi) v
  rcases hm : elem (worksetOf lab' lo hi) v with _ | _
  · rcases hm2 : elem (worksetOf lab lo hi) v with _ | _
    · rfl
    · exact absurd (elem_worksetOf.mpr (hp.mem_iff.mp
        (elem_worksetOf.mp hm2))) (by simp [hm])
  · exact elem_worksetOf.mpr (hp.mem_iff.mpr (elem_worksetOf.mp hm))

/-- Pointwise-permuted images have permuted concatenations. -/
private theorem flatMap_perm {α : Type} {f g : α → List Nat} :
    ∀ l : List α, (∀ x ∈ l, (f x).Perm (g x)) →
      (l.flatMap f).Perm (l.flatMap g)
  | [], _ => List.Perm.refl _
  | x :: l, h => by
    rw [List.flatMap_cons, List.flatMap_cons]
    exact List.Perm.append (h x (List.mem_cons_self ..))
      (flatMap_perm l fun y hy => h y (List.mem_cons_of_mem _ hy))

/-- The whole labelling segment is the concatenation of the cell
segments. -/
private theorem segN_flatMap_cells_go {lab ptn : Array Nat}
    {level nn : Nat} (hnn : nn ≤ ptn.size)
    (hendn : ptn[nn - 1]! ≤ level) :
    ∀ fuel c1, nn ≤ c1 + fuel →
      (cells.go ptn level nn fuel c1).flatMap
          (fun p => segN lab p.1 (p.2 + 1 - p.1)) =
        segN lab c1 (nn - c1)
  | 0, c1, hf => by
    rw [cells.go, show nn - c1 = 0 from by omega, segN_zero,
      List.flatMap_nil]
  | fuel + 1, c1, hf => by
    rw [cells.go]
    rcases Decidable.em (c1 < nn) with hc | hc
    · rw [ite_eq_left hc, List.flatMap_cons]
      have hge : c1 ≤ cellEnd ptn level c1 := cellEnd_ge
      have hle : cellEnd ptn level c1 ≤ nn - 1 :=
        cellEnd_le (by omega) hendn (by omega)
      rw [segN_flatMap_cells_go hnn hendn fuel (cellEnd ptn level c1 + 1)
        (by omega),
        show nn - c1 = (cellEnd ptn level c1 + 1 - c1) +
          (nn - (cellEnd ptn level c1 + 1)) from by omega, segN_append,
        show c1 + (cellEnd ptn level c1 + 1 - c1) =
          cellEnd ptn level c1 + 1 from by omega]
    · rw [ite_eq_right hc, show nn - c1 = 0 from by omega, segN_zero,
        List.flatMap_nil]

/-- Cell-contents equivalence permutes the whole labelling segment. -/
theorem cellsPerm_segN_perm {lab lab' ptn : Array Nat} {level nn : Nat}
    (h : cellsPerm ptn level lab lab') (hnn : nn ≤ ptn.size)
    (hend : ptn[ptn.size - 1]! ≤ level) (hendn : ptn[nn - 1]! ≤ level) :
    (segN lab 0 nn).Perm (segN lab' 0 nn) := by
  have h1 := segN_flatMap_cells_go (lab := lab) hnn hendn nn 0 (by omega)
  have h2 := segN_flatMap_cells_go (lab := lab') hnn hendn nn 0 (by omega)
  rw [Nat.sub_zero] at h1 h2
  rw [← h1, ← h2]
  refine flatMap_perm _ fun p hp => ?_
  exact h p.1 (p.2 + 1 - p.1)
    (cells_isCell hnn hend p (by rw [cells]; exact hp))

/-! # Injective labellings and disjoint cell members

The certificate algebra rests on distinct cells having disjoint
splitter sets, which needs the labelling injective on the vertex
range; injectivity survives a pass because the pass permutes the
whole segment. -/

/-- The labelling is injective on the vertex range. -/
def LabInj (lab : Array Nat) (nn : Nat) : Prop :=
  ∀ i j, i < nn → j < nn → lab[i]! = lab[j]! → i = j

private theorem countP_range_le_one {p : Nat → Bool} {n : Nat}
    (h : ∀ i j, i < n → j < n → p i = true → p j = true → i = j) :
    (List.range n).countP p ≤ 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons,
      List.countP_nil]
    rcases hp : p m with _ | _
    · simp only [Bool.false_eq_true, ite_false]
      have := ih fun i j hi hj hpi hpj =>
        h i j (by omega) (by omega) hpi hpj
      omega
    · have hz : (List.range m).countP p = 0 := by
        rw [List.countP_eq_zero]
        intro a ha hpa
        have ham := List.mem_range.mp ha
        exact absurd (h a m (by omega) (by omega) hpa hp) (by omega)
      simp [hz]

private theorem two_le_countP_range {p : Nat → Bool} {n i j : Nat}
    (hij : i < j) (hj : j < n) (hpi : p i = true) (hpj : p j = true) :
    2 ≤ (List.range n).countP p := by
  induction n with
  | zero => omega
  | succ m ih =>
    rw [List.range_succ, List.countP_append, List.countP_cons,
      List.countP_nil]
    rcases Decidable.em (j = m) with heq | hne
    · have h1 : 0 < (List.range m).countP p :=
        List.countP_pos_iff.mpr ⟨i, List.mem_range.mpr (by omega), hpi⟩
      rw [show p m = true from heq ▸ hpj]
      simp only [ite_true]
      omega
    · have := ih (by omega)
      omega

/-- Injectivity transports across a whole-segment permutation. -/
theorem labInj_of_perm {lab lab' : Array Nat} {nn : Nat}
    (hp : (segN lab' 0 nn).Perm (segN lab 0 nn))
    (h : LabInj lab nn) : LabInj lab' nn := by
  intro i j hi hj he
  rcases Nat.lt_or_ge i j with hlt | hge
  · exfalso
    have h2 : 2 ≤ (segN lab' 0 nn).count lab'[j]! := by
      rw [segN, List.count_eq_countP, List.countP_map]
      refine two_le_countP_range hlt hj ?_ ?_ <;>
        simp only [Function.comp_apply, Nat.zero_add] <;>
        simp [he]
    have h1 : (segN lab 0 nn).count lab'[j]! ≤ 1 := by
      rw [segN, List.count_eq_countP, List.countP_map]
      refine countP_range_le_one fun a b ha hb hpa hpb => ?_
      simp only [Function.comp_apply, Nat.zero_add, beq_iff_eq] at hpa hpb
      exact h a b ha hb (hpa.trans hpb.symm)
    rw [hp.count_eq] at h2
    omega
  · rcases Nat.lt_or_ge j i with hlt | hge2
    · exfalso
      have h2 : 2 ≤ (segN lab' 0 nn).count lab'[i]! := by
        rw [segN, List.count_eq_countP, List.countP_map]
        refine two_le_countP_range hlt hi ?_ ?_ <;>
          simp only [Function.comp_apply, Nat.zero_add] <;>
          simp [he]
      have h1 : (segN lab 0 nn).count lab'[i]! ≤ 1 := by
        rw [segN, List.count_eq_countP, List.countP_map]
        refine countP_range_le_one fun a b ha hb hpa hpb => ?_
        simp only [Function.comp_apply, Nat.zero_add, beq_iff_eq]
          at hpa hpb
        exact h a b ha hb (hpa.trans hpb.symm)
      rw [hp.count_eq] at h2
      omega
    · omega

/-- Under an injective labelling, separated windows have disjoint
members. -/
theorem segments_disjoint_of_labInj {lab : Array Nat}
    {nn a la b lb : Nat} (h : LabInj lab nn) (hab : a + la ≤ b)
    (hbn : b + lb ≤ nn) :
    ∀ v, v ∈ segN lab a la → v ∈ segN lab b lb → False := by
  intro v hva hvb
  obtain ⟨o, ho, rfl⟩ := mem_segN_iff.mp hva
  obtain ⟨o', ho', he⟩ := mem_segN_iff.mp hvb
  have := h (b + o') (a + o) (by omega) (by omega) he
  omega

/-! # The active union as a membership test -/

private theorem testBit_activeUnion_fold {level : Nat} {st : RefineSt} :
    ∀ (l : List (Nat × Nat)) (A : Nat) (v : Nat),
      (l.foldl (fun A p => if elem st.active p.1 then
          A ||| worksetOf st.lab p.1 p.2 else A) A).testBit v =
        (A.testBit v || l.any fun p =>
          elem st.active p.1 && (worksetOf st.lab p.1 p.2).testBit v)
  | [], A, v => by simp
  | x :: l, A, v => by
    rw [List.foldl_cons, List.any_cons]
    rcases hP : elem st.active x.1 with _ | _
    · rw [ite_eq_right (by simp),
        testBit_activeUnion_fold (level := level) l A v]
      simp
    · rw [ite_eq_left (by simp),
        testBit_activeUnion_fold (level := level) l _ v, Nat.testBit_or]
      simp [Bool.or_assoc]

/-- Membership in the active union: some active cell's splitter set
holds the vertex. -/
theorem elem_activeUnion {level : Nat} {st : RefineSt} {v : Nat} :
    elem (activeUnion ctx level st) v = true ↔
      ∃ p ∈ cells st.ptn level ctx.n, elem st.active p.1 = true ∧
        elem (worksetOf st.lab p.1 p.2) v = true := by
  rw [activeUnion, elem,
    testBit_activeUnion_fold (level := level) (cells st.ptn level ctx.n)
      0 v,
    Nat.zero_testBit, Bool.false_or, List.any_eq_true]
  constructor
  · rintro ⟨p, hp, hpp⟩
    rw [Bool.and_eq_true] at hpp
    exact ⟨p, hp, hpp.1, hpp.2⟩
  · rintro ⟨p, hp, h1, h2⟩
    exact ⟨p, hp, by rw [h1, Bool.true_and]; exact h2⟩

/-- An active cell's splitter set lies inside the active union. -/
theorem workset_submask_activeUnion {level : Nat} {st : RefineSt}
    {p : Nat × Nat} (hp : p ∈ cells st.ptn level ctx.n)
    (ha : elem st.active p.1 = true) :
    worksetOf st.lab p.1 p.2 &&& activeUnion ctx level st =
      worksetOf st.lab p.1 p.2 :=
  submask_of_testBit fun _ hi =>
    elem_activeUnion.mpr ⟨p, hp, ha, hi⟩

private theorem pairwise_rel_of_mem {α : Type} {R : α → α → Prop} :
    ∀ {l : List α}, l.Pairwise R →
      ∀ a ∈ l, ∀ b ∈ l, a = b ∨ R a b ∨ R b a
  | [], _, a, ha, _, _ => absurd ha (by simp)
  | x :: l, h, a, ha, b, hb => by
    obtain ⟨hx, hl⟩ := List.pairwise_cons.mp h
    rcases List.mem_cons.mp ha with rfl | ha' <;>
      rcases List.mem_cons.mp hb with rfl | hb'
    · exact Or.inl rfl
    · exact Or.inr (Or.inl (hx b hb'))
    · exact Or.inr (Or.inr (hx a ha'))
    · exact pairwise_rel_of_mem hl a ha' b hb'

/-- Distinct cells of an injective labelling have disjoint splitter
sets. -/
theorem worksetOf_cells_disjoint {level : Nat} {st : RefineSt}
    (hinj : LabInj st.lab ctx.n) (hps : st.ptn.size = ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    {p q : Nat × Nat} (hp : p ∈ cells st.ptn level ctx.n)
    (hq : q ∈ cells st.ptn level ctx.n) (hne : p ≠ q) :
    worksetOf st.lab p.1 p.2 &&& worksetOf st.lab q.1 q.2 = 0 := by
  have hendn : st.ptn[ctx.n - 1]! ≤ level := by
    rw [← hps]
    exact hend
  have hpb := cells_end_lt_of_end (Nat.le_of_eq hps.symm) hend hendn p hp
  have hqb := cells_end_lt_of_end (Nat.le_of_eq hps.symm) hend hendn q hq
  have hple := cells_le p hp
  have hqle := cells_le q hq
  rcases pairwise_rel_of_mem cells_pairwise p hp q hq with rfl | ho | ho
  · exact absurd rfl hne
  · exact worksetOf_disjoint fun v hv hv' =>
      segments_disjoint_of_labInj hinj (by omega : p.1 + (p.2 + 1 - p.1) ≤ q.1)
        (by omega) v hv hv'
  · have h := worksetOf_disjoint (lab := st.lab) (lab' := st.lab)
      (lo := q.1) (hi := q.2) (lo' := p.1) (hi' := p.2)
      fun v hv hv' => segments_disjoint_of_labInj hinj
        (by omega : q.1 + (q.2 + 1 - q.1) ≤ p.1) (by omega) v hv hv'
    calc worksetOf st.lab p.1 p.2 &&& worksetOf st.lab q.1 q.2
        = worksetOf st.lab q.1 q.2 &&& worksetOf st.lab p.1 p.2 :=
          Nat.and_comm ..
      _ = 0 := h

/-- An inactive cell's splitter set misses the active union. -/
theorem inactive_and_activeUnion {level : Nat} {st : RefineSt}
    (hinj : LabInj st.lab ctx.n) (hps : st.ptn.size = ctx.n)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level)
    {p : Nat × Nat} (hp : p ∈ cells st.ptn level ctx.n)
    (ha : elem st.active p.1 = false) :
    worksetOf st.lab p.1 p.2 &&& activeUnion ctx level st = 0 := by
  refine Nat.eq_of_testBit_eq fun i => ?_
  rw [Nat.testBit_and, Nat.zero_testBit]
  rcases h1 : (worksetOf st.lab p.1 p.2).testBit i with _ | _
  · rfl
  · rcases h2 : (activeUnion ctx level st).testBit i with _ | _
    · rfl
    · obtain ⟨q, hq, hqa, hqi⟩ := elem_activeUnion.mp h2
      have hne : p ≠ q := fun he => by
        rw [he, hqa] at ha
        cases ha
      have := worksetOf_cells_disjoint hinj hps hend hp hq hne
      have h3 := congrArg (fun x => x.testBit i) this
      simp only [Nat.testBit_and, Nat.zero_testBit] at h3
      rw [h1, show (worksetOf st.lab q.1 q.2).testBit i = true from hqi]
        at h3
      cases h3

/-! # The trivial pass: active-set effect per processed cell -/

private theorem trivialSplit_active_eq (level cell1 cell2 : Nat)
    (c1 c2 : Int) (st : RefineSt) :
    (trivialSplit level cell1 cell2 c1 c2 st).active =
      if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
        if elem st.active cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat then
          insert st.active c1.toNat
        else
          insert st.active cell1
      else
        st.active := by
  rw [trivialSplit]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with
    hA | hA
  · rw [ite_eq_left hA, ite_eq_left hA]
    rcases Decidable.em
        (elem st.active cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hB | hB
    · rw [ite_eq_left hB, ite_eq_left hB]
      rcases (c1.toNat == cell2) with _ | _ <;> rfl
    · rw [ite_eq_right hB, ite_eq_right hB]
      rcases (c2.toNat == cell1) with _ | _ <;> rfl
  · rw [ite_eq_right hA, ite_eq_right hA]

private theorem trivialSplit_numcells_eq (level cell1 cell2 : Nat)
    (c1 c2 : Int) (st : RefineSt) :
    (trivialSplit level cell1 cell2 c1 c2 st).numcells =
      if c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2 then
        st.numcells + 1
      else
        st.numcells := by
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

private theorem trivialSplit_maxpos_eq (level cell1 cell2 : Nat)
    (c1 c2 : Int) (st : RefineSt) :
    (trivialSplit level cell1 cell2 c1 c2 st).maxpos = st.maxpos := by
  rw [trivialSplit]
  rcases Decidable.em (c2 ≥ Int.ofNat cell1 ∧ c1 ≤ Int.ofNat cell2) with
    hA | hA
  · rw [ite_eq_left hA]
    rcases Decidable.em
        (elem st.active cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hB | hB
    · rw [ite_eq_left hB]
      rcases (c1.toNat == cell2) with _ | _ <;> rfl
    · rw [ite_eq_right hB]
      rcases (c2.toNat == cell1) with _ | _ <;> rfl
  · rw [ite_eq_right hA]

/-- One processed cell of the trivial pass, the bookkeeping half:
`maxpos` untouched, and either nothing changes or exactly one junction
boundary is written together with one activation, the activated
position being the junction successor whenever the cell was active. -/
theorem trivialCell_state {level gRow cell1 cell2 : Nat} {st : RefineSt}
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size) :
    (trivialCell level gRow cell1 cell2 st).maxpos = st.maxpos ∧
    (((trivialCell level gRow cell1 cell2 st).ptn = st.ptn ∧
      (trivialCell level gRow cell1 cell2 st).active = st.active ∧
      (trivialCell level gRow cell1 cell2 st).numcells = st.numcells) ∨
     (∃ j x, cell1 ≤ j ∧ j < cell2 ∧
       (trivialCell level gRow cell1 cell2 st).ptn = st.ptn.set! j level ∧
       (trivialCell level gRow cell1 cell2 st).active =
         insert st.active x ∧
       (trivialCell level gRow cell1 cell2 st).numcells =
         st.numcells + 1 ∧
       (x = cell1 ∨ x = j + 1) ∧
       (elem st.active cell1 = true → x = j + 1))) := by
  rcases Decidable.em (cell1 = cell2) with rfl | hne
  · have heq : trivialCell level gRow cell1 cell1 st = st := by
      rw [trivialCell]
      simp
    rw [heq]
    exact ⟨rfl, Or.inl ⟨rfl, rfl, rfl⟩⟩
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
    obtain ⟨cnt, hcnt⟩ : ∃ c,
        (segN st.lab cell1 (cell2 + 1 - cell1)).countP (elem gRow ·) =
          c := ⟨_, rfl⟩
    have hcntle : cnt ≤ cell2 + 1 - cell1 := by
      have := List.countP_le_length
        (l := segN st.lab cell1 (cell2 + 1 - cell1))
        (p := (elem gRow ·))
      rw [segN_length, hcnt] at this
      exact this
    have htn : (Int.ofNat cell1).toNat = cell1 := rfl
    rw [htn] at hp1 hp2
    rw [hcnt] at hp1 hp2
    rw [heq, trivialSplit_maxpos_eq]
    refine ⟨rfl, ?_⟩
    rw [trivialSplit_active_eq, trivialSplit_numcells_eq,
      trivialSplit_ptn_eq]
    dsimp only
    rw [hp1, hp2]
    rcases Decidable.em (1 ≤ cnt ∧ cnt ≤ cell2 - cell1) with hc | hc
    · have hg : (Int.ofNat cell1 + (cnt : Int) - 1 ≥ Int.ofNat cell1 ∧
          Int.ofNat cell1 + (cnt : Int) ≤ Int.ofNat cell2) := by
        constructor
        · simp only [Int.ofNat_eq_natCast]
          omega
        · simp only [Int.ofNat_eq_natCast]
          omega
      rw [ite_eq_left hg, ite_eq_left hg, ite_eq_left hg]
      have htn2 : (Int.ofNat cell1 + (cnt : Int) - 1).toNat =
          cell1 + cnt - 1 := by
        simp only [Int.ofNat_eq_natCast]
        omega
      have htn3 : (Int.ofNat cell1 + (cnt : Int)).toNat = cell1 + cnt := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [htn2, htn3]
      refine Or.inr ?_
      rcases Decidable.em (elem st.active cell1 = true ∨
          cell1 + cnt - 1 - cell1 ≥ cell2 - (cell1 + cnt)) with hB | hB
      · exact ⟨cell1 + cnt - 1, cell1 + cnt, by omega, by omega, rfl,
          by rw [ite_eq_left hB], rfl, Or.inr (by omega),
          fun _ => by omega⟩
      · exact ⟨cell1 + cnt - 1, cell1, by omega, by omega, rfl,
          by rw [ite_eq_right hB], rfl, Or.inl rfl,
          fun hact => absurd (Or.inl hact) hB⟩
    · have hg : ¬(Int.ofNat cell1 + (cnt : Int) - 1 ≥ Int.ofNat cell1 ∧
          Int.ofNat cell1 + (cnt : Int) ≤ Int.ofNat cell2) := by
        intro ⟨hg1, hg2⟩
        simp only [Int.ofNat_eq_natCast] at hg1 hg2
        exact hc ⟨by omega, by omega⟩
      rw [ite_eq_right hg, ite_eq_right hg, ite_eq_right hg]
      exact Or.inl ⟨rfl, rfl, rfl⟩

/-- The trivial pass over a window list, the bookkeeping half:
`maxpos` kept, partition and active bits outside the windows kept,
the potential ledger balanced, and per window either nothing or one
junction with one activation. -/
theorem refineTrivial_go_state {level gRow nb : Nat} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt),
      (∀ p ∈ cs, p.1 ≤ p.2 ∧ p.2 < st.lab.size) →
      cs.Pairwise (fun p q => p.2 < q.1) →
      st.ptn.size = st.lab.size →
      (refineTrivial.go level gRow cs st).maxpos = st.maxpos ∧
      (∀ u, (∀ p ∈ cs, u < p.1 ∨ p.2 < u) →
        elem (refineTrivial.go level gRow cs st).active u =
          elem st.active u) ∧
      (∀ q, (∀ p ∈ cs, q < p.1 ∨ p.2 < q) →
        (refineTrivial.go level gRow cs st).ptn[q]! = st.ptn[q]!) ∧
      bitCount nb (refineTrivial.go level gRow cs st).active +
          2 * st.numcells ≤
        bitCount nb st.active +
          2 * (refineTrivial.go level gRow cs st).numcells ∧
      st.numcells ≤ (refineTrivial.go level gRow cs st).numcells ∧
      (∀ p ∈ cs,
        ((∀ q, p.1 ≤ q → q ≤ p.2 →
            (refineTrivial.go level gRow cs st).ptn[q]! = st.ptn[q]!) ∧
         (∀ u, p.1 ≤ u → u ≤ p.2 →
            elem (refineTrivial.go level gRow cs st).active u =
              elem st.active u)) ∨
        (∃ j x, p.1 ≤ j ∧ j < p.2 ∧
          (refineTrivial.go level gRow cs st).ptn[j]! = level ∧
          (∀ q, p.1 ≤ q → q ≤ p.2 → q ≠ j →
            (refineTrivial.go level gRow cs st).ptn[q]! = st.ptn[q]!) ∧
          (x = p.1 ∨ x = j + 1) ∧
          (elem st.active p.1 = true → x = j + 1) ∧
          elem (refineTrivial.go level gRow cs st).active x = true ∧
          (∀ u, p.1 ≤ u → u ≤ p.2 → u ≠ x →
            elem (refineTrivial.go level gRow cs st).active u =
              elem st.active u)))
  | [], st, _, _, _ => by
    rw [refineTrivial.go]
    exact ⟨rfl, fun _ _ => rfl, fun _ _ => rfl, by omega, Nat.le_refl _,
      fun p hp => absurd hp (by simp)⟩
  | (c1, c2) :: rest, st, hw, hpw, hlp => by
    rw [refineTrivial.go]
    obtain ⟨h12, hsz⟩ := hw (c1, c2) (List.mem_cons_self ..)
    dsimp only at h12 hsz
    obtain ⟨hsize, _, _⟩ :=
      trivialCell_effect (level := level) (gRow := gRow) (st := st)
        h12 hsz
    obtain ⟨hmax, hdisj⟩ :=
      trivialCell_state (level := level) (gRow := gRow) (st := st)
        h12 hsz
    have hps1 : (trivialCell level gRow c1 c2 st).ptn.size =
        st.ptn.size := by
      rcases hdisj with ⟨he, _, _⟩ | ⟨j, x, _, _, he, _⟩
      · rw [he]
      · rw [he, Array.size_set!]
    have hhead := (List.pairwise_cons.mp hpw).1
    obtain ⟨ih1, ih2, ih3, ih4, ih5, ih6⟩ :=
      refineTrivial_go_state (nb := nb) rest
        (trivialCell level gRow c1 c2 st)
        (fun p hp => by
          obtain ⟨hp1, hp2⟩ := hw p (List.mem_cons_of_mem _ hp)
          exact ⟨hp1, by rw [hsize]; exact hp2⟩)
        (List.pairwise_cons.mp hpw).2
        (by rw [hps1, hsize]; exact hlp)
    have houtA : ∀ u, u < c1 ∨ c2 < u →
        elem (trivialCell level gRow c1 c2 st).active u =
          elem st.active u := by
      intro u hu
      rcases hdisj with ⟨_, he, _⟩ | ⟨j, x, hj1, hj2, _, he, _, hx, _⟩
      · rw [he]
      · rw [he, elem_insert,
          show (x == u) = false from by
            simp only [beq_eq_false_iff_ne]
            rcases hx with rfl | rfl <;> omega,
          Bool.or_false]
    have houtP : ∀ q, q < c1 ∨ c2 < q →
        (trivialCell level gRow c1 c2 st).ptn[q]! = st.ptn[q]! := by
      intro q hq
      rcases hdisj with ⟨he, _, _⟩ | ⟨j, x, hj1, hj2, he, _⟩
      · rw [he]
      · rw [he, Array.getElem!_set!_ne _ _ _ _ (by omega)]
    have hkeepP : ∀ q, q ≤ c2 →
        (refineTrivial.go level gRow rest
          (trivialCell level gRow c1 c2 st)).ptn[q]! =
          (trivialCell level gRow c1 c2 st).ptn[q]! := by
      intro q hq
      exact ih3 q fun pr hpr => Or.inl (by
        have := hhead pr hpr
        simp only at this
        omega)
    have hkeepA : ∀ u, u ≤ c2 →
        elem (refineTrivial.go level gRow rest
          (trivialCell level gRow c1 c2 st)).active u =
          elem (trivialCell level gRow c1 c2 st).active u := by
      intro u hu
      exact ih2 u fun pr hpr => Or.inl (by
        have := hhead pr hpr
        simp only at this
        omega)
    refine ⟨ih1.trans hmax, ?_, ?_, ?_, ?_, ?_⟩
    · intro u hu
      rw [ih2 u fun p hp => hu p (List.mem_cons_of_mem _ hp),
        houtA u (by
          have := hu (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · intro q hq
      rw [ih3 q fun pr hpr => hq pr (List.mem_cons_of_mem _ hpr),
        houtP q (by
          have := hq (c1, c2) (List.mem_cons_self ..)
          simpa using this)]
    · have hcell : bitCount nb (trivialCell level gRow c1 c2 st).active +
          2 * st.numcells ≤
            bitCount nb st.active +
              2 * (trivialCell level gRow c1 c2 st).numcells := by
        rcases hdisj with ⟨_, he, hn⟩ | ⟨j, x, _, _, _, he, hn, _⟩
        · rw [he, hn]
          exact Nat.le_refl _
        · rw [he, hn]
          have := bitCount_insert_le nb st.active x
          omega
      omega
    · have : st.numcells ≤
          (trivialCell level gRow c1 c2 st).numcells := by
        rcases hdisj with ⟨_, _, hn⟩ | ⟨j, x, _, _, _, _, hn, _⟩
        · rw [hn]
          exact Nat.le_refl _
        · rw [hn]
          omega
      omega
    · intro p hp
      rcases List.mem_cons.mp hp with rfl | hmem
      · rcases hdisj with ⟨heP, heA, _⟩ |
          ⟨j, x, hj1, hj2, heP, heA, _, hx, himp⟩
        · refine Or.inl ⟨?_, ?_⟩
          · intro q hq1 hq2
            rw [hkeepP q hq2, heP]
          · intro u hu1 hu2
            rw [hkeepA u hu2, heA]
        · refine Or.inr ⟨j, x, hj1, hj2, ?_, ?_, hx, himp, ?_, ?_⟩
          · rw [hkeepP j (by omega), heP,
              Array.getElem!_set!_self _ _ _ (by
                rw [hlp]
                omega)]
          · intro q hq1 hq2 hqj
            rw [hkeepP q hq2, heP,
              Array.getElem!_set!_ne _ _ _ _ (by omega)]
          · rw [hkeepA x (by rcases hx with rfl | rfl <;> omega), heA,
              elem_insert]
            simp
          · intro u hu1 hu2 hux
            rw [hkeepA u hu2, heA, elem_insert,
              show (x == u) = false from by
                simp only [beq_eq_false_iff_ne]
                omega,
              Bool.or_false]
      · have hout1 : c2 < p.1 := by
          have := hhead p hmem
          simpa using this
        rcases ih6 p hmem with ⟨hP, hA⟩ |
          ⟨j, x, hj1, hj2, hjl, hP, hx, himp, hax, hA⟩
        · refine Or.inl ⟨?_, ?_⟩
          · intro q hq1 hq2
            rw [hP q hq1 hq2, houtP q (Or.inr (by omega))]
          · intro u hu1 hu2
            rw [hA u hu1 hu2, houtA u (Or.inr (by omega))]
        · refine Or.inr ⟨j, x, hj1, hj2, hjl, ?_, hx, ?_, hax, ?_⟩
          · intro q hq1 hq2 hqj
            rw [hP q hq1 hq2 hqj, houtP q (Or.inr (by omega))]
          · intro hact
            exact himp (by
              rw [houtA p.1 (Or.inr (by omega))]
              exact hact)
          · intro u hu1 hu2 hux
            rw [hA u hu1 hu2 hux, houtA u (Or.inr (by omega))]

/-! # The nontrivial pass: active-set effect of the window scan -/

private theorem windowStep_maxpos (level cell1 cell2 v c1 c2 : Nat)
    (maxcell : Int) (st : RefineSt) :
    (windowStep level cell1 cell2 v c1 c2 maxcell st).maxpos =
      if Int.ofNat (c2 - c1) > maxcell then c1 else st.maxpos := by
  rw [windowStep]
  dsimp only
  rcases Decidable.em (Int.ofNat (c2 - c1) > maxcell) with h1 | h1 <;>
  rcases hB : (c1 != cell1) with _ | _ <;>
  rcases hC : (c2 - c1 == 1) with _ | _ <;>
  rcases Decidable.em (c2 ≤ cell2) with h4 | h4 <;>
    simp only [h1, h4, Bool.false_eq_true, ite_false, ite_true]

/-- The window scan's active-set ledger: bits at or below the cell
start and beyond the cell end are untouched, the active set only
grows, every new bit sits just after a boundary, every boundary the
scan writes gets its successor activated (the successor of the last
write being pending exactly while mass remains), the potential ledger
balances, and the running largest-fragment position stays justified. -/
theorem windowScan_active_state {level cell1 cell2 nb : Nat}
    {counts : List Nat} :
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt),
      cell1 ≤ c1 →
      c1 + (vs.map (multOf counts)).sum = cell2 + 1 →
      (c1 = cell1 ∨ st.ptn[c1 - 1]! ≤ level ∨ c1 = cell2 + 1) →
      cell2 < st.ptn.size →
      (∀ u, u ≤ cell1 ∨ cell2 < u →
        elem (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active u = elem st.active u) ∧
      (∀ u, elem st.active u = true →
        elem (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active u = true) ∧
      (∀ q : Nat, st.ptn[q]! ≤ level →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).ptn[q]! ≤ level) ∧
      (∀ q : Nat, q < c1 →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).ptn[q]! = st.ptn[q]!) ∧
      (∀ u, elem (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active u = true → elem st.active u = true ∨
        (cell1 < u ∧ u ≤ cell2 ∧
          (windowScan level cell1 cell2 counts vs c1 maxcell
            st).ptn[u - 1]! ≤ level)) ∧
      (∀ u, c1 < u → u ≤ cell2 →
        (windowScan level cell1 cell2 counts vs c1 maxcell
          st).ptn[u - 1]! ≤ level →
        st.ptn[u - 1]! ≤ level ∨
          elem (windowScan level cell1 cell2 counts vs c1 maxcell
            st).active u = true) ∧
      (0 < (vs.map (multOf counts)).sum → c1 = cell1 ∨
        elem (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active c1 = true) ∧
      (bitCount nb (windowScan level cell1 cell2 counts vs c1 maxcell
          st).active + 2 * st.numcells ≤
        bitCount nb st.active + 2 * (windowScan level cell1 cell2
          counts vs c1 maxcell st).numcells) ∧
      st.numcells ≤ (windowScan level cell1 cell2 counts vs c1 maxcell
        st).numcells ∧
      ((maxcell < 0 ∨ (cell1 ≤ st.maxpos ∧ st.maxpos ≤ cell2 ∧
          (st.maxpos = cell1 ∨ elem st.active st.maxpos = true))) →
        (0 < (vs.map (multOf counts)).sum ∨ 0 ≤ maxcell) →
        (cell1 ≤ (windowScan level cell1 cell2 counts vs c1 maxcell
            st).maxpos ∧
         (windowScan level cell1 cell2 counts vs c1 maxcell
            st).maxpos ≤ cell2 ∧
         ((windowScan level cell1 cell2 counts vs c1 maxcell
            st).maxpos = cell1 ∨
          elem (windowScan level cell1 cell2 counts vs c1 maxcell
            st).active (windowScan level cell1 cell2 counts vs c1
              maxcell st).maxpos = true)))
  | [], c1, maxcell, st, hcw, htot, hbnd, hsz => by
    rw [windowScan]
    refine ⟨fun _ _ => rfl, fun _ h => h, fun _ h => h, fun _ _ => rfl,
      fun u h => Or.inl h, fun u hu1 hu2 h => Or.inl h,
      by simp, by omega, Nat.le_refl _, ?_⟩
    intro hmc hf
    rcases hmc with hmc | hmc
    · rcases hf with hf | hf
      · simp at hf
      · omega
    · exact hmc
  | v :: vs, c1, maxcell, st, hcw, htot, hbnd, hsz => by
    rw [windowScan]
    have hsum : (List.map (multOf counts) (v :: vs)).sum =
        multOf counts v + (List.map (multOf counts) vs).sum := by
      rw [List.map_cons, List.sum_cons]
    rcases Decidable.em (multOf counts v > 0) with hm | hm
    · rw [ite_eq_left hm]
      obtain ⟨m, hmv⟩ : ∃ m, multOf counts v = m := ⟨_, rfl⟩
      rw [hmv] at hm ⊢
      have hin : c1 + m ≤ cell2 + 1 := by
        rw [hsum, hmv] at htot
        omega
      have hpe := ptn_windowStep_eq level cell1 cell2 v c1 (c1 + m)
        maxcell st
      have hae := active_windowStep_eq level cell1 cell2 v c1 (c1 + m)
        maxcell st
      have hne := nc_windowStep_eq level cell1 cell2 v c1 (c1 + m)
        maxcell st
      have hme := windowStep_maxpos level cell1 cell2 v c1 (c1 + m)
        maxcell st
      obtain ⟨w, hw⟩ : ∃ w, windowStep level cell1 cell2 v c1 (c1 + m)
        maxcell st = w := ⟨_, rfl⟩
      rw [hw] at hpe hae hne hme
      rw [hw]
      have hwps : w.ptn.size = st.ptn.size := by
        rw [hpe]
        rcases Decidable.em (c1 + m ≤ cell2) with h | h
        · rw [ite_eq_left h, Array.size_set!]
        · rw [ite_eq_right h]
      obtain ⟨ih1, ih2, ih3, ihH, ih4, ih5, ih6, ih7, ih8, ih9⟩ :=
        windowScan_active_state (level := level) (cell1 := cell1)
          (cell2 := cell2) (nb := nb) (counts := counts) vs (c1 + m)
          (if Int.ofNat m > maxcell then Int.ofNat m else maxcell) w
          (by omega)
          (by rw [hsum, hmv] at htot; omega)
          (by
            rcases Decidable.em (c1 + m ≤ cell2) with h | h
            · refine Or.inr (Or.inl ?_)
              rw [hpe, ite_eq_left h,
                Array.getElem!_set!_self _ _ _ (by omega)]
              exact Nat.le_refl _
            · refine Or.inr (Or.inr (by omega)))
          (by rw [hwps]; exact hsz)
      have houtA : ∀ u, u ≤ cell1 ∨ cell2 < u →
          elem w.active u = elem st.active u := by
        intro u hu
        rw [hae]
        rcases Decidable.em (c1 = cell1) with h | h
        · rw [ite_eq_right (by simp [h])]
        · rw [ite_eq_left (by simp [h]), elem_insert,
            show (c1 == u) = false from by
              simp only [beq_eq_false_iff_ne]
              omega,
            Bool.or_false]
      have hmonoA : ∀ u, elem st.active u = true →
          elem w.active u = true := by
        intro u hu
        rw [hae]
        rcases Decidable.em (c1 = cell1) with h | h
        · rw [ite_eq_right (by simp [h])]
          exact hu
        · rw [ite_eq_left (by simp [h]), elem_insert, hu, Bool.true_or]
      have hpersist : ∀ q : Nat, st.ptn[q]! ≤ level →
          w.ptn[q]! ≤ level := by
        intro q hq
        rw [hpe]
        rcases Decidable.em (c1 + m ≤ cell2) with h | h
        · rw [ite_eq_left h]
          rcases getElem!_set!_cases st.ptn (c1 + m - 1) level q with
            he | he
          · rw [he]
            exact hq
          · rw [he]
            exact Nat.le_refl _
        · rw [ite_eq_right h]
          exact hq
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rw [ih1 u hu, houtA u hu]
      · intro u hu
        exact ih2 u (hmonoA u hu)
      · intro q hq
        exact ih3 q (hpersist q hq)
      · intro q hq
        rw [ihH q (by omega), hpe]
        rcases Decidable.em (c1 + m ≤ cell2) with h | h
        · rw [ite_eq_left h,
            Array.getElem!_set!_ne _ _ _ _ (by omega)]
        · rw [ite_eq_right h]
      · intro u hu
        rcases ih4 u hu with h | h
        · rw [hae] at h
          rcases Decidable.em (c1 = cell1) with hc | hc
          · rw [ite_eq_right (by simp [hc])] at h
            exact Or.inl h
          · rw [ite_eq_left (by simp [hc]), elem_insert] at h
            rcases hb2 : elem st.active u with _ | _
            · rw [hb2, Bool.false_or, beq_iff_eq] at h
              subst h
              refine Or.inr ⟨by omega, by omega, ?_⟩
              rcases hbnd with hb | hb | hb
              · exact absurd hb hc
              · exact ih3 _ (hpersist _ hb)
              · omega
            · exact Or.inl rfl
        · exact Or.inr h
      · intro u hu1 hu2 hb
        rcases Decidable.em (c1 + m < u) with hgt | hgt
        · rcases ih5 u hgt hu2 hb with h | h
          · rw [hpe] at h
            rcases Decidable.em (c1 + m ≤ cell2) with hc | hc
            · rw [ite_eq_left hc] at h
              rcases Decidable.em (u - 1 = c1 + m - 1) with he | he
              · omega
              · rw [Array.getElem!_set!_ne _ _ _ _ (by omega)] at h
                exact Or.inl h
            · rw [ite_eq_right hc] at h
              exact Or.inl h
          · exact Or.inr h
        · rcases Decidable.em (u = c1 + m) with hu' | hu'
          · subst hu'
            rcases Decidable.em (0 < (vs.map (multOf counts)).sum) with
              hf | hf
            · rcases ih6 hf with h | h
              · exact absurd h (by omega)
              · exact Or.inr h
            · rw [hsum, hmv] at htot
              omega
          · refine Or.inl ?_
            rw [ihH (u - 1) (by omega), hpe] at hb
            rcases Decidable.em (c1 + m ≤ cell2) with h | h
            · rw [ite_eq_left h,
                Array.getElem!_set!_ne _ _ _ _ (by omega)] at hb
              exact hb
            · rw [ite_eq_right h] at hb
              exact hb
      · intro _
        rcases Decidable.em (c1 = cell1) with hc | hc
        · exact Or.inl hc
        · refine Or.inr (ih2 c1 ?_)
          rw [hae, ite_eq_left (by simp [hc]), elem_insert]
          simp
      · have hstep : bitCount nb w.active + 2 * st.numcells ≤
            bitCount nb st.active + 2 * w.numcells := by
          rw [hae, hne]
          rcases Decidable.em (c1 = cell1) with hc | hc
          · rw [ite_eq_right (by simp [hc]), ite_eq_left hc]
            exact Nat.le_refl _
          · rw [ite_eq_left (by simp [hc]), ite_eq_right hc]
            have := bitCount_insert_le nb st.active c1
            omega
        omega
      · have hstep : st.numcells ≤ w.numcells := by
          rw [hne]
          rcases Decidable.em (c1 = cell1) with hc | hc
          · rw [ite_eq_left hc]
            exact Nat.le_refl _
          · rw [ite_eq_right hc]
            omega
        omega
      · intro hmc _
        refine ih9 ?_ (Or.inr (by
          rcases Decidable.em (Int.ofNat m > maxcell) with h | h
          · rw [ite_eq_left h]
            simp only [Int.ofNat_eq_natCast]
            omega
          · rw [ite_eq_right h]
            simp only [Int.ofNat_eq_natCast] at h
            omega))
        refine Or.inr ?_
        rw [hme]
        rcases Decidable.em (Int.ofNat (c1 + m - c1) > maxcell) with
          h | h
        · rw [ite_eq_left h]
          refine ⟨by omega, by omega, ?_⟩
          rcases Decidable.em (c1 = cell1) with hc | hc
          · exact Or.inl hc
          · refine Or.inr ?_
            rw [hae, ite_eq_left (by simp [hc]), elem_insert]
            simp
        · rw [ite_eq_right h]
          have hmge : ¬((m : Int) > maxcell) := by
            rw [show Int.ofNat (c1 + m - c1) = (m : Int) from by
              simp only [Int.ofNat_eq_natCast]
              omega] at h
            exact h
          have hmc0 : 0 ≤ maxcell := by
            rcases Decidable.em (0 ≤ maxcell) with h0 | h0
            · exact h0
            · exfalso
              have : (m : Int) ≥ 1 := by exact_mod_cast hm
              omega
          rcases hmc with hmc | hmc
          · omega
          · obtain ⟨hg1, hg2, hg3⟩ := hmc
            refine ⟨hg1, hg2, ?_⟩
            rcases hg3 with hg | hg
            · exact Or.inl hg
            · exact Or.inr (hmonoA _ hg)
    · rw [ite_eq_right hm]
      have hsum0 : (List.map (multOf counts) (v :: vs)).sum =
          (List.map (multOf counts) vs).sum := by
        rw [hsum]
        omega
      obtain ⟨ih1, ih2, ih3, ihH, ih4, ih5, ih6, ih7, ih8, ih9⟩ :=
        windowScan_active_state (level := level) (cell1 := cell1)
          (cell2 := cell2) (nb := nb) (counts := counts) vs c1 maxcell
          st hcw (by rw [← hsum0]; exact htot) hbnd hsz
      refine ⟨ih1, ih2, ih3, ihH, ih4, ih5, ?_, ih7, ih8, ?_⟩
      · intro hf
        rw [hsum0] at hf
        exact ih6 hf
      · intro hmc hf
        refine ih9 hmc ?_
        rcases hf with hf | hf
        · rw [hsum0] at hf
          exact Or.inl hf
        · exact Or.inr hf

private theorem nontrivialFix_active (cell1 : Nat) (st : RefineSt) :
    (nontrivialFix cell1 st).active =
      if elem st.active cell1 = true then st.active
      else erase (insert st.active cell1) st.maxpos := by
  rw [nontrivialFix]
  rcases h : elem st.active cell1 with _ | _
  · rw [ite_eq_left (by simp), ite_eq_right (by simp)]
  · rw [ite_eq_right (by simp), ite_eq_left (by simp)]

private theorem nontrivialFix_numcells (cell1 : Nat) (st : RefineSt) :
    (nontrivialFix cell1 st).numcells = st.numcells := by
  rw [nontrivialFix]
  rcases h : elem st.active cell1 with _ | _
  · rw [ite_eq_left (by simp)]
  · rw [ite_eq_right (by simp)]

/-- One processed cell of the nontrivial pass, the bookkeeping half:
active bits and boundaries outside the window untouched, the
potential ledger balanced, and the two activation clauses — an active
cell activates every fragment start, an inactive one every fragment
start but one. -/
theorem nontrivialCell_outcome {ctx : Ctx}
    {level workset cell1 cell2 nb : Nat} {st : RefineSt}
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.ptn.size) (hnb : cell2 < nb)
    (hopen : ∀ q, cell1 ≤ q → q < cell2 → st.ptn[q]! > level) :
    (∀ u, u < cell1 ∨ cell2 < u →
      elem (nontrivialCell ctx level workset cell1 cell2 st).active u =
        elem st.active u) ∧
    (∀ q : Nat, q < cell1 ∨ cell2 ≤ q →
      (nontrivialCell ctx level workset cell1 cell2 st).ptn[q]! =
        st.ptn[q]!) ∧
    (nontrivialCell ctx level workset cell1 cell2 st).ptn.size =
      st.ptn.size ∧
    (bitCount nb (nontrivialCell ctx level workset cell1 cell2
        st).active + 2 * st.numcells ≤
      bitCount nb st.active +
        2 * (nontrivialCell ctx level workset cell1 cell2 st).numcells) ∧
    st.numcells ≤
      (nontrivialCell ctx level workset cell1 cell2 st).numcells ∧
    (elem st.active cell1 = true →
      ∀ u, cell1 ≤ u → u ≤ cell2 →
        (u = cell1 ∨ (nontrivialCell ctx level workset cell1 cell2
          st).ptn[u - 1]! ≤ level) →
        elem (nontrivialCell ctx level workset cell1 cell2
          st).active u = true) ∧
    (elem st.active cell1 = false →
      ∃ w, ∀ u, cell1 ≤ u → u ≤ cell2 →
        (u = cell1 ∨ (nontrivialCell ctx level workset cell1 cell2
          st).ptn[u - 1]! ≤ level) → u ≠ w →
        elem (nontrivialCell ctx level workset cell1 cell2
          st).active u = true) := by
  rcases Decidable.em (cell1 = cell2) with heq | hne
  · have he : nontrivialCell ctx level workset cell1 cell2 st = st := by
      rw [nontrivialCell, ite_eq_left (by simp [heq])]
    rw [he]
    subst heq
    refine ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, by omega, Nat.le_refl _,
      ?_, ?_⟩
    · intro hact u hu1 hu2 _
      rw [show u = cell1 from by omega]
      exact hact
    · intro hact
      exact ⟨cell1, fun u hu1 hu2 _ hne =>
        absurd (show u = cell1 from by omega) hne⟩
  · rw [nontrivialCell, ite_eq_right (by simp [hne])]
    rcases Decidable.em
        ((countsOf ctx st.lab workset cell1 cell2).foldl Nat.min
          ((countsOf ctx st.lab workset cell1 cell2).headD 0) =
        (countsOf ctx st.lab workset cell1 cell2).foldl Nat.max
          ((countsOf ctx st.lab workset cell1 cell2).headD 0)) with
      hmm | hmm
    · rw [ite_eq_left (by simpa using hmm)]
      refine ⟨fun _ _ => rfl, fun _ _ => rfl, rfl, by dsimp only; omega,
        Nat.le_refl _, ?_, ?_⟩
      · intro hact u hu1 hu2 hu3
        rcases Decidable.em (u = cell1) with rfl | hne2
        · exact hact
        · have hb' : st.ptn[u - 1]! ≤ level := by
            rcases hu3 with rfl | hb
            · exact absurd rfl hne2
            · exact hb
          exact absurd hb' (by
            have := hopen (u - 1) (by omega) (by omega)
            omega)
      · intro hact
        refine ⟨cell1, fun u hu1 hu2 hu3 hne2 => ?_⟩
        have hb' : st.ptn[u - 1]! ≤ level := by
          rcases hu3 with rfl | hb
          · exact absurd rfl hne2
          · exact hb
        exact absurd hb' (by
          have := hopen (u - 1) (by omega) (by omega)
          omega)
    · rw [ite_eq_right (by simpa using hmm)]
      obtain ⟨S, hS⟩ : ∃ S, windowScan level cell1 cell2
          (countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st = S := ⟨_, rfl⟩
      have hlen := countsOf_length ctx st.lab workset cell1 cell2
      have htotS : cell1 + ((countValues (countsOf ctx st.lab workset
          cell1 cell2)).map (multOf (countsOf ctx st.lab workset cell1
            cell2))).sum = cell2 + 1 := by
        rw [sum_multOf_countValues, hlen]
        omega
      have hfired : 0 < ((countValues (countsOf ctx st.lab workset
          cell1 cell2)).map (multOf (countsOf ctx st.lab workset cell1
            cell2))).sum := by
        rw [sum_multOf_countValues, hlen]
        omega
      obtain ⟨sc1, sc2, sc3, scH, sc4, sc5, sc6, sc7, sc8, sc9⟩ :=
        windowScan_active_state (level := level) (cell1 := cell1)
          (cell2 := cell2) (nb := nb)
          (counts := countsOf ctx st.lab workset cell1 cell2)
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st (Nat.le_refl _) htotS (Or.inl rfl) hsz
      obtain ⟨_, _, scF, scS, _⟩ :=
        windowScan_payload (level := level) (nn := nb) hnb
          (countValues (countsOf ctx st.lab workset cell1 cell2))
          cell1 (-1) st (Nat.le_refl _) htotS hsz
          (fun p hp1 hp2 => hopen p hp1 hp2)
      rw [hS] at sc1 sc2 sc3 scH sc4 sc5 sc6 sc7 sc8 sc9 scF scS
      have hmp := sc9 (Or.inl (by omega)) (Or.inl hfired)
      have hcell1A : elem S.active cell1 = elem st.active cell1 :=
        sc1 cell1 (Or.inl (Nat.le_refl _))
      have hax : (nontrivialFix cell1 { S with
          lab := writeSegment S.lab cell1 (segmentOf S.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1
              cell2))) }).active =
          if elem S.active cell1 = true then S.active
          else erase (insert S.active cell1) S.maxpos := by
        rw [nontrivialFix_active]
      have hpx : (nontrivialFix cell1 { S with
          lab := writeSegment S.lab cell1 (segmentOf S.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1
              cell2))) }).ptn = S.ptn := by
        rw [nontrivialFix_ptn]
      have hnx : (nontrivialFix cell1 { S with
          lab := writeSegment S.lab cell1 (segmentOf S.lab cell1
            (countsOf ctx st.lab workset cell1 cell2)
            (countValues (countsOf ctx st.lab workset cell1
              cell2))) }).numcells = S.numcells := by
        rw [nontrivialFix_numcells]
      rw [hS, hax, hpx, hnx]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro u hu
        rcases hb : elem st.active cell1 with _ | _
        · rw [ite_eq_right (by simp [hcell1A, hb]), elem_erase,
            elem_insert,
            show (cell1 == u) = false from by
              simp only [beq_eq_false_iff_ne]
              omega,
            Bool.or_false,
            show (S.maxpos == u) = false from by
              simp only [beq_eq_false_iff_ne]
              omega,
            Bool.not_false, Bool.and_true]
          exact sc1 u (by omega)
        · rw [ite_eq_left (by rw [hcell1A, hb])]
          exact sc1 u (by omega)
      · intro q hq
        exact scF q (by omega)
      · exact scS
      · rcases hb : elem st.active cell1 with _ | _
        · rw [ite_eq_right (by simp [hcell1A, hb])]
          have h1 := bitCount_insert_le nb S.active cell1
          have h2 : elem (insert S.active cell1) S.maxpos = true := by
            rcases hmp.2.2 with hm | hm
            · rw [hm, elem_insert]
              simp
            · rw [elem_insert, hm, Bool.true_or]
          have h3 := bitCount_erase_of_elem
            (show S.maxpos < nb from by omega) h2
          omega
        · rw [ite_eq_left (by rw [hcell1A, hb])]
          exact sc7
      · exact sc8
      · intro hact u hu1 hu2 hu3
        rw [ite_eq_left (by rw [hcell1A, hact])]
        rcases Decidable.em (u = cell1) with rfl | hne2
        · rw [hcell1A]
          exact hact
        · have hb : S.ptn[u - 1]! ≤ level := by
            rcases hu3 with rfl | hb
            · exact absurd rfl hne2
            · exact hb
          rcases sc5 u (by omega) hu2 hb with h | h
          · exact absurd h (by
              have := hopen (u - 1) (by omega) (by omega)
              omega)
          · exact h
      · intro hact
        refine ⟨S.maxpos, fun u hu1 hu2 hu3 hne2 => ?_⟩
        rw [ite_eq_right (by simp [hcell1A, hact]), elem_erase,
          show (S.maxpos == u) = false from by
            simp only [beq_eq_false_iff_ne]
            omega,
          Bool.not_false, Bool.and_true, elem_insert]
        rcases hu3 with rfl | hb
        · simp
        · rcases Decidable.em (u = cell1) with rfl | hne3
          · simp
          · rcases sc5 u (by omega) hu2 hb with h | h
            · exact absurd h (by
                have := hopen (u - 1) (by omega) (by omega)
                omega)
            · rw [h, Bool.true_or]

end Hex.GraphIso.Nauty
