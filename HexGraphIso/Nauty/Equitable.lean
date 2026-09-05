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

Proven: the predicate layer; the member-level `ConstOn` toolkit
(disjoint-union count additivity, union and difference transport,
splitter-set disjointness and window splitting); both splitting
passes' postconditions, culminating in `refineStep_cell_const`; the
active-set bookkeeping of both passes (`refineTrivial_go_state`,
`windowScan_active_state`, `nontrivialCell_outcome`,
`refineNontrivial_go_state`) assembled into `refineStep_state` — the
strict potential drop and the per-cell activation clauses (an active
non-splitter cell activates every fragment start, any other cell
leaves at most one start inactive); the certificate interface
`CertInv`/`activeUnion`/`Saturated` with its collapse at exit; the
injectivity and splitter-set structure (`LabInj` transport across the
pass, `worksetOf_cells_disjoint`, `isCell_disj_or_eq`); the
preservation theorem `certInv_refineStep`; and the fixpoint theorem
`refine_equitable` — entering `refine` with an injective labelling,
an active set of cell starts, an accurate cell count and the
certificate invariant, the output partition is equitable. The
certificate seed is vacuous at the root (every cell active) and is
discharged at descent from the parent's equitability joined with the
individualized singleton's splitter set.

Remaining for the cheapautom arm on top of this fixpoint: the
small-cell subtree lemma and the arm-2 assembly in StoreValid.lean.
-/

namespace Hex.GraphIso.Nauty

variable {ctx : Ctx n}

/-- The window of `len` positions from `lo` has constant neighbour
counts into the vertex set `workset`. -/
@[expose] def SplitDone (ctx : Ctx n) (lab : Array Nat) (workset : VSet n) (lo len : Nat) :
    Prop :=
  ∀ o o', o < len → o' < len →
    workset.cardInter ctx.g[lab[lo + o]!]! =
      workset.cardInter ctx.g[lab[lo + o']!]!

/-- The partition at `level` is equitable: every cell has constant
neighbour counts into every cell's vertex set. -/
@[expose] def Equitable (ctx : Ctx n) (level : Nat) (lab ptn : Array Nat) : Prop :=
  ∀ cd ∈ cells ptn level n, ∀ de ∈ cells ptn level n,
    SplitDone ctx lab (worksetOf n lab de.1 de.2) cd.1 (cd.2 + 1 - cd.1)

/-- Constant counts restrict to any sub-window. -/
theorem SplitDone.sub {lab : Array Nat} {workset : VSet n} {lo len lo' len' : Nat}
    (h : SplitDone ctx lab workset lo len) (hlo : lo ≤ lo')
    (hhi : lo' + len' ≤ lo + len) : SplitDone ctx lab workset lo' len' := by
  intro o o' ho ho'
  have h1 := h (lo' - lo + o) (lo' - lo + o') (by omega) (by omega)
  have e1 : lo + (lo' - lo + o) = lo' + o := by omega
  have e2 : lo + (lo' - lo + o') = lo' + o' := by omega
  rwa [e1, e2] at h1

/-- Windows with at most one position have constant counts. -/
theorem splitDone_of_le_one {lab : Array Nat} {workset : VSet n} {lo len : Nat}
    (h : len ≤ 1) : SplitDone ctx lab workset lo len := by
  intro o o' ho ho'
  have : o = o' := by omega
  rw [this]

/-- Constant counts transfer between labellings agreeing on the
window. -/
theorem SplitDone.congr {lab lab' : Array Nat} {workset : VSet n} {lo len : Nat}
    (h : SplitDone ctx lab workset lo len)
    (hagree : ∀ o, o < len → lab'[lo + o]! = lab[lo + o]!) :
    SplitDone ctx lab' workset lo len := by
  intro o o' ho ho'
  rw [hagree o ho, hagree o' ho']
  exact h o o' ho ho'

/-- A discrete partition is equitable. -/
theorem equitable_of_singletons {level : Nat} {lab ptn : Array Nat}
    (h : ∀ cd ∈ cells ptn level n, cd.2 = cd.1) :
    Equitable ctx level lab ptn := by
  intro cd hcd de _
  exact splitDone_of_le_one (by rw [h cd hcd]; omega)

/-- Constant adjacency to a vertex on a window gives constant counts
into its singleton set. -/
theorem splitDone_single_of_const {lab : Array Nat} {u lo len : Nat}
    {b : Bool}
    (hconst : ∀ o, o < len → (ctx.g[lab[lo + o]!]!).mem u = b) :
    SplitDone ctx lab (VSet.empty.insert u) lo len := by
  intro o o' ho ho'
  rw [VSet.cardInter_singleton, VSet.cardInter_singleton, hconst o ho, hconst o' ho']

/-- The two-pointer pass separates a window: the first `cnt` positions
hold splitter-adjacent vertices and the remainder non-adjacent ones,
where `cnt` is the window's adjacency count. -/
theorem splitCellLoop_memConst {gRow : VSet n} {lab : Array Nat}
    {cell1 cell2 : Nat} (h12 : cell1 ≤ cell2) (hsz : cell2 < lab.size) :
    (∀ o, o < (segN lab cell1 (cell2 + 1 - cell1)).countP (gRow.mem ·) →
      gRow.mem (splitCellLoop gRow (cell2 - cell1 + 2) lab
        (Int.ofNat cell1) (Int.ofNat cell2)).1[cell1 + o]! = true) ∧
    (∀ o, (segN lab cell1 (cell2 + 1 - cell1)).countP (gRow.mem ·) ≤ o →
      o < cell2 + 1 - cell1 →
      gRow.mem (splitCellLoop gRow (cell2 - cell1 + 2) lab
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
          ((segN lab cell1 (cell2 + 1 - cell1)).countP (gRow.mem ·)) :=
      mem_segN_iff.mpr ⟨o, ho, rfl⟩
    have hfil := h5.mem_iff.mp hmem
    exact (List.mem_filter.mp hfil).2
  · have hmem : (splitCellLoop gRow (cell2 - cell1 + 2) lab
        (Int.ofNat cell1) (Int.ofNat cell2)).1[cell1 + o]! ∈
        segN (splitCellLoop gRow (cell2 - cell1 + 2) lab
          (Int.ofNat cell1) (Int.ofNat cell2)).1
          (cell1 + (segN lab cell1 (cell2 + 1 - cell1)).countP (gRow.mem ·))
          ((cell2 + 1 - cell1) -
            (segN lab cell1 (cell2 + 1 - cell1)).countP (gRow.mem ·)) := by
      refine mem_segN_iff.mpr
        ⟨o - (segN lab cell1 (cell2 + 1 - cell1)).countP (gRow.mem ·),
          by omega, ?_⟩
      congr 1
      omega
    have hfil := h6.mem_iff.mp hmem
    have := (List.mem_filter.mp hfil).2
    rcases hval : gRow.mem (splitCellLoop gRow (cell2 - cell1 + 2) lab
        (Int.ofNat cell1) (Int.ofNat cell2)).1[cell1 + o]! with _ | _
    · rfl
    · rw [hval] at this
      cases this

/-- A processed cell of the trivial-splitter pass: the labelling
outside the cell is untouched, the cell keeps its contents as a
multiset, and it is rearranged into the splitter-adjacent block
followed by the non-adjacent block. -/
theorem trivialCell_memConst {level cell1 cell2 : Nat} {gRow : VSet n} {st : RefineSt n}
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size) :
    (trivialCell level gRow cell1 cell2 st).lab.size = st.lab.size ∧
    (∀ j, j < cell1 ∨ cell2 < j →
      (trivialCell level gRow cell1 cell2 st).lab[j]! = st.lab[j]!) ∧
    ((segN (trivialCell level gRow cell1 cell2 st).lab cell1
      (cell2 + 1 - cell1)).Perm
      (segN st.lab cell1 (cell2 + 1 - cell1))) ∧
    (∀ o, o < (segN st.lab cell1 (cell2 + 1 - cell1)).countP
        (gRow.mem ·) →
      gRow.mem (trivialCell level gRow cell1 cell2 st).lab[cell1 + o]! =
        true) ∧
    (∀ o, (segN st.lab cell1 (cell2 + 1 - cell1)).countP
        (gRow.mem ·) ≤ o →
      o < cell2 + 1 - cell1 →
      gRow.mem (trivialCell level gRow cell1 cell2 st).lab[cell1 + o]! =
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
      rcases hval : gRow.mem st.lab[cell1]! with _ | _
      · simp [hval] at ho
      · have ho0 : o = 0 := by
          simp [hval] at ho
          omega
        rw [ho0, Nat.add_zero]
        exact hval
    · rw [hw] at ho
      have ho0 : o = 0 := by omega
      rw [hseg] at hcnt
      rcases hval : gRow.mem st.lab[cell1]! with _ | _
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
@[expose] def ConstOn (ctx : Ctx n) (W : VSet n) (ms : List Nat) : Prop :=
  ∀ x ∈ ms, ∀ y ∈ ms, W.cardInter ctx.g[x]! = W.cardInter ctx.g[y]!

theorem ConstOn.mono {W : VSet n} {ms ms' : List Nat}
    (h : ConstOn ctx W ms) (hsub : ∀ x ∈ ms', x ∈ ms) :
    ConstOn ctx W ms' :=
  fun x hx y hy => h x (hsub x hx) y (hsub y hy)

theorem ConstOn.perm {W : VSet n} {ms ms' : List Nat}
    (h : ConstOn ctx W ms) (hp : ms'.Perm ms) : ConstOn ctx W ms' :=
  h.mono fun _ hx => hp.mem_iff.mp hx

theorem splitDone_iff_constOn {lab : Array Nat} {W : VSet n} {lo len : Nat} :
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

/-- Constancy into two disjoint sets gives constancy into the union. -/
theorem ConstOn.or {a b : VSet n} {ms : List Nat} (hd : a.inter b = VSet.empty)
    (h1 : ConstOn ctx a ms) (h2 : ConstOn ctx b ms) :
    ConstOn ctx (a.union b) ms := by
  intro x hx y hy
  rw [VSet.cardInter_union_disjoint hd, VSet.cardInter_union_disjoint hd,
    h1 x hx y hy, h2 x hx y hy]

/-- Constancy into a disjoint union and into the right part gives
constancy into the left part. -/
theorem ConstOn.of_or {a b : VSet n} {ms : List Nat} (hd : a.inter b = VSet.empty)
    (h1 : ConstOn ctx (a.union b) ms) (h2 : ConstOn ctx b ms) :
    ConstOn ctx a ms := by
  intro x hx y hy
  have hx1 := h1 x hx y hy
  have hx2 := h2 x hx y hy
  rw [VSet.cardInter_union_disjoint hd, VSet.cardInter_union_disjoint hd] at hx1
  omega

/-! # Splitter sets of cells -/

/-- Splitter sets of member-disjoint segments are disjoint. -/
theorem worksetOf_disjoint {lab lab' : Array Nat} {lo hi lo' hi' : Nat}
    (h : ∀ v, v ∈ segN lab lo (hi + 1 - lo) →
      v ∈ segN lab' lo' (hi' + 1 - lo') → False) :
    (worksetOf n lab lo hi).inter (worksetOf n lab' lo' hi') = VSet.empty := by
  refine VSet.eq_empty_iff.mpr fun v => ?_
  rw [VSet.mem_inter, mem_worksetOf, mem_worksetOf]
  rcases h1 : (segN lab lo (hi + 1 - lo)).any (· == v) with _ | _
  · simp
  · rcases h2 : (segN lab' lo' (hi' + 1 - lo')).any (· == v) with _ | _
    · simp
    · obtain ⟨x, hx, hxv⟩ := List.any_eq_true.mp h1
      obtain ⟨y, hy, hyv⟩ := List.any_eq_true.mp h2
      simp only [beq_iff_eq] at hxv hyv
      subst hxv
      exact absurd (hyv ▸ hy) fun hm => h x hx hm

/-- A splitter set splits at any interior junction of its window. -/
theorem worksetOf_split {lab : Array Nat} {lo j hi : Nat}
    (hlo : lo ≤ j) (hj : j < hi) :
    worksetOf n lab lo hi =
      (worksetOf n lab lo j).union (worksetOf n lab (j + 1) hi) := by
  refine VSet.ext fun v => ?_
  rw [VSet.mem_union, mem_worksetOf, mem_worksetOf, mem_worksetOf,
    show hi + 1 - lo = (j + 1 - lo) + (hi + 1 - (j + 1)) from by omega,
    segN_append, List.any_append,
    show lo + (j + 1 - lo) = j + 1 from by omega]
  cases decide (v < n) <;> simp

/-- Membership in a splitter set is membership of the segment (of a
vertex). -/
theorem mem_worksetOf_iff {lab : Array Nat} {lo hi v : Nat} :
    (worksetOf n lab lo hi).mem v = true ↔
      v < n ∧ v ∈ segN lab lo (hi + 1 - lo) := by
  rw [mem_worksetOf, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true]
  constructor
  · rintro ⟨hv, x, hx, hxv⟩
    simp only [beq_iff_eq] at hxv
    exact ⟨hv, hxv ▸ hx⟩
  · rintro ⟨hv, hmem⟩
    exact ⟨hv, v, hmem, by simp⟩

/-- Adjacency to a vertex constant over a member list gives constant
counts into its singleton set, through row symmetry. -/
theorem constOn_single_of_adj {v : Nat} {ms : List Nat} {b : Bool}
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hv : v < n) (hms : ∀ x ∈ ms, x < n)
    (hconst : ∀ x ∈ ms, (ctx.g[v]!).mem x = b) :
    ConstOn ctx (VSet.empty.insert v) ms := by
  intro x hx y hy
  rw [VSet.cardInter_singleton, VSet.cardInter_singleton,
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
    (st : RefineSt n) :
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
        (st.active.mem cell1 ∨ c2.toNat - cell1 ≥ cell2 - c1.toNat) with
      hB | hB
    · rw [ite_eq_left hB]
      rcases (c1.toNat == cell2) with _ | _ <;> rfl
    · rw [ite_eq_right hB]
      rcases (c2.toNat == cell1) with _ | _ <;> rfl
  · rw [ite_eq_right hA, ite_eq_right hA]

/-- One processed cell of the trivial pass: sizes and the outside
kept, and the window left as constant block(s) with the junction
boundary written exactly in the two-block case. -/
theorem trivialCell_effect {level cell1 cell2 : Nat} {gRow : VSet n} {st : RefineSt n}
    (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size) :
    (trivialCell level gRow cell1 cell2 st).lab.size = st.lab.size ∧
    (∀ j, j < cell1 ∨ cell2 < j →
      (trivialCell level gRow cell1 cell2 st).lab[j]! = st.lab[j]!) ∧
    (((trivialCell level gRow cell1 cell2 st).ptn = st.ptn ∧
        ∃ b : Bool, ∀ p, cell1 ≤ p → p ≤ cell2 →
          gRow.mem (trivialCell level gRow cell1 cell2 st).lab[p]! = b) ∨
      (∃ j, cell1 ≤ j ∧ j < cell2 ∧
        (trivialCell level gRow cell1 cell2 st).ptn = st.ptn.set! j level ∧
        (∀ p, cell1 ≤ p → p ≤ j →
          gRow.mem (trivialCell level gRow cell1 cell2 st).lab[p]! =
            true) ∧
        (∀ p, j < p → p ≤ cell2 →
          gRow.mem (trivialCell level gRow cell1 cell2 st).lab[p]! =
            false))) := by
  obtain ⟨hsize, houtside, hperm, htrue, hfalse⟩ :=
    trivialCell_memConst (level := level) (gRow := gRow) (st := st)
      h12 hsz
  refine ⟨hsize, houtside, ?_⟩
  obtain ⟨cnt, hcnt⟩ : ∃ c,
      (segN st.lab cell1 (cell2 + 1 - cell1)).countP (gRow.mem ·) = c :=
    ⟨_, rfl⟩
  rw [hcnt] at htrue hfalse
  have hcntle : cnt ≤ cell2 + 1 - cell1 := by
    have := List.countP_le_length (l := segN st.lab cell1 (cell2 + 1 - cell1))
      (p := (gRow.mem ·))
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
theorem refineTrivial_go_blocks {level : Nat} {gRow : VSet n} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n),
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
          gRow.mem (refineTrivial.go level gRow cs st).lab[q]! = b) ∨
        (∃ j, p.1 ≤ j ∧ j < p.2 ∧
          (refineTrivial.go level gRow cs st).ptn[j]! = level ∧
          (∀ q, p.1 ≤ q → q ≤ j →
            gRow.mem (refineTrivial.go level gRow cs st).lab[q]! =
              true) ∧
          (∀ q, j < q → q ≤ p.2 →
            gRow.mem (refineTrivial.go level gRow cs st).lab[q]! =
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
theorem refineTrivial_cell_adj {ctx : Ctx n} {level split1 : Nat}
    {st : RefineSt n} (hpsz : st.ptn.size = n)
    (hlp : st.lab.size = st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    ∀ a len, IsCell (refineTrivial ctx level split1 st).ptn level a len →
      a + len ≤ n →
      ∃ b : Bool, ∀ q, a ≤ q → q < a + len →
        (ctx.g[st.lab[split1]!]!).mem
          (refineTrivial ctx level split1 st).lab[q]! = b := by
  intro a len hcell halen
  have hnn : n ≤ st.ptn.size := Nat.le_of_eq hpsz.symm
  have hendn : st.ptn[n - 1]! ≤ level := by
    have h := hend
    rw [hpsz] at h
    exact h
  have hwind : ∀ p ∈ cells st.ptn level n,
      p.1 ≤ p.2 ∧ p.2 < st.lab.size := fun p hp =>
    ⟨cells_le p hp, by
      have := cells_end_lt_of_end hnn hend hendn p hp
      omega⟩
  obtain ⟨g1, g2, g3, g4, g5⟩ := refineTrivial_go_blocks
    (level := level) (gRow := ctx.g[st.lab[split1]!]!)
    (cells st.ptn level n) st hwind cells_pairwise hlp.symm
  rw [refineTrivial] at hcell ⊢
  have hpres : ∀ q : Nat, st.ptn[q]! ≤ level →
      (refineTrivial.go level (ctx.g[st.lab[split1]!]!)
        (cells st.ptn level n) st).ptn[q]! = st.ptn[q]! := by
    intro q hq
    refine g3 q fun p hp => ?_
    rcases Nat.lt_or_ge q n with hqn | hqn
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
        (cells st.ptn level n) st).ptn[q]! ≤ level := by
    intro q hq
    rw [hpres q hq]
    exact hq
  have hl0 : 0 < len := hcell.1
  obtain ⟨c, lenC, hcC, hca, hcb⟩ := subcell_of_grow (ptn0 := st.ptn)
    g4.symm hcell hend hgrow (by omega) (by omega)
  have hmem : (c, c + lenC - 1) ∈ cells st.ptn level n :=
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
    ∀ (vs : List Nat) (c1 : Nat) (maxcell : Int) (st : RefineSt n),
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

theorem countsOf_getElem! {ctx : Ctx n} {lab : Array Nat}
    {workset : VSet n} {cell1 cell2 j : Nat} (hj : j < cell2 + 1 - cell1) :
    (countsOf ctx lab workset cell1 cell2)[j]! =
      workset.cardInter ctx.g[lab[cell1 + j]!]! := by
  rw [countsOf_eq_map,
    getElem!_pos _ j (by rw [List.length_map, segN_length]; exact hj),
    List.getElem_map,
    ← getElem!_pos (segN lab cell1 (cell2 + 1 - cell1)) j
      (by rw [segN_length]; exact hj),
    segN_getElem! lab cell1 (cell2 + 1 - cell1) j hj]

/-- Every element of a chunk carries the chunk's count value. -/
private theorem chunkOf_count {ctx : Ctx n} {lab : Array Nat}
    {workset : VSet n} {cell1 cell2 : Nat} {v x : Nat}
    (hx : x ∈ chunkOf lab cell1 (countsOf ctx lab workset cell1 cell2) v) :
    workset.cardInter ctx.g[x]! = v := by
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

theorem getElem!_append_left'' {β : Type} [Inhabited β]
    {as bs : List β} {i : Nat} (h : i < as.length) :
    (as ++ bs)[i]! = as[i]! := by
  rw [getElem!_pos (as ++ bs) i (by rw [List.length_append]; omega),
    getElem!_pos as i h, List.getElem_append_left h]

theorem getElem!_append_right'' {β : Type} [Inhabited β]
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
theorem nontrivialCell_effect {ctx : Ctx n} {level cell1 cell2 : Nat} {workset : VSet n}
    {st : RefineSt n} (h12 : cell1 ≤ cell2) (hsz : cell2 < st.lab.size)
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
      workset.cardInter ctx.g[(nontrivialCell ctx level workset cell1 cell2 st).lab[q]!]! =
      workset.cardInter ctx.g[(nontrivialCell ctx level workset cell1 cell2 st).lab[q']!]!) := by
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
            workset.cardInter ctx.g[((countValues (countsOf ctx st.lab workset cell1
                cell2)).flatMap
                (chunkOf st.lab cell1
                  (countsOf ctx st.lab workset cell1 cell2)))[o]!]! =
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
          workset.cardInter ctx.g[st.lab[p]!]! ∈
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
theorem refineNontrivial_go_blocks {ctx : Ctx n} {level : Nat} {workset : VSet n} :
    ∀ (cs : List (Nat × Nat)) (st : RefineSt n),
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
        workset.cardInter ctx.g[(refineNontrivial.go ctx level workset cs st).lab[q]!]! =
        workset.cardInter ctx.g[(refineNontrivial.go ctx level workset cs
            st).lab[q']!]!)
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
theorem refineNontrivial_cell_const {ctx : Ctx n}
    {level split1 split2 : Nat} {st : RefineSt n}
    (hpsz : st.ptn.size = n) (hlp : st.lab.size = st.ptn.size)
    (hend : st.ptn[st.ptn.size - 1]! ≤ level) :
    ∀ a len,
      IsCell (refineNontrivial ctx level split1 split2 st).ptn level
        a len →
      a + len ≤ n →
      ConstOn ctx (worksetOf n st.lab split1 split2)
        (segN (refineNontrivial ctx level split1 split2 st).lab a len) := by
  intro a len hcell halen
  have hnn : n ≤ st.ptn.size := Nat.le_of_eq hpsz.symm
  have hendn : st.ptn[n - 1]! ≤ level := by
    have h := hend
    rw [hpsz] at h
    exact h
  have hwind : ∀ p ∈ cells st.ptn level n,
      p.1 ≤ p.2 ∧ p.2 < st.lab.size := fun p hp =>
    ⟨cells_le p hp, by
      have := cells_end_lt_of_end hnn hend hendn p hp
      omega⟩
  have hfrw : ∀ p ∈ cells st.ptn level n, ∀ i, p.1 ≤ i → i < p.2 →
      st.ptn[i]! > level := by
    intro p hp i hi1 hi2
    have hic := cells_isCell hnn hend p hp
    have hle := cells_le p hp
    have := hic.2.2.1 i hi1 (by omega)
    exact this
  obtain ⟨g1, g2, g3, g4, g5⟩ := refineNontrivial_go_blocks
    (ctx := ctx) (level := level)
    (workset := worksetOf n st.lab split1 split2)
    (cells st.ptn level n)
    { st with
      longcode := mash st.longcode (split2 - split1 + 1) }
    hwind cells_pairwise hlp.symm hfrw
  rw [refineNontrivial] at hcell ⊢
  dsimp only at hcell g1 g2 g3 g4 g5 ⊢
  have hpres : ∀ q : Nat, st.ptn[q]! ≤ level →
      (refineNontrivial.go ctx level (worksetOf n st.lab split1 split2)
        (cells st.ptn level n)
        { st with
          longcode := mash st.longcode (split2 - split1 + 1) }).ptn[q]! =
        st.ptn[q]! := by
    intro q hq
    refine g3 q fun p hp => ?_
    rcases Nat.lt_or_ge q n with hqn | hqn
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
      (refineNontrivial.go ctx level (worksetOf n st.lab split1 split2)
        (cells st.ptn level n)
        { st with
          longcode := mash st.longcode
            (split2 - split1 + 1) }).ptn[q]! ≤ level := by
    intro q hq
    rw [hpres q hq]
    exact hq
  have hl0 : 0 < len := hcell.1
  obtain ⟨c, lenC, hcC, hca, hcb⟩ := subcell_of_grow (ptn0 := st.ptn)
    g4.symm hcell hend hgrow (by omega) (by omega)
  have hmem : (c, c + lenC - 1) ∈ cells st.ptn level n :=
    isCell_mem_cells hcC hnn hend (by omega)
  have hlen0 := hcC.1
  intro x hx y hy
  obtain ⟨ox, hox, rfl⟩ := mem_segN_iff.mp hx
  obtain ⟨oy, hoy, rfl⟩ := mem_segN_iff.mp hy
  have hrun : ∀ u u', a ≤ u → u ≤ u' → u' < a + len →
      ∀ i, u ≤ i → i < u' →
      (refineNontrivial.go ctx level (worksetOf n st.lab split1 split2)
        (cells st.ptn level n)
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
    worksetOf n lab lo lo = VSet.empty.insert lab[lo]! := by
  have h1 : lo + 1 - lo = 1 := by omega
  rw [worksetOf, h1]
  have h2 : List.range 1 = [0] := rfl
  rw [h2, List.foldl_cons, List.foldl_nil, Nat.add_zero]

/-- After one `refineStep`, every cell of the result within range has
constant counts into the retired splitter's captured vertex set. -/
theorem refineStep_cell_const {ctx : Ctx n} {level split1 : Nat}
    {st : RefineSt n} (hok : StOk n level st)
    (hsymm : ∀ u w, u < n → w < n →
      (ctx.g[u]!).mem w = (ctx.g[w]!).mem u)
    (hs1 : split1 < n) :
    ∀ a len, IsCell (refineStep ctx level split1 st).ptn level a len →
      a + len ≤ n →
      ConstOn ctx (worksetOf n st.lab split1 (cellEnd st.ptn level split1))
        (segN (refineStep ctx level split1 st).lab a len) := by
  intro a len hcell halen
  have hps : st.ptn.size = n := hok.ptnSize
  have hls : st.lab.size = n := hok.labSize
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
        active := st.active.erase split1,
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
        active := st.active.erase split1,
        longcode := mash st.longcode (split1 + split1) })
      (by dsimp only; omega)
      (by dsimp only; omega)
      (by dsimp only; exact hend)
      a len hcell halen
    have hok' : StOk n level { st with
        active := st.active.erase split1,
        longcode := mash st.longcode (split1 + split1) } :=
      ⟨hok.labSize, hok.labOk, hok.ptnSize,
        hok.ptnEnd⟩
    have hendn : st.ptn[n - 1]! ≤ level := by
      have h := hend
      rw [hps] at h
      exact h
    have hcs : ∀ p ∈ cells st.ptn level n,
        p.1 < n ∧ p.2 < n := by
      intro p hp
      have h2 := cells_end_lt_of_end (Nat.le_of_eq hps.symm) hend hendn
        p hp
      have h1 := cells_le p hp
      exact ⟨by omega, h2⟩
    have hokR := refineTrivial_go_stOk (n := n)
      (level := level)
      (gRow := ctx.g[st.lab[split1]!]!)
      (cells st.ptn level n)
      { st with
        active := st.active.erase split1,
        longcode := mash st.longcode (split1 + split1) }
      hok' hcs
    have hokR' : StOk n level (refineTrivial ctx level split1
        { st with
          active := st.active.erase split1,
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
@[expose] def activeUnion (level : Nat) (st : RefineSt n) : VSet n :=
  (cells st.ptn level n).foldl
    (fun A p =>
      if st.active.mem p.1 then A.union (worksetOf n st.lab p.1 p.2) else A) .empty

/-- Every cell's splitter set lies inside `V` or misses it. -/
@[expose] def Saturated (level : Nat) (st : RefineSt n) (V : VSet n) : Prop :=
  ∀ p ∈ cells st.ptn level n,
    (worksetOf n st.lab p.1 p.2).inter V = VSet.empty ∨
    (worksetOf n st.lab p.1 p.2).inter V = worksetOf n st.lab p.1 p.2

/-- The refinement loop's certificate invariant. -/
@[expose] def CertInv (ctx : Ctx n) (level : Nat) (st : RefineSt n) : Prop :=
  ∀ p ∈ cells st.ptn level n, st.active.mem p.1 = false →
  ∀ c ∈ cells st.ptn level n,
  ∃ V : VSet n, V.inter (activeUnion level st) = V ∧
    Saturated level st V ∧
    ConstOn ctx ((worksetOf n st.lab p.1 p.2).union V)
      (segN st.lab c.1 (c.2 + 1 - c.1))

/-- An exhausted `pickSplit` means an empty active set. -/
theorem active_eq_empty_of_pickSplit_none {active : VSet n} {hint : Nat}
    (h : pickSplit active hint = none) : active = VSet.empty := by
  rw [pickSplit] at h
  rcases hmem : active.mem hint with _ | _
  · rw [ite_eq_right (by simp [hmem])] at h
    rcases hn : active.nextElem (some hint) with _ | v
    · rw [hn] at h
      exact VSet.eq_empty_iff.mpr fun v =>
        VSet.nextElem_none h v (by rw [VSet.scanStart]; exact Nat.zero_le _)
    · rw [hn] at h
      cases h
  · rw [ite_eq_left hmem] at h
    cases h

/-- With no active cells the active union vanishes. -/
theorem activeUnion_eq_empty {level : Nat} {st : RefineSt n}
    (h : st.active = VSet.empty) : activeUnion level st = VSet.empty := by
  rw [activeUnion]
  have hgen : ∀ (l : List (Nat × Nat)),
      l.foldl (fun A p =>
        if st.active.mem p.1 then A.union (worksetOf n st.lab p.1 p.2)
        else A) VSet.empty = VSet.empty := by
    intro l
    induction l with
    | nil => rfl
    | cons x l ih =>
      rw [List.foldl_cons, ite_eq_right (by
        rw [h, VSet.mem_empty]
        simp)]
      exact ih
  exact hgen _

/-- At exit the certificate collapses and the invariant is
equitability. -/
theorem equitable_of_certInv_exit {ctx : Ctx n} {level : Nat}
    {st : RefineSt n} (hinv : CertInv ctx level st)
    (hact : st.active = VSet.empty) :
    Equitable ctx level st.lab st.ptn := by
  intro cd hcd de hde
  have hde0 : st.active.mem de.1 = false := by
    rw [hact, VSet.mem_empty]
  obtain ⟨V, hVau, _, hconst⟩ := hinv de hde hde0 cd hcd
  rw [activeUnion_eq_empty hact, VSet.inter_empty] at hVau
  rw [← hVau, VSet.union_empty] at hconst
  rw [splitDone_iff_constOn]
  exact hconst

end Hex.GraphIso.Nauty
